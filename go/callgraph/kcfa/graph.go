// Copyright 2024 zeroy0410. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package kcfa

import (
	"fmt"
	"go/token"
	"go/types"
	"strings"

	"golang.org/x/tools/go/ssa"
	"golang.org/x/tools/go/types/typeutil"
	"golang.org/x/tools/internal/typeparams"
)

// 定义上下文类型，支持k层调用链
type context struct {
	callChain []ssa.Instruction // 调用链（最多保留k个最近的调用点）
	k         int               // CFA的k值
}

func NewContext(k int, callSite ssa.Instruction) context {
	if k <= 0 {
		return context{k: k}
	}
	return context{
		callChain: []ssa.Instruction{callSite},
		k:         k,
	}
}

// 新增全局映射，用于存储上下文键到原始上下文的映射
var ContextMap = make(map[string]context) // ctxKey -> context

func createCtxKey(ctx context) string {
	ctxKey := ctx.String()

	// 存储到全局映射
	ContextMap[ctxKey] = ctx

	return ctxKey
}

// 使用示例（在需要获取原始 context 的地方）
func getOriginalContext(ctxKey string) context {
	if ctx, exists := ContextMap[ctxKey]; exists {
		return ctx
	}
	return context{} // 或处理错误情况
}

// String方法生成唯一标识上下文的字符串，包含k值和callChain中各指令的指针地址
func (c context) String() string {
	var parts []string
	parts = append(parts, fmt.Sprintf("k=%d", c.k)) // 包含k值
	if len(c.callChain) == 0 {
		parts = append(parts, "root")
	} else {
		for _, site := range c.callChain {
			pos := site.Pos()
			parts = append(parts, fmt.Sprintf("call@%d", pos))
		}
	}
	return strings.Join(parts, "->")
}

// 创建新上下文（保留最近k个调用点）
func (c context) extend(callSite ssa.Instruction) context {
	newChain := make([]ssa.Instruction, 0, c.k)
	newChain = append(newChain, callSite)

	// 保留前k-1个调用点
	remaining := c.k - 1
	if remaining > 0 {
		start := len(c.callChain) - remaining
		if start < 0 {
			start = 0
		}
		newChain = append(newChain, c.callChain[start:]...)
	}

	return context{
		callChain: newChain[:min(len(newChain), c.k)],
		k:         c.k,
	}
}

// node 接口，表示VTA图的节点，增加了上下文信息。
type node interface {
	Type() types.Type
	Context() context       // 新增方法，获取节点的上下文
	String() string
}

// constant node for VTA.
type constant struct {
	typ types.Type
	ctxKey string
}

func (c constant) Type() types.Type {
	return c.typ
}

func (c constant) String() string {
	return fmt.Sprintf("%s: Constant(%v)", c.ctxKey, c.Type())
}

func (c constant) Context() context {return getOriginalContext(c.ctxKey)}
// pointer node for VTA.
type pointer struct {
	typ *types.Pointer
	ctxKey string
}

func (p pointer) Type() types.Type {
	return p.typ
}

func (p pointer) String() string {
	return fmt.Sprintf("%s: Pointer(%v)", p.ctxKey, p.Type())
}

func (p pointer) Context() context {return getOriginalContext(p.ctxKey)}

// mapKey node for VTA, modeling reachable map key types.
type mapKey struct {
	typ types.Type
	ctxKey string
}

func (mk mapKey) Type() types.Type {
	return mk.typ
}

func (mk mapKey) String() string {
	return fmt.Sprintf("%s: MapKey(%v)", mk.ctxKey, mk.Type())
}

func (mk mapKey) Context() context {return getOriginalContext(mk.ctxKey)}

// mapValue node for VTA, modeling reachable map value types.
type mapValue struct {
	typ types.Type
	ctxKey string
}

func (mv mapValue) Type() types.Type {
	return mv.typ
}

func (mv mapValue) String() string {
	return fmt.Sprintf("%s: MapValue(%v)", mv.ctxKey, mv.Type())
}

func (mv mapValue) Context() context {return getOriginalContext(mv.ctxKey)}

// sliceElem node for VTA, modeling reachable slice and array element types.
type sliceElem struct {
	typ types.Type
	ctxKey string
}

func (s sliceElem) Type() types.Type {
	return s.typ
}

func (s sliceElem) String() string {
	return fmt.Sprintf("%s: Slice([]%v)", s.ctxKey, s.Type())
}

func (s sliceElem) Context() context {return getOriginalContext(s.ctxKey)}

// channelElem node for VTA, modeling reachable channel element types.
type channelElem struct {
	typ types.Type
	ctxKey string
}

func (c channelElem) Type() types.Type {
	return c.typ
}

func (c channelElem) String() string {
	return fmt.Sprintf("%s: Channel(chan %v)", c.ctxKey, c.Type())
}

func (c channelElem) Context() context {return getOriginalContext(c.ctxKey)}

// field node for VTA.
type field struct {
	StructType types.Type
	index      int // index of the field in the struct
	ctxKey string
}

func (f field) Type() types.Type {
	s := typeparams.CoreType(f.StructType).(*types.Struct)
	return s.Field(f.index).Type()
}

func (f field) String() string {
	s := typeparams.CoreType(f.StructType).(*types.Struct)
	return fmt.Sprintf("%s Field(%v:%s)", f.ctxKey, f.StructType, s.Field(f.index).Name())
}

func (f field) Context() context {return getOriginalContext(f.ctxKey)}

// global node for VTA.
type global struct {
	val *ssa.Global
	ctxKey string
}

func (g global) Type() types.Type {
	return g.val.Type()
}

func (g global) String() string {
	return fmt.Sprintf("%s: Global(%s)", g.ctxKey, g.val.Name())
}

func (g global) Context() context {return getOriginalContext(g.ctxKey)}

// local node for VTA modeling local variables
// and function/method parameters.
type local struct {
	val ssa.Value
	ctxKey string
}

func (l local) Type() types.Type {
	return l.val.Type()
}

func (l local) String() string {
	return fmt.Sprintf("%s: Local(%s)", l.ctxKey, l.val.Name())
}

func (l local) Context() context {return getOriginalContext(l.ctxKey)}

// indexedLocal node for VTA node. Models indexed locals
// related to the ssa extract instructions.
type indexedLocal struct {
	val   ssa.Value
	index int
	typ   types.Type
	ctxKey string
}

func (i indexedLocal) Type() types.Type {
	return i.typ
}

func (i indexedLocal) String() string {
	return fmt.Sprintf("%s: Local(%s[%d])", i.ctxKey, i.val.Name(), i.index)
}

func (i indexedLocal) Context() context {return getOriginalContext(i.ctxKey)}
// function node for VTA.
type function struct {
	f *ssa.Function
	ctxKey string
}

func (f function) Type() types.Type {
	return f.f.Type()
}

func (f function) String() string {
	return fmt.Sprintf("%s: Function(%s)", f.ctxKey, f.f.Name())
}

func (f function) Context() context {return getOriginalContext(f.ctxKey)}
// resultVar represents the result
// variable of a function, whether
// named or not.
type resultVar struct {
	f     *ssa.Function
	index int // valid index into result var tuple
	ctxKey string
}

func (o resultVar) Type() types.Type {
	return o.f.Signature.Results().At(o.index).Type()
}

func (o resultVar) String() string {
	v := o.f.Signature.Results().At(o.index)
	if n := v.Name(); n != "" {
		return fmt.Sprintf("%s: Return(%s[%s])", o.ctxKey, o.f.Name(), n)
	}
	return fmt.Sprintf("%s: Return(%s[%d])", o.ctxKey, o.f.Name(), o.index)
}

func (o resultVar) Context() context {return getOriginalContext(o.ctxKey)}

// nestedPtrInterface node represents all references and dereferences
// of locals and globals that have a nested pointer to interface type.
// We merge such constructs into a single node for simplicity and without
// much precision sacrifice as such variables are rare in practice. Both
// a and b would be represented as the same PtrInterface(I) node in:
//
//	type I interface
//	var a ***I
//	var b **I
type nestedPtrInterface struct {
	typ types.Type
	ctxKey string
}

func (l nestedPtrInterface) Type() types.Type {
	return l.typ
}

func (l nestedPtrInterface) String() string {
	return fmt.Sprintf("%s: PtrInterface(%v)", l.ctxKey, l.typ)
}

func (l nestedPtrInterface) Context() context {return getOriginalContext(l.ctxKey)}
// nestedPtrFunction node represents all references and dereferences of locals
// and globals that have a nested pointer to function type. We merge such
// constructs into a single node for simplicity and without much precision
// sacrifice as such variables are rare in practice. Both a and b would be
// represented as the same PtrFunction(func()) node in:
//
//	var a *func()
//	var b **func()
type nestedPtrFunction struct {
	typ types.Type
	ctxKey string
}

func (p nestedPtrFunction) Type() types.Type {
	return p.typ
}

func (p nestedPtrFunction) String() string {
	return fmt.Sprintf("%s: PtrFunction(%v)", p.ctxKey, p.typ)
}

func (p nestedPtrFunction) Context() context {return getOriginalContext(p.ctxKey)}

// panicArg models types of all arguments passed to panic.
type panicArg struct{
	ctxKey string
}

func (p panicArg) Type() types.Type {
	return nil
}

func (p panicArg) String() string {
	return "Panic"
}

func (p panicArg) Context() context {return getOriginalContext(p.ctxKey)}

// recoverReturn models types of all return values of recover().
type recoverReturn struct{
	ctxKey string
}

func (r recoverReturn) Type() types.Type {
	return nil
}

func (r recoverReturn) String() string {
	return "Recover"
}

func (r recoverReturn) Context() context {return getOriginalContext(r.ctxKey)}

type empty = struct{}

// idx is an index representing a unique node in a vtaGraph.
type idx int

// vtaGraph remembers for each VTA node the set of its successors.
// Tailored for VTA, hence does not support singleton (sub)graphs.
type vtaGraph struct {
	m    []map[idx]empty // m[i] has the successors for the node with index i.
	idx  map[node]idx    // idx[n] is the index for the node n.
	node []node          // node[i] is the node with index i.
}

func (g *vtaGraph) numNodes() int {
	return len(g.idx)
}

func (g *vtaGraph) successors(x idx) func(yield func(y idx) bool) {
	return func(yield func(y idx) bool) {
		for y := range g.m[x] {
			if !yield(y) {
				return
			}
		}
	}
}

// addEdge adds an edge x->y to the graph.
func (g *vtaGraph) addEdge(x, y node) {
	fmt.Printf("Add Edge: %-60s %-60s\n", x, y)
	if g.idx == nil {
		g.idx = make(map[node]idx)
	}
	lookup := func(n node) idx {
		i, ok := g.idx[n]
		if !ok {
			i = idx(len(g.idx))
			g.m = append(g.m, nil)
			g.idx[n] = i
			g.node = append(g.node, n)
		}
		return i
	}
	a := lookup(x)
	b := lookup(y)
	succs := g.m[a]
	if succs == nil {
		succs = make(map[idx]empty)
		g.m[a] = succs
	}
	succs[b] = empty{}
}

// typePropGraph builds a VTA graph for a set of `funcs` and initial
// `callgraph` needed to establish interprocedural edges. Returns the
// graph and a map for unique type representatives.
func typePropGraph(funcs map[*ssa.Function]bool, callees calleesFunc, k int) (*vtaGraph, *typeutil.Map) {
	b := builder{callees: callees, k: k}
	b.visit(funcs)
	b.callees = nil // ensure callees is not pinned by pointers to other fields of b.
	return &b.graph, &b.canon
}

// Data structure responsible for linearly traversing the
// code and building a VTA graph.
type builder struct {
	graph   vtaGraph
	callees calleesFunc // initial call graph for creating flows at unresolved call sites.
	callSiteIDs   map[ssa.CallInstruction]int
	nextCallSiteID int
	// Specialized type map for canonicalization of types.Type.
	// Semantically equivalent types can have different implementations,
	// i.e., they are different pointer values. The map allows us to
	// have one unique representative. The keys are fixed and from the
	// client perspective they are types. The values in our case are
	// types too, in particular type representatives. Each value is a
	// pointer so this map is not expected to take much memory.
	canon typeutil.Map
	k             int // 存储k值
}

// 为每个调用点分配唯一的ID
func (b *builder) getCallSiteID(c ssa.CallInstruction) int {
	if b.callSiteIDs == nil {
		b.callSiteIDs = make(map[ssa.CallInstruction]int)
	}
	id, ok := b.callSiteIDs[c]
	if !ok {
		id = b.nextCallSiteID
		b.nextCallSiteID++
		b.callSiteIDs[c] = id
	}
	return id
}

func (b *builder) visit(funcs map[*ssa.Function]bool) {
	// Add the fixed edge Panic -> Recover
	b.graph.addEdge(panicArg{}, recoverReturn{})

	for f, in := range funcs {
		if in {
			b.fun(f, context{k: b.k})
		}
	}
}

type funcNode struct{
	f *ssa.Function
	ctxKey string // 使用context生成的字符串键替代原context结构体
}

//record all functions with context so that after type propagation, we can find the function with context.
var AllFuncs map[funcNode]struct{} = make(map[funcNode]struct{})

func (b *builder) fun(f *ssa.Function, ctx context) {
	key := funcNode{f,createCtxKey(ctx)}
	if _, exists := AllFuncs[key]; exists {
		return
	}
	AllFuncs[key] = struct{}{}

	// 处理函数体时携带当前上下文
	for _, bl := range f.Blocks {
		for _, instr := range bl.Instrs {
			b.instr(instr, ctx)
		}
	}
}

func (b *builder) instr(instr ssa.Instruction, ctx context) {
	switch i := instr.(type) {
	case *ssa.Store:
		b.addInFlowAliasEdges(b.nodeFromVal(i.Addr, ctx), b.nodeFromVal(i.Val, ctx))
	case *ssa.MakeInterface:
		b.addInFlowEdge(b.nodeFromVal(i.X, ctx), b.nodeFromVal(i, ctx))
	case *ssa.MakeClosure:
		b.closure(i, ctx)
	case *ssa.UnOp:
		b.unop(i, ctx)
	case *ssa.Phi:
		b.phi(i, ctx)
	case *ssa.ChangeInterface:
		// Although in change interface a := A(b) command a and b are
		// the same object, the only interesting flow happens when A
		// is an interface. We create flow b -> a, but omit a -> b.
		// The latter flow is not needed: if a gets assigned concrete
		// type later on, that cannot be propagated back to b as b
		// is a separate variable. The a -> b flow can happen when
		// A is a pointer to interface, but then the command is of
		// type ChangeType, handled below.
		b.addInFlowEdge(b.nodeFromVal(i.X, ctx), b.nodeFromVal(i, ctx))
	case *ssa.ChangeType:
		// change type command a := A(b) results in a and b being the
		// same value. For concrete type A, there is no interesting flow.
		//
		// When A is an interface, most interface casts are handled
		// by the ChangeInterface instruction. The relevant case here is
		// when converting a pointer to an interface type. This can happen
		// when the underlying interfaces have the same method set.
		//
		//	type I interface{ foo() }
		//	type J interface{ foo() }
		//	var b *I
		//	a := (*J)(b)
		//
		// When this happens we add flows between a <--> b.
		b.addInFlowAliasEdges(b.nodeFromVal(i, ctx), b.nodeFromVal(i.X, ctx))
	case *ssa.TypeAssert:
		b.tassert(i, ctx)
	case *ssa.Extract:
		b.extract(i, ctx)
	case *ssa.Field:
		b.field(i, ctx)
	case *ssa.FieldAddr:
		b.fieldAddr(i, ctx)
	case *ssa.Send:
		b.send(i, ctx)
	case *ssa.Select:
		b.selekt(i, ctx)
	case *ssa.Index:
		b.index(i, ctx)
	case *ssa.IndexAddr:
		b.indexAddr(i, ctx)
	case *ssa.Lookup:
		b.lookup(i, ctx)
	case *ssa.MapUpdate:
		b.mapUpdate(i, ctx)
	case *ssa.Next:
		b.next(i, ctx)
	case ssa.CallInstruction:
		b.call(i, ctx)
	case *ssa.Panic:
		b.panic(i, ctx)
	case *ssa.Return:
		b.rtrn(i, ctx)
	case *ssa.MakeChan, *ssa.MakeMap, *ssa.MakeSlice, *ssa.BinOp,
		*ssa.Alloc, *ssa.DebugRef, *ssa.Convert, *ssa.Jump, *ssa.If,
		*ssa.Slice, *ssa.SliceToArrayPointer, *ssa.Range, *ssa.RunDefers:
		// No interesting flow here.
		// Notes on individual instructions:
		// SliceToArrayPointer: t1 = slice to array pointer *[4]T <- []T (t0)
		// No interesting flow as sliceArrayElem(t1) == sliceArrayElem(t0).
		return
	case *ssa.MultiConvert:
		b.multiconvert(i, ctx)
	default:
		panic(fmt.Sprintf("unsupported instruction %v\n", instr))
	}
}

func (b *builder) unop(u *ssa.UnOp, ctx context) {
	switch u.Op {
	case token.MUL:
		// Multiplication operator * is used here as a dereference operator.
		b.addInFlowAliasEdges(b.nodeFromVal(u, ctx), b.nodeFromVal(u.X, ctx))
	case token.ARROW:
		t := typeparams.CoreType(u.X.Type()).(*types.Chan).Elem()
		b.addInFlowAliasEdges(b.nodeFromVal(u,ctx), channelElem{typ: t, ctxKey: createCtxKey(ctx)})
	default:
		// There is no interesting type flow otherwise.
	}
}

func (b *builder) phi(p *ssa.Phi, ctx context) {
	for _, edge := range p.Edges {
		b.addInFlowAliasEdges(b.nodeFromVal(p, ctx), b.nodeFromVal(edge, ctx))
	}
}

func (b *builder) tassert(a *ssa.TypeAssert, ctx context) {
	if !a.CommaOk {
		b.addInFlowEdge(b.nodeFromVal(a.X, ctx), b.nodeFromVal(a, ctx))
		return
	}
	// The case where a is <a.AssertedType, bool> register so there
	// is a flow from a.X to a[0]. Here, a[0] is represented as an
	// indexedLocal: an entry into local tuple register a at index 0.
	tup := a.Type().(*types.Tuple)
	t := tup.At(0).Type()

	local := indexedLocal{val: a, typ: t, index: 0, ctxKey: createCtxKey(ctx)}
	b.addInFlowEdge(b.nodeFromVal(a.X, ctx), local)
}

// extract instruction t1 := t2[i] generates flows between t2[i]
// and t1 where the source is indexed local representing a value
// from tuple register t2 at index i and the target is t1.
func (b *builder) extract(e *ssa.Extract, ctx context) {
	tup := e.Tuple.Type().(*types.Tuple)
	t := tup.At(e.Index).Type()

	local := indexedLocal{val: e.Tuple, typ: t, index: e.Index, ctxKey: createCtxKey(ctx)}
	b.addInFlowAliasEdges(b.nodeFromVal(e, ctx), local)
}

func (b *builder) field(f *ssa.Field, ctx context) {
	fnode := field{StructType: f.X.Type(), index: f.Field, ctxKey: createCtxKey(ctx)}
	b.addInFlowEdge(fnode, b.nodeFromVal(f, ctx))
}

func (b *builder) fieldAddr(f *ssa.FieldAddr, ctx context) {
	t := typeparams.CoreType(f.X.Type()).(*types.Pointer).Elem()

	// Since we are getting pointer to a field, make a bidirectional edge.
	fnode := field{StructType: t, index: f.Field}
	b.addInFlowEdge(fnode, b.nodeFromVal(f, ctx))
	b.addInFlowEdge(b.nodeFromVal(f, ctx), fnode)
}

func (b *builder) send(s *ssa.Send, ctx context) {
	t := typeparams.CoreType(s.Chan.Type()).(*types.Chan).Elem()
	b.addInFlowAliasEdges(channelElem{typ: t}, b.nodeFromVal(s.X, ctx))
}

// selekt generates flows for select statement
//
//	a = select blocking/nonblocking [c_1 <- t_1, c_2 <- t_2, ..., <- o_1, <- o_2, ...]
//
// between receiving channel registers c_i and corresponding input register t_i. Further,
// flows are generated between o_i and a[2 + i]. Note that a is a tuple register of type
// <int, bool, r_1, r_2, ...> where the type of r_i is the element type of channel o_i.
func (b *builder) selekt(s *ssa.Select, ctx context) {
	recvIndex := 0
	for _, state := range s.States {
		t := typeparams.CoreType(state.Chan.Type()).(*types.Chan).Elem()

		if state.Dir == types.SendOnly {
			b.addInFlowAliasEdges(channelElem{typ: t, ctxKey: createCtxKey(ctx)}, b.nodeFromVal(state.Send, ctx))
		} else {
			// state.Dir == RecvOnly by definition of select instructions.
			tupEntry := indexedLocal{val: s, typ: t, index: 2 + recvIndex, ctxKey: createCtxKey(ctx)}
			b.addInFlowAliasEdges(tupEntry, channelElem{typ: t, ctxKey: createCtxKey(ctx)})
			recvIndex++
		}
	}
}

// index instruction a := b[c] on slices creates flows between a and
// SliceElem(t) flow where t is an interface type of c. Arrays and
// slice elements are both modeled as SliceElem.
func (b *builder) index(i *ssa.Index, ctx context) {
	et := sliceArrayElem(i.X.Type())
	b.addInFlowAliasEdges(b.nodeFromVal(i, ctx), sliceElem{typ: et, ctxKey: createCtxKey(ctx)})
}

// indexAddr instruction a := &b[c] fetches address of a index
// into the field so we create bidirectional flow a <-> SliceElem(t)
// where t is an interface type of c. Arrays and slice elements are
// both modeled as SliceElem.
func (b *builder) indexAddr(i *ssa.IndexAddr, ctx context) {
	et := sliceArrayElem(i.X.Type())
	b.addInFlowEdge(sliceElem{typ: et, ctxKey: createCtxKey(ctx)}, b.nodeFromVal(i, ctx))
	b.addInFlowEdge(b.nodeFromVal(i, ctx), sliceElem{typ: et, ctxKey: createCtxKey(ctx)})
}

// lookup handles map query commands a := m[b] where m is of type
// map[...]V and V is an interface. It creates flows between `a`
// and MapValue(V).
func (b *builder) lookup(l *ssa.Lookup, ctx context) {
	t, ok := l.X.Type().Underlying().(*types.Map)
	if !ok {
		// No interesting flows for string lookups.
		return
	}

	if !l.CommaOk {
		b.addInFlowAliasEdges(b.nodeFromVal(l, ctx), mapValue{typ: t.Elem(), ctxKey: createCtxKey(ctx)})
	} else {
		i := indexedLocal{val: l, typ: t.Elem(), index: 0, ctxKey: createCtxKey(ctx)}
		b.addInFlowAliasEdges(i, mapValue{typ: t.Elem(), ctxKey: createCtxKey(ctx)})
	}
}

// mapUpdate handles map update commands m[b] = a where m is of type
// map[K]V and K and V are interfaces. It creates flows between `a`
// and MapValue(V) as well as between MapKey(K) and `b`.
func (b *builder) mapUpdate(u *ssa.MapUpdate, ctx context) {
	t, ok := u.Map.Type().Underlying().(*types.Map)
	if !ok {
		// No interesting flows for string updates.
		return
	}

	b.addInFlowAliasEdges(mapKey{typ: t.Key(), ctxKey: createCtxKey(ctx)}, b.nodeFromVal(u.Key, ctx))
	b.addInFlowAliasEdges(mapValue{typ: t.Elem(), ctxKey: createCtxKey(ctx)}, b.nodeFromVal(u.Value, ctx))
}

// next instruction <ok, key, value> := next r, where r
// is a range over map or string generates flow between
// key and MapKey as well value and MapValue nodes.
func (b *builder) next(n *ssa.Next, ctx context) {
	if n.IsString {
		return
	}
	tup := n.Type().(*types.Tuple)
	kt := tup.At(1).Type()
	vt := tup.At(2).Type()

	b.addInFlowAliasEdges(indexedLocal{val: n, typ: kt, index: 1, ctxKey: createCtxKey(ctx)}, mapKey{typ: kt, ctxKey: createCtxKey(ctx)})
	b.addInFlowAliasEdges(indexedLocal{val: n, typ: vt, index: 2, ctxKey: createCtxKey(ctx)}, mapValue{typ: vt, ctxKey: createCtxKey(ctx)})
}

// addInFlowAliasEdges adds an edge r -> l to b.graph if l is a node that can
// have an inflow, i.e., a node that represents an interface or an unresolved
// function value. Similarly for the edge l -> r with an additional condition
// of that l and r can potentially alias.
func (b *builder) addInFlowAliasEdges(l, r node) {
	b.addInFlowEdge(r, l)

	if canAlias(l, r) {
		b.addInFlowEdge(l, r)
	}
}

func (b *builder) closure(c *ssa.MakeClosure, ctx context) {
	f := c.Fn.(*ssa.Function)
	b.addInFlowEdge(function{f: f}, b.nodeFromVal(c, ctx))

	for i, fv := range f.FreeVars {
		b.addInFlowAliasEdges(b.nodeFromVal(fv, ctx), b.nodeFromVal(c.Bindings[i], ctx))
	}
}

// panic creates a flow from arguments to panic instructions to return
// registers of all recover statements in the program. Introduces a
// global panic node Panic and
//  1. for every panic statement p: add p -> Panic
//  2. for every recover statement r: add Panic -> r (handled in call)
//
// TODO(zpavlinovic): improve precision by explicitly modeling how panic
// values flow from callees to callers and into deferred recover instructions.
func (b *builder) panic(p *ssa.Panic, ctx context) {
	// Panics often have, for instance, strings as arguments which do
	// not create interesting flows.
	if !canHaveMethods(p.X.Type()) {
		return
	}

	b.addInFlowEdge(b.nodeFromVal(p.X,ctx), panicArg{})
}

// call adds flows between arguments/parameters and return values/registers
// for both static and dynamic calls, as well as go and defer calls.
func (b *builder) call(c ssa.CallInstruction, ctx context) {
	// When c is r := recover() call register instruction, we add Recover -> r.
	if bf, ok := c.Common().Value.(*ssa.Builtin); ok && bf.Name() == "recover" {
		if v, ok := c.(ssa.Value); ok {
			b.addInFlowEdge(recoverReturn{}, b.nodeFromVal(v, ctx))
		}
		return
	}

	siteCallees(c, b.callees)(func(f *ssa.Function) bool {
		newCtx := ctx.extend(c)

		addArgumentFlows(b, c, f, ctx)
		b.fun(f, newCtx)

		site, ok := c.(ssa.Value)
		if !ok {
			return true // go or defer
		}

		results := f.Signature.Results()
		if results.Len() == 1 {
			// When there is only one return value, the destination register does not
			// have a tuple type.
			b.addInFlowEdge(resultVar{f: f, index: 0, ctxKey: createCtxKey(newCtx)}, b.nodeFromVal(site, ctx))
		} else {
			tup := site.Type().(*types.Tuple)
			for i := 0; i < results.Len(); i++ {
				local := indexedLocal{val: site, typ: tup.At(i).Type(), index: i, ctxKey: createCtxKey(ctx)}
				b.addInFlowEdge(resultVar{f: f, index: i, ctxKey: createCtxKey(newCtx)}, local)
			}
		}
		return true
	})
}

func addArgumentFlows(b *builder, c ssa.CallInstruction, f *ssa.Function, ctx context) {
	// When f has no paremeters (including receiver), there is no type
	// flow here. Also, f's body and parameters might be missing, such
	// as when vta is used within the golang.org/x/tools/go/analysis
	// framework (see github.com/golang/go/issues/50670).
	if len(f.Params) == 0 {
		return
	}
	cc := c.Common()
	if cc.Method != nil {
		// In principle we don't add interprocedural flows for receiver
		// objects. At a call site, the receiver object is interface
		// while the callee object is concrete. The flow from interface
		// to concrete type in general does not make sense. The exception
		// is when the concrete type is a named function type (see #57756).
		//
		// The flow other way around would bake in information from the
		// initial call graph.
		if isFunction(f.Params[0].Type()) {
			b.addInFlowEdge(b.nodeFromVal(cc.Value, ctx.extend(c)), b.nodeFromVal(f.Params[0], ctx))
		}
	}

	offset := 0
	if cc.Method != nil {
		offset = 1
	}
	for i, v := range cc.Args {
		// Parameters of f might not be available, as in the case
		// when vta is used within the golang.org/x/tools/go/analysis
		// framework (see github.com/golang/go/issues/50670).
		//
		// TODO: investigate other cases of missing body and parameters
		if len(f.Params) <= i+offset {
			return
		}
		b.addInFlowAliasEdges(b.nodeFromVal(f.Params[i+offset], ctx.extend(c)), b.nodeFromVal(v, ctx))
	}
}

// rtrn creates flow edges from the operands of the return
// statement to the result variables of the enclosing function.
func (b *builder) rtrn(r *ssa.Return, ctx context) {
	for i, rs := range r.Results {
		b.addInFlowEdge(b.nodeFromVal(rs, ctx), resultVar{f: r.Parent(), index: i, ctxKey: createCtxKey(ctx)})
	}
}

func (b *builder) multiconvert(c *ssa.MultiConvert, ctx context) {
	// TODO(zpavlinovic): decide what to do on MultiConvert long term.
	// TODO(zpavlinovic): add unit tests.
	typeSetOf := func(typ types.Type) []*types.Term {
		// This is a adaptation of x/exp/typeparams.NormalTerms which x/tools cannot depend on.
		var terms []*types.Term
		var err error
		switch typ := types.Unalias(typ).(type) {
		case *types.TypeParam:
			terms, err = typeparams.StructuralTerms(typ)
		case *types.Union:
			terms, err = typeparams.UnionTermSet(typ)
		case *types.Interface:
			terms, err = typeparams.InterfaceTermSet(typ)
		default:
			// Common case.
			// Specializing the len=1 case to avoid a slice
			// had no measurable space/time benefit.
			terms = []*types.Term{types.NewTerm(false, typ)}
		}

		if err != nil {
			return nil
		}
		return terms
	}
	// isValuePreserving returns true if a conversion from ut_src to
	// ut_dst is value-preserving, i.e. just a change of type.
	// Precondition: neither argument is a named or alias type.
	isValuePreserving := func(ut_src, ut_dst types.Type) bool {
		// Identical underlying types?
		if types.IdenticalIgnoreTags(ut_dst, ut_src) {
			return true
		}

		switch ut_dst.(type) {
		case *types.Chan:
			// Conversion between channel types?
			_, ok := ut_src.(*types.Chan)
			return ok

		case *types.Pointer:
			// Conversion between pointers with identical base types?
			_, ok := ut_src.(*types.Pointer)
			return ok
		}
		return false
	}
	dst_terms := typeSetOf(c.Type())
	src_terms := typeSetOf(c.X.Type())
	for _, s := range src_terms {
		us := s.Type().Underlying()
		for _, d := range dst_terms {
			ud := d.Type().Underlying()
			if isValuePreserving(us, ud) {
				// This is equivalent to a ChangeType.
				b.addInFlowAliasEdges(b.nodeFromVal(c, ctx), b.nodeFromVal(c.X, ctx))
				return
			}
			// This is equivalent to either: SliceToArrayPointer,,
			// SliceToArrayPointer+Deref, Size 0 Array constant, or a Convert.
		}
	}
}

// addInFlowEdge adds s -> d to g if d is node that can have an inflow, i.e., a node
// that represents an interface or an unresolved function value. Otherwise, there
// is no interesting type flow so the edge is omitted.
func (b *builder) addInFlowEdge(s, d node) {
	if hasInFlow(d) {
		b.graph.addEdge(b.representative(s), b.representative(d))
	}
}

// Creates const, pointer, global, func, and local nodes based on register instructions.
func (b *builder) nodeFromVal(val ssa.Value, ctx context) node {
	if p, ok := types.Unalias(val.Type()).(*types.Pointer); ok && !types.IsInterface(p.Elem()) && !isFunction(p.Elem()) {
		// Nested pointer to interfaces are modeled as a special
		// nestedPtrInterface node.
		if i := interfaceUnderPtr(p.Elem()); i != nil {
			return nestedPtrInterface{typ: i, ctxKey: createCtxKey(ctx)}
		}
		// The same goes for nested function types.
		if f := functionUnderPtr(p.Elem()); f != nil {
			return nestedPtrFunction{typ: f, ctxKey: createCtxKey(ctx)}
		}
		return pointer{typ: p, ctxKey: createCtxKey(ctx)}
	}

	switch v := val.(type) {
	case *ssa.Const:
		return constant{typ: val.Type(), ctxKey: createCtxKey(ctx)}
	case *ssa.Global:
		return global{val: v, ctxKey: createCtxKey(ctx)}
	case *ssa.Function:
		return function{f: v, ctxKey: createCtxKey(ctx)}
	case *ssa.Parameter, *ssa.FreeVar, ssa.Instruction:
		// ssa.Param, ssa.FreeVar, and a specific set of "register" instructions,
		// satisifying the ssa.Value interface, can serve as local variables.
		return local{val: v, ctxKey: createCtxKey(ctx)}
	default:
		panic(fmt.Errorf("unsupported value %v in node creation", val))
	}
}

// representative returns a unique representative for node `n`. Since
// semantically equivalent types can have different implementations,
// this method guarantees the same implementation is always used.
func (b *builder) representative(n node) node {
	if n.Type() == nil {
		// panicArg and recoverReturn do not have
		// types and are unique by definition.
		return n
	}
	t := canonicalize(n.Type(), &b.canon)

	switch i := n.(type) {
	case constant:
		return constant{typ: t, ctxKey: createCtxKey(n.Context())}
	case pointer:
		return pointer{typ: t.(*types.Pointer), ctxKey: createCtxKey(n.Context())}
	case sliceElem:
		return sliceElem{typ: t, ctxKey: createCtxKey(n.Context())}
	case mapKey:
		return mapKey{typ: t, ctxKey: createCtxKey(n.Context())}
	case mapValue:
		return mapValue{typ: t, ctxKey: createCtxKey(n.Context())}
	case channelElem:
		return channelElem{typ: t, ctxKey: createCtxKey(n.Context())}
	case nestedPtrInterface:
		return nestedPtrInterface{typ: t, ctxKey: createCtxKey(n.Context())}
	case nestedPtrFunction:
		return nestedPtrFunction{typ: t, ctxKey: createCtxKey(n.Context())}
	case field:
		return field{StructType: canonicalize(i.StructType, &b.canon), index: i.index, ctxKey: createCtxKey(n.Context())}
	case indexedLocal:
		return indexedLocal{typ: t, val: i.val, index: i.index, ctxKey: createCtxKey(n.Context())}
	case local, global, panicArg, recoverReturn, function, resultVar:
		return n
	default:
		panic(fmt.Errorf("canonicalizing unrecognized node %v", n))
	}
}

// canonicalize returns a type representative of `t` unique subject
// to type map `canon`.
func canonicalize(t types.Type, canon *typeutil.Map) types.Type {
	rep := canon.At(t)
	if rep != nil {
		return rep.(types.Type)
	}
	canon.Set(t, t)
	return t
}
