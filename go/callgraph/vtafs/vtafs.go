// Copyright 2024 The zeroy0410. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Add field sensitive type analysis for vta.

package vtafs

import (
	"fmt"
	"go/types"
	"maps"

	"golang.org/x/tools/go/callgraph"
	"golang.org/x/tools/go/ssa"
)

// CallGraph uses the VTAFS algorithm to compute call graph for all functions
// f:true in funcs. VTAFS refines the results of initial call graph and uses it
// to establish interprocedural type flow. If initial is nil, VTAFS uses a more
// efficient approach to construct a CHA call graph.
//
// The resulting graph does not have a root node.
//
// CallGraph does not make any assumptions on initial types global variables
// and function/method inputs can have. CallGraph is then sound, modulo use of
// reflection and unsafe, if the initial call graph is sound.
var edgeCnt int = 0
func CallGraph(funcs map[*ssa.Function]bool, initial *callgraph.Graph) *callgraph.Graph {
	callees := makeCalleesFunc(funcs, initial)
	vtaG, canon := typePropGraph(funcs, callees)
	types := propagate(vtaG, canon)

	c := &constructor{types: types, callees: callees, cache: make(methodCache)}
	cg := c.construct(funcs)
	fmt.Printf("vtafs: %d edges\n", edgeCnt)
	return cg
}

// constructor type linearly traverses the input program
// and constructs a callgraph based on the results of the
// VTAFS type propagation phase.
type constructor struct {
	types   propTypeMap
	cache   methodCache
	callees calleesFunc
}

func (c *constructor) construct(funcs map[*ssa.Function]bool) *callgraph.Graph {
	cg := &callgraph.Graph{Nodes: make(map[*ssa.Function]*callgraph.Node)}
	for f, in := range funcs {
		if in {
			c.constrct(cg, f)
		}
	}
	return cg
}

func (c *constructor) constrct(g *callgraph.Graph, f *ssa.Function) {
	caller := g.CreateNode(f)
	for _, call := range calls(f) {
		for _, c := range c.resolves(call) {
			callgraph.AddEdge(caller, call, g.CreateNode(c))
			edgeCnt++
		}
	}
}

// resolves computes the set of functions to which VTAFS resolves `c`. The resolved
// functions are intersected with functions to which `c.initial` resolves `c`.
func (c *constructor) resolves(call ssa.CallInstruction) []*ssa.Function {
	cc := call.Common()
	if cc.StaticCallee() != nil {
		return []*ssa.Function{cc.StaticCallee()}
	}

	// Skip builtins as they are not *ssa.Function.
	if _, ok := cc.Value.(*ssa.Builtin); ok {
		return nil
	}

	// Cover the case of dynamic higher-order and interface calls.
	var res []*ssa.Function
	resolved := resolve(call, c.types, c.cache)
	siteCallees(call, c.callees)(func(f *ssa.Function) bool {
		if _, ok := resolved[f]; ok {
			res = append(res, f)
		}
		return true
	})
	return res
}

// resolve returns a set of functions `c` resolves to based on the
// type propagation results in `types`.
func resolve(c ssa.CallInstruction, types propTypeMap, cache methodCache) map[*ssa.Function]empty {
	fns := make(map[*ssa.Function]empty)
	n := local{val: c.Common().Value}
	types.propTypes(n)(func(p propType) bool {
		for _, f := range propFunc(p, c, cache) {
			fns[f] = empty{}
		}
		return true
	})
	return fns
}

// propFunc returns the functions modeled with the propagation type `p`
// assigned to call site `c`. If no such function exists, nil is returned.
func propFunc(p propType, c ssa.CallInstruction, cache methodCache) []*ssa.Function {
	if p.f != nil {
		return []*ssa.Function{p.f}
	}

	if c.Common().Method == nil {
		return nil
	}

	return cache.methods(p.typ, c.Common().Method.Name(), c.Parent().Prog)
}

// methodCache serves as a type -> method name -> methods
// cache when computing methods of a type using the
// ssa.Program.MethodSets and ssa.Program.MethodValue
// APIs. The cache is used to speed up querying of
// methods of a type as the mentioned APIs are expensive.
type methodCache map[types.Type]map[string][]*ssa.Function

// methods returns methods of a type `t` named `name`. First consults
// `mc` and otherwise queries `prog` for the method. If no such method
// exists, nil is returned.
func (mc methodCache) methods(t types.Type, name string, prog *ssa.Program) []*ssa.Function {
	if ms, ok := mc[t]; ok {
		return ms[name]
	}

	ms := make(map[string][]*ssa.Function)
	mset := prog.MethodSets.MethodSet(t)
	for i, n := 0, mset.Len(); i < n; i++ {
		// f can be nil when t is an interface or some
		// other type without any runtime methods.
		if f := prog.MethodValue(mset.At(i)); f != nil {
			ms[f.Name()] = append(ms[f.Name()], f)
		}
	}
	mc[t] = ms
	return ms[name]
}

// typeAssertTypes returns a mapping from each type assertion instruction in `f` to the possible types of its input variable.
func typeAssertTypes(f *ssa.Function, typesMap *propTypeMap, cache methodCache) map[*ssa.TypeAssert][]types.Type {
	asserts := typeAsserts(f)
	result := make(map[*ssa.TypeAssert][]types.Type)

	for _, ta := range asserts {
		inputVal := ta.X
		n := local{val: inputVal}

		var possTypes []types.Type
		typesMap.propTypes(n)(func(p propType) bool {
			possTypes = append(possTypes, p.typ)
			return true
		})

		result[ta] = possTypes
	}

	return result
}

func GetTypeAsserts(funcs map[*ssa.Function]bool, initial *callgraph.Graph) map[*ssa.TypeAssert][]types.Type {
	callees := makeCalleesFunc(funcs, initial)
	vtaG, canon := typePropGraph(funcs, callees)
	typesMap := propagate(vtaG, canon)
	result := make(map[*ssa.TypeAssert][]types.Type)
	for f, in := range funcs {
		if in {
			maps.Copy(result, typeAssertTypes(f, &typesMap, methodCache{}))
		}
	}
	return result
}
