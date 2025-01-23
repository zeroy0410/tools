package vtafs

import (
	"go/types"
	//"fmt"
	"golang.org/x/tools/go/ssa"
)

var IDtoTreeNode map[int]*TreeNode

type TreeNode struct {
	ID       int
	types.Type
	Children map[int]*TreeNode
}

type FieldTree struct {
	RootNodes map[ssa.Value]*TreeNode
	nextID    int
}

func NewFieldTree() *FieldTree {
	IDtoTreeNode = make(map[int]*TreeNode)
	return &FieldTree{
		RootNodes: make(map[ssa.Value]*TreeNode),
		nextID:    0,
	}
}

func (ft *FieldTree) GetNextID() int {
	id := ft.nextID
	ft.nextID++
	return id
}

func (b *builder) Insert(root ssa.Value, path []int, typ types.Type) *TreeNode {
	ft := b.fieldTree
	if _, exists := ft.RootNodes[root]; !exists {
		ft.RootNodes[root] = &TreeNode{
			ID:       ft.GetNextID(),
			Children: make(map[int]*TreeNode),
		}
		IDtoTreeNode[ft.RootNodes[root].ID] = ft.RootNodes[root]
	}
	currentNode := ft.RootNodes[root]
	for _, index := range path {
		if _, exists := currentNode.Children[index]; !exists {
			currentNode.Children[index] = &TreeNode{
				ID:       ft.GetNextID(),
				Children: make(map[int]*TreeNode),
			}
			IDtoTreeNode[currentNode.Children[index].ID] = currentNode.Children[index]
		}
		currentNode = currentNode.Children[index]
	}
	currentNode.Type = typ
	return currentNode
}



// dst = src
func (b *builder) CopySubtree(src *TreeNode, dst *TreeNode) {
	ft := b.fieldTree
	b.addInFlowEdge(field{Typ: src.Type, FieldId: src.ID}, field{Typ: dst.Type, FieldId: dst.ID})
	for index, child := range src.Children {
		if _, exists := dst.Children[index]; !exists {
			dst.Children[index] = &TreeNode{
				ID:       ft.GetNextID(),
				Children: make(map[int]*TreeNode),
			}
			IDtoTreeNode[dst.Children[index].ID] = dst.Children[index]
		}
		b.CopySubtree(child, dst.Children[index])
	}
}



//func main() {
//	// Example usage
//	fieldTree := NewFieldTree()
//
//	// Simulated ssa.Value, replace with real instances in actual use
//	var a, pb ssa.Value
//
//	// Insert field access a.0.0.0.1.0
//	fieldTree.Insert(a, []int{0, 0, 0, 1, 0})
//
//	// Simulate field assignment a.b.c = pb.c
//	fieldTree.Assign(a, []int{0, 1, 2}, pb, []int{1, 2})
//
//	// Print the tree or inspect the nodes as needed
//	fmt.Println("Field trees updated.")
//}

