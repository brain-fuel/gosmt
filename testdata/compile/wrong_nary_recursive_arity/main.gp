package compilefixture

import (
	"goforge.dev/gosmt"
	"goforge.dev/goplus/std/vec"
)

func Rejected() {
	context := gosmt.NewContext(7)
	leaf := gosmt.DatatypeConstructor(3, 2, 0, context, "leaf")
	names := vec.Cons("first", vec.Cons("second", vec.Cons("third", vec.Nil[string]())))
	branch := gosmt.DeclareNaryRecursiveDatatypeConstructor(3, 2, 1, 3, context, "branch", names)
	wrong := vec.Cons(leaf, vec.Cons(leaf, vec.Nil[gosmt.DatatypeExpr[7, 3, 2]]()))
	_ = gosmt.ApplyNaryRecursiveDatatypeConstructor(branch, wrong)
}
