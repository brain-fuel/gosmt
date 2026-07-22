package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	succ := gosmt.DeclareRecursiveDatatypeConstructor(1, 2, 1, context, "succ", "pred")
	foreign := gosmt.DatatypeConst(2, 2, context, "foreign", 1)
	_ = gosmt.ApplyRecursiveDatatypeConstructor(succ, foreign)
}
