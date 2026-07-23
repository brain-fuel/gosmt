package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	node := gosmt.DeclareBinaryRecursiveDatatypeConstructor(1, 2, 1, context, "node", "left", "right")
	first := gosmt.DatatypeConst(1, 2, context, "first", 1)
	foreign := gosmt.DatatypeConst(2, 2, context, "foreign", 2)
	_ = gosmt.ApplyBinaryRecursiveDatatypeConstructor(node, first, foreign)
}
