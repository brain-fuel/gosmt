package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	left := gosmt.UninterpretedConst(1, context, "left", 1)
	wrongRight := gosmt.UninterpretedConst(1, context, "wrong-right", 2)
	function := gosmt.DeclareBinary(1, 2, 3, context, "f", 3)
	_ = gosmt.ApplyBinaryUninterpreted(function, left, wrongRight)
}
