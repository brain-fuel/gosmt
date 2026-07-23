package compilefixture

import "goforge.dev/gosmt"

func AcceptedIntegerTernaryFunction() {
	context := gosmt.NewContext(7)
	function := gosmt.DeclareIntTernary(context, "f", 1)
	x := gosmt.IntConst(context, "x", 2)
	y := gosmt.IntConst(context, "y", 3)
	z := gosmt.IntConst(context, "z", 4)
	_ = gosmt.ApplyIntTernary(function, x, y, z)
}
