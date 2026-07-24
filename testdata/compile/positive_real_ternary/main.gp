package compilefixture

import "goforge.dev/gosmt"

func AcceptedRealTernary() {
	context := gosmt.NewContext(7)
	x := gosmt.RealConst(context, "x", 1)
	function := gosmt.DeclareRealTernary(context, "combine3", 2)
	_ = gosmt.ApplyRealTernary(function, x, x, x)
}
