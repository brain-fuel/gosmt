package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	function := gosmt.DeclareRealFunction(context, "f", 1)
	integer := gosmt.IntConst(context, "x", 2)
	_ = gosmt.ApplyRealFunction(function, integer)
}
