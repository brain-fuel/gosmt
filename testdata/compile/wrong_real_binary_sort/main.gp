package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	function := gosmt.DeclareRealBinary(context, "combine", 1)
	real := gosmt.RealConst(context, "x", 2)
	integer := gosmt.IntConst(context, "y", 3)
	_ = gosmt.ApplyRealBinary(function, real, integer)
}
