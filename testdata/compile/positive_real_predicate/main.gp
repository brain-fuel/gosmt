package compilefixture

import "goforge.dev/gosmt"

func AcceptedRealPredicates() {
	context := gosmt.NewContext(7)
	x := gosmt.RealConst(context, "x", 1)
	unary := gosmt.DeclareRealPredicate(context, "p", 2)
	_ = gosmt.ApplyRealPredicate(unary, x)
	binary := gosmt.DeclareRealBinaryPredicate(context, "q", 3)
	_ = gosmt.ApplyRealBinaryPredicate(binary, x, x)
}
