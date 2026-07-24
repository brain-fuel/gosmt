package compilefixture

import "goforge.dev/gosmt"

func RejectedRealPredicateContext() {
	leftContext := gosmt.NewContext(7)
	rightContext := gosmt.NewContext(8)
	predicate := gosmt.DeclareRealPredicate(leftContext, "p", 1)
	right := gosmt.RealConst(rightContext, "right", 2)
	_ = gosmt.ApplyRealPredicate(predicate, right)
}
