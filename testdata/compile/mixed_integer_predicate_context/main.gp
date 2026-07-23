package compilefixture

import "goforge.dev/gosmt"

func RejectedIntegerPredicateContext() {
	predicateContext := gosmt.NewContext(7)
	argumentContext := gosmt.NewContext(8)
	predicate := gosmt.DeclareIntPredicate(predicateContext, "p", 1)
	argument := gosmt.IntConst(argumentContext, "x", 2)
	_ = gosmt.ApplyIntPredicate(predicate, argument)
}
