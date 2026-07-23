package compilefixture

import "goforge.dev/gosmt"

func RejectedBinaryIntegerPredicateContext() {
	predicateContext := gosmt.NewContext(7)
	argumentContext := gosmt.NewContext(8)
	predicate := gosmt.DeclareIntBinaryPredicate(predicateContext, "p", 1)
	first := gosmt.IntConst(predicateContext, "x", 2)
	second := gosmt.IntConst(argumentContext, "y", 3)
	_ = gosmt.ApplyIntBinaryPredicate(predicate, first, second)
}
