package compilefixture

import "goforge.dev/gosmt"

func RejectedIntegerConditionalContext() {
	conditionContext := gosmt.NewContext(7)
	valueContext := gosmt.NewContext(8)
	condition := gosmt.BoolConst(conditionContext, "condition", 1)
	thenValue := gosmt.IntConst(conditionContext, "then", 2)
	elseValue := gosmt.IntConst(valueContext, "else", 3)
	_ = gosmt.IfInt(condition, thenValue, elseValue)
}
