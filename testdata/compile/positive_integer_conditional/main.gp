package compilefixture

import "goforge.dev/gosmt"

func AcceptedIntegerConditional() {
	context := gosmt.NewContext(7)
	condition := gosmt.BoolConst(context, "condition", 1)
	thenValue := gosmt.IntConst(context, "then", 2)
	elseValue := gosmt.IntConst(context, "else", 3)
	_ = gosmt.IfInt(condition, thenValue, elseValue)
}
