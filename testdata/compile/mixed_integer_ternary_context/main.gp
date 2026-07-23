package compilefixture

import "goforge.dev/gosmt"

func RejectedIntegerTernaryFunctionContext() {
	functionContext := gosmt.NewContext(7)
	argumentContext := gosmt.NewContext(8)
	function := gosmt.DeclareIntTernary(functionContext, "f", 1)
	first := gosmt.IntConst(functionContext, "x", 2)
	second := gosmt.IntConst(functionContext, "y", 3)
	third := gosmt.IntConst(argumentContext, "z", 4)
	_ = gosmt.ApplyIntTernary(function, first, second, third)
}
