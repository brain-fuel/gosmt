package compilefixture

import "goforge.dev/gosmt"

func RejectedIntegerFunctionContext() {
	functionContext := gosmt.NewContext(7)
	argumentContext := gosmt.NewContext(8)
	function := gosmt.DeclareIntFunction(functionContext, "f", 1)
	argument := gosmt.IntConst(argumentContext, "x", 2)
	_ = gosmt.ApplyIntFunction(function, argument)
}
