package compilefixture

import gosmt "goforge.dev/gosmt"

func main() {
	context := gosmt.NewContext(1)
	signature := gosmt.IntDatatypeMixedField("payload", gosmt.SelfDatatypeMixedField("next", gosmt.EmptyDatatypeMixedSignature()))
	node := gosmt.DeclareMixedDatatypeConstructor(1, 2, 1, context, "node", signature)
	leaf := gosmt.DatatypeConstructor(1, 2, 0, context, "leaf")
	arguments := gosmt.SelfDatatypeMixedArgument(leaf, gosmt.IntDatatypeMixedArgument(gosmt.IntVal(context, 1), gosmt.EmptyDatatypeMixedArguments(context)))
	_ = gosmt.ApplyMixedDatatypeConstructor(node, arguments)
}
