package compilefixture

import "goforge.dev/gosmt"

func AcceptedAndPair() {
	context := gosmt.NewContext(7)
	left := gosmt.BoolConst(context, "left", 1)
	right := gosmt.BoolConst(context, "right", 2)
	_ = gosmt.AndPair(left, right)
}
