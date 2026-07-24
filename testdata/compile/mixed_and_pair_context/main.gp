package compilefixture

import "goforge.dev/gosmt"

func RejectedAndPairContext() {
	leftContext := gosmt.NewContext(7)
	rightContext := gosmt.NewContext(8)
	left := gosmt.BoolConst(leftContext, "left", 1)
	right := gosmt.BoolConst(rightContext, "right", 2)
	_ = gosmt.AndPair(left, right)
}
