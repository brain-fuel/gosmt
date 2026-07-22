package compilefixture

import "goforge.dev/gosmt"

func RejectedIntegerContext() {
	leftContext := gosmt.NewContext(7)
	rightContext := gosmt.NewContext(8)
	left := gosmt.IntConst(leftContext, "left", 1)
	right := gosmt.IntConst(rightContext, "right", 2)
	_ = gosmt.Le(left, right)
}
