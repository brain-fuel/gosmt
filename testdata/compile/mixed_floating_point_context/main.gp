package compilefixture

import "goforge.dev/gosmt"

func RejectedFloatingPointContext() {
	leftContext := gosmt.NewContext(7)
	rightContext := gosmt.NewContext(8)
	left := gosmt.FloatingPointFromUint64(8, 24, leftContext, 0x3f800000)
	right := gosmt.FloatingPointFromUint64(8, 24, rightContext, 0x40000000)
	_ = gosmt.FloatingPointEqual(left, right)
}
