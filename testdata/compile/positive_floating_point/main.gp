package compilefixture

import "goforge.dev/gosmt"

func AcceptedFloatingPoint() {
	context := gosmt.NewContext(7)
	left := gosmt.FloatingPointFromUint64(8, 24, context, 0x3f800000)
	right := gosmt.FloatingPointFromUint64(8, 24, context, 0x40000000)
	_ = gosmt.FloatingPointEqual(left, right)
	_ = gosmt.FloatingPointBits(left)
	symbolic := gosmt.FloatingPointConst(8, 24, context, "x", 1)
	_ = gosmt.FloatingPointIsNormal(symbolic)
}
