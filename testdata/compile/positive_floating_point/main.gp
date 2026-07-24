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
	_ = gosmt.FloatingPointAbs(symbolic)
	_ = gosmt.FloatingPointNeg(symbolic)
	_ = gosmt.FloatingPointLessThan(left, right)
	_ = gosmt.FloatingPointLessOrEqual(left, right)
	_ = gosmt.FloatingPointGreaterThan(left, right)
	_ = gosmt.FloatingPointGreaterOrEqual(left, right)
	_ = gosmt.FloatingPointMin(left, right)
	_ = gosmt.FloatingPointMax(left, right)
}
