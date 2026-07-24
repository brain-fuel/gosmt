package compilefixture

import "goforge.dev/gosmt"

func RejectedFloatingPointBitWidth() {
	context := gosmt.NewContext(7)
	halfBits := gosmt.BitVecValue(16, context, 0x3c00)
	_ = gosmt.FloatingPointFromIEEEBitVec(8, 24, halfBits)
}
