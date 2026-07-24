package compilefixture

import "goforge.dev/gosmt"

func RejectedFloatingPointFormat() {
	context := gosmt.NewContext(7)
	single := gosmt.FloatingPointFromUint64(8, 24, context, 0x3f800000)
	half := gosmt.FloatingPointFromUint64(5, 11, context, 0x3c00)
	_ = gosmt.FloatingPointEqual(single, half)
}
