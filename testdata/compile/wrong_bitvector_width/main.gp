package compilefixture

import "goforge.dev/gosmt"

func Rejected() {
	context := gosmt.NewContext(7)
	byteValue := gosmt.BitVecValue(8, context, 1)
	wordValue := gosmt.BitVecValue(16, context, 1)
	_ = gosmt.AndBitVec(byteValue, wordValue)
}
