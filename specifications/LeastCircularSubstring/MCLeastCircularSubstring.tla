--------------------- MODULE MCLeastCircularSubstring -----------------------
EXTENDS Naturals, LeastCircularSubstring

CONSTANTS CharSetSize, MaxStringLength

ZSeqNat == 0 .. MaxStringLength

MCCharacterSet == 0 .. (CharSetSize - 1)

=============================================================================

