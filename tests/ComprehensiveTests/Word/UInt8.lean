import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

set_option maxRecDepth 8192

/-!
# UInt8 Comprehensive Tests

Exhaustive unit tests for all Radix.UInt8 operations:
- 5 arithmetic modes (proof-carrying, wrapping, saturating, checked, overflowing)
- Bitwise operations (AND, OR, XOR, NOT, shifts, rotates)
- Scan operations (clz, ctz, popcount)
- Bit field operations (testBit, setBit, clearBit, toggleBit, extract, insert)
- bitReverse, hammingDistance, shrArith
- Edge cases: 0, 1, MAX(255), powers of 2, alternating bits

## Spec References

- FR-001.1: Unsigned integer types (UInt8)
- FR-001.2: Arithmetic operations
- FR-002: Bitwise operations
-/

open ComprehensiveTests

def runUInt8Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UInt8 unit tests..."

  -- ## Wrapping Arithmetic

  -- wrappingAdd: normal cases
  assert ((Radix.UInt8.wrappingAdd ⟨1⟩ ⟨2⟩).toNat == 3) "wrappingAdd 1+2=3"
  assert ((Radix.UInt8.wrappingAdd ⟨100⟩ ⟨50⟩).toNat == 150) "wrappingAdd 100+50=150"
  assert ((Radix.UInt8.wrappingAdd ⟨0⟩ ⟨0⟩).toNat == 0) "wrappingAdd 0+0=0"
  -- wrappingAdd: overflow cases
  assert ((Radix.UInt8.wrappingAdd ⟨200⟩ ⟨100⟩).toNat == 44) "wrappingAdd 200+100=44"
  assert ((Radix.UInt8.wrappingAdd ⟨255⟩ ⟨1⟩).toNat == 0) "wrappingAdd 255+1=0"
  assert ((Radix.UInt8.wrappingAdd ⟨255⟩ ⟨255⟩).toNat == 254) "wrappingAdd 255+255=254"
  assert ((Radix.UInt8.wrappingAdd ⟨128⟩ ⟨128⟩).toNat == 0) "wrappingAdd 128+128=0"
  -- wrappingAdd: identity
  assert ((Radix.UInt8.wrappingAdd ⟨42⟩ ⟨0⟩).toNat == 42) "wrappingAdd identity"
  assert ((Radix.UInt8.wrappingAdd ⟨0⟩ ⟨42⟩).toNat == 42) "wrappingAdd identity2"
  -- wrappingAdd: boundary
  assert ((Radix.UInt8.wrappingAdd ⟨127⟩ ⟨128⟩).toNat == 255) "wrappingAdd 127+128=255"
  assert ((Radix.UInt8.wrappingAdd ⟨254⟩ ⟨1⟩).toNat == 255) "wrappingAdd 254+1=255"

  -- wrappingSub: normal cases
  assert ((Radix.UInt8.wrappingSub ⟨20⟩ ⟨10⟩).toNat == 10) "wrappingSub 20-10=10"
  assert ((Radix.UInt8.wrappingSub ⟨255⟩ ⟨0⟩).toNat == 255) "wrappingSub 255-0=255"
  assert ((Radix.UInt8.wrappingSub ⟨0⟩ ⟨0⟩).toNat == 0) "wrappingSub 0-0=0"
  -- wrappingSub: underflow cases
  assert ((Radix.UInt8.wrappingSub ⟨0⟩ ⟨1⟩).toNat == 255) "wrappingSub 0-1=255"
  assert ((Radix.UInt8.wrappingSub ⟨10⟩ ⟨20⟩).toNat == 246) "wrappingSub 10-20=246"
  assert ((Radix.UInt8.wrappingSub ⟨0⟩ ⟨255⟩).toNat == 1) "wrappingSub 0-255=1"
  -- wrappingSub: self
  assert ((Radix.UInt8.wrappingSub ⟨128⟩ ⟨128⟩).toNat == 0) "wrappingSub self=0"
  assert ((Radix.UInt8.wrappingSub ⟨255⟩ ⟨255⟩).toNat == 0) "wrappingSub MAX-MAX=0"

  -- wrappingMul: normal cases
  assert ((Radix.UInt8.wrappingMul ⟨3⟩ ⟨4⟩).toNat == 12) "wrappingMul 3*4=12"
  assert ((Radix.UInt8.wrappingMul ⟨15⟩ ⟨15⟩).toNat == 225) "wrappingMul 15*15=225"
  -- wrappingMul: overflow
  assert ((Radix.UInt8.wrappingMul ⟨16⟩ ⟨17⟩).toNat == 16) "wrappingMul 16*17=16"
  assert ((Radix.UInt8.wrappingMul ⟨255⟩ ⟨2⟩).toNat == 254) "wrappingMul 255*2=254"
  assert ((Radix.UInt8.wrappingMul ⟨128⟩ ⟨2⟩).toNat == 0) "wrappingMul 128*2=0"
  -- wrappingMul: identity and zero
  assert ((Radix.UInt8.wrappingMul ⟨42⟩ ⟨1⟩).toNat == 42) "wrappingMul identity"
  assert ((Radix.UInt8.wrappingMul ⟨42⟩ ⟨0⟩).toNat == 0) "wrappingMul zero"
  assert ((Radix.UInt8.wrappingMul ⟨0⟩ ⟨255⟩).toNat == 0) "wrappingMul 0*MAX"

  -- wrappingNeg
  assert ((Radix.UInt8.wrappingNeg ⟨0⟩).toNat == 0) "wrappingNeg 0=0"
  assert ((Radix.UInt8.wrappingNeg ⟨1⟩).toNat == 255) "wrappingNeg 1=255"
  assert ((Radix.UInt8.wrappingNeg ⟨128⟩).toNat == 128) "wrappingNeg 128=128"
  assert ((Radix.UInt8.wrappingNeg ⟨255⟩).toNat == 1) "wrappingNeg 255=1"
  assert ((Radix.UInt8.wrappingNeg ⟨127⟩).toNat == 129) "wrappingNeg 127=129"

  -- ## Saturating Arithmetic

  -- saturatingAdd
  assert ((Radix.UInt8.saturatingAdd ⟨200⟩ ⟨100⟩).toNat == 255) "satAdd 200+100=255"
  assert ((Radix.UInt8.saturatingAdd ⟨255⟩ ⟨255⟩).toNat == 255) "satAdd MAX+MAX=255"
  assert ((Radix.UInt8.saturatingAdd ⟨255⟩ ⟨1⟩).toNat == 255) "satAdd MAX+1=255"
  assert ((Radix.UInt8.saturatingAdd ⟨100⟩ ⟨50⟩).toNat == 150) "satAdd 100+50=150"
  assert ((Radix.UInt8.saturatingAdd ⟨0⟩ ⟨0⟩).toNat == 0) "satAdd 0+0=0"
  assert ((Radix.UInt8.saturatingAdd ⟨254⟩ ⟨1⟩).toNat == 255) "satAdd 254+1=255"
  assert ((Radix.UInt8.saturatingAdd ⟨127⟩ ⟨128⟩).toNat == 255) "satAdd 127+128=255"

  -- saturatingSub
  assert ((Radix.UInt8.saturatingSub ⟨10⟩ ⟨20⟩).toNat == 0) "satSub 10-20=0"
  assert ((Radix.UInt8.saturatingSub ⟨0⟩ ⟨255⟩).toNat == 0) "satSub 0-255=0"
  assert ((Radix.UInt8.saturatingSub ⟨0⟩ ⟨1⟩).toNat == 0) "satSub 0-1=0"
  assert ((Radix.UInt8.saturatingSub ⟨255⟩ ⟨0⟩).toNat == 255) "satSub 255-0=255"
  assert ((Radix.UInt8.saturatingSub ⟨20⟩ ⟨10⟩).toNat == 10) "satSub 20-10=10"
  assert ((Radix.UInt8.saturatingSub ⟨128⟩ ⟨128⟩).toNat == 0) "satSub self=0"

  -- saturatingMul
  assert ((Radix.UInt8.saturatingMul ⟨16⟩ ⟨17⟩).toNat == 255) "satMul overflow=255"
  assert ((Radix.UInt8.saturatingMul ⟨255⟩ ⟨2⟩).toNat == 255) "satMul MAX*2=255"
  assert ((Radix.UInt8.saturatingMul ⟨3⟩ ⟨4⟩).toNat == 12) "satMul 3*4=12"
  assert ((Radix.UInt8.saturatingMul ⟨42⟩ ⟨0⟩).toNat == 0) "satMul x*0=0"
  assert ((Radix.UInt8.saturatingMul ⟨42⟩ ⟨1⟩).toNat == 42) "satMul x*1=x"
  assert ((Radix.UInt8.saturatingMul ⟨128⟩ ⟨2⟩).toNat == 255) "satMul 128*2=255"

  -- ## Checked Arithmetic

  -- checkedAdd
  assert (Radix.UInt8.checkedAdd ⟨200⟩ ⟨100⟩ == none) "chkAdd overflow=none"
  assert (Radix.UInt8.checkedAdd ⟨100⟩ ⟨50⟩ == some ⟨150⟩) "chkAdd 100+50"
  assert (Radix.UInt8.checkedAdd ⟨255⟩ ⟨0⟩ == some ⟨255⟩) "chkAdd MAX+0"
  assert (Radix.UInt8.checkedAdd ⟨0⟩ ⟨0⟩ == some ⟨0⟩) "chkAdd 0+0"
  assert (Radix.UInt8.checkedAdd ⟨255⟩ ⟨1⟩ == none) "chkAdd MAX+1=none"
  assert (Radix.UInt8.checkedAdd ⟨128⟩ ⟨127⟩ == some ⟨255⟩) "chkAdd 128+127=255"
  assert (Radix.UInt8.checkedAdd ⟨128⟩ ⟨128⟩ == none) "chkAdd 128+128=none"

  -- checkedSub
  assert (Radix.UInt8.checkedSub ⟨10⟩ ⟨20⟩ == none) "chkSub underflow=none"
  assert (Radix.UInt8.checkedSub ⟨20⟩ ⟨10⟩ == some ⟨10⟩) "chkSub 20-10"
  assert (Radix.UInt8.checkedSub ⟨0⟩ ⟨0⟩ == some ⟨0⟩) "chkSub 0-0"
  assert (Radix.UInt8.checkedSub ⟨255⟩ ⟨255⟩ == some ⟨0⟩) "chkSub MAX-MAX"
  assert (Radix.UInt8.checkedSub ⟨0⟩ ⟨1⟩ == none) "chkSub 0-1=none"

  -- checkedMul
  assert (Radix.UInt8.checkedMul ⟨200⟩ ⟨2⟩ == none) "chkMul overflow=none"
  assert (Radix.UInt8.checkedMul ⟨10⟩ ⟨20⟩ == some ⟨200⟩) "chkMul 10*20"
  assert (Radix.UInt8.checkedMul ⟨0⟩ ⟨255⟩ == some ⟨0⟩) "chkMul 0*MAX"
  assert (Radix.UInt8.checkedMul ⟨15⟩ ⟨17⟩ == some ⟨255⟩) "chkMul 15*17=255"
  assert (Radix.UInt8.checkedMul ⟨16⟩ ⟨16⟩ == none) "chkMul 16*16=none"

  -- checkedDiv
  assert (Radix.UInt8.checkedDiv ⟨10⟩ ⟨0⟩ == none) "chkDiv /0=none"
  assert (Radix.UInt8.checkedDiv ⟨10⟩ ⟨2⟩ == some ⟨5⟩) "chkDiv 10/2=5"
  assert (Radix.UInt8.checkedDiv ⟨255⟩ ⟨1⟩ == some ⟨255⟩) "chkDiv MAX/1=MAX"
  assert (Radix.UInt8.checkedDiv ⟨0⟩ ⟨1⟩ == some ⟨0⟩) "chkDiv 0/1=0"
  assert (Radix.UInt8.checkedDiv ⟨255⟩ ⟨255⟩ == some ⟨1⟩) "chkDiv MAX/MAX=1"
  assert (Radix.UInt8.checkedDiv ⟨7⟩ ⟨3⟩ == some ⟨2⟩) "chkDiv 7/3=2"
  assert (Radix.UInt8.checkedDiv ⟨0⟩ ⟨0⟩ == none) "chkDiv 0/0=none"

  -- checkedRem
  assert (Radix.UInt8.checkedRem ⟨10⟩ ⟨0⟩ == none) "chkRem %0=none"
  assert (Radix.UInt8.checkedRem ⟨10⟩ ⟨3⟩ == some ⟨1⟩) "chkRem 10%3=1"
  assert (Radix.UInt8.checkedRem ⟨255⟩ ⟨128⟩ == some ⟨127⟩) "chkRem 255%128=127"
  assert (Radix.UInt8.checkedRem ⟨100⟩ ⟨100⟩ == some ⟨0⟩) "chkRem self=0"
  assert (Radix.UInt8.checkedRem ⟨0⟩ ⟨42⟩ == some ⟨0⟩) "chkRem 0%x=0"

  -- ## Overflowing Arithmetic

  let (r1, ov1) := Radix.UInt8.overflowingAdd ⟨200⟩ ⟨100⟩
  assert (r1.toNat == 44 && ov1 == true) "ovfAdd 200+100 overflow"
  let (r2, ov2) := Radix.UInt8.overflowingAdd ⟨1⟩ ⟨2⟩
  assert (r2.toNat == 3 && ov2 == false) "ovfAdd 1+2 no overflow"
  let (r3, ov3) := Radix.UInt8.overflowingAdd ⟨255⟩ ⟨1⟩
  assert (r3.toNat == 0 && ov3 == true) "ovfAdd MAX+1 overflow"
  let (r4, ov4) := Radix.UInt8.overflowingAdd ⟨0⟩ ⟨0⟩
  assert (r4.toNat == 0 && ov4 == false) "ovfAdd 0+0 no overflow"
  let (r5, ov5) := Radix.UInt8.overflowingAdd ⟨128⟩ ⟨127⟩
  assert (r5.toNat == 255 && ov5 == false) "ovfAdd 128+127 exact max"

  let (rs1, os1) := Radix.UInt8.overflowingSub ⟨10⟩ ⟨20⟩
  assert (rs1.toNat == 246 && os1 == true) "ovfSub 10-20 underflow"
  let (rs2, os2) := Radix.UInt8.overflowingSub ⟨20⟩ ⟨10⟩
  assert (rs2.toNat == 10 && os2 == false) "ovfSub 20-10 no underflow"
  let (rs3, os3) := Radix.UInt8.overflowingSub ⟨0⟩ ⟨1⟩
  assert (rs3.toNat == 255 && os3 == true) "ovfSub 0-1 underflow"
  let (rs4, os4) := Radix.UInt8.overflowingSub ⟨255⟩ ⟨255⟩
  assert (rs4.toNat == 0 && os4 == false) "ovfSub MAX-MAX no underflow"

  let (rm1, om1) := Radix.UInt8.overflowingMul ⟨16⟩ ⟨17⟩
  assert (rm1.toNat == 16 && om1 == true) "ovfMul 16*17 overflow"
  let (rm2, om2) := Radix.UInt8.overflowingMul ⟨3⟩ ⟨4⟩
  assert (rm2.toNat == 12 && om2 == false) "ovfMul 3*4 no overflow"
  let (rm3, om3) := Radix.UInt8.overflowingMul ⟨255⟩ ⟨0⟩
  assert (rm3.toNat == 0 && om3 == false) "ovfMul MAX*0 no overflow"

  -- ## Bitwise Operations

  -- band
  assert ((Radix.UInt8.band ⟨0xAA⟩ ⟨0x0F⟩).toNat == 0x0A) "band AA&0F=0A"
  assert ((Radix.UInt8.band ⟨0xFF⟩ ⟨0x00⟩).toNat == 0x00) "band FF&00=00"
  assert ((Radix.UInt8.band ⟨0xFF⟩ ⟨0xFF⟩).toNat == 0xFF) "band FF&FF=FF"
  assert ((Radix.UInt8.band ⟨0x55⟩ ⟨0xAA⟩).toNat == 0x00) "band 55&AA=00"
  assert ((Radix.UInt8.band ⟨0x12⟩ ⟨0x34⟩).toNat == 0x10) "band 12&34=10"
  -- bor
  assert ((Radix.UInt8.bor ⟨0xA0⟩ ⟨0x0F⟩).toNat == 0xAF) "bor A0|0F=AF"
  assert ((Radix.UInt8.bor ⟨0x00⟩ ⟨0x00⟩).toNat == 0x00) "bor 00|00=00"
  assert ((Radix.UInt8.bor ⟨0xFF⟩ ⟨0x00⟩).toNat == 0xFF) "bor FF|00=FF"
  assert ((Radix.UInt8.bor ⟨0x55⟩ ⟨0xAA⟩).toNat == 0xFF) "bor 55|AA=FF"
  -- bxor
  assert ((Radix.UInt8.bxor ⟨0xFF⟩ ⟨0xAA⟩).toNat == 0x55) "bxor FF^AA=55"
  assert ((Radix.UInt8.bxor ⟨0xFF⟩ ⟨0xFF⟩).toNat == 0x00) "bxor FF^FF=00"
  assert ((Radix.UInt8.bxor ⟨0x00⟩ ⟨0xFF⟩).toNat == 0xFF) "bxor 00^FF=FF"
  assert ((Radix.UInt8.bxor ⟨0x55⟩ ⟨0xAA⟩).toNat == 0xFF) "bxor 55^AA=FF"
  assert ((Radix.UInt8.bxor ⟨0x00⟩ ⟨0x00⟩).toNat == 0x00) "bxor 00^00=00"
  -- bnot
  assert ((Radix.UInt8.bnot ⟨0x00⟩).toNat == 0xFF) "bnot 00=FF"
  assert ((Radix.UInt8.bnot ⟨0xFF⟩).toNat == 0x00) "bnot FF=00"
  assert ((Radix.UInt8.bnot ⟨0xAA⟩).toNat == 0x55) "bnot AA=55"
  assert ((Radix.UInt8.bnot ⟨0x55⟩).toNat == 0xAA) "bnot 55=AA"
  assert ((Radix.UInt8.bnot ⟨0x0F⟩).toNat == 0xF0) "bnot 0F=F0"

  -- ## Shift Operations

  -- shl
  assert ((Radix.UInt8.shl ⟨1⟩ ⟨0⟩).toNat == 1) "shl 1<<0=1"
  assert ((Radix.UInt8.shl ⟨1⟩ ⟨1⟩).toNat == 2) "shl 1<<1=2"
  assert ((Radix.UInt8.shl ⟨1⟩ ⟨3⟩).toNat == 8) "shl 1<<3=8"
  assert ((Radix.UInt8.shl ⟨1⟩ ⟨7⟩).toNat == 128) "shl 1<<7=128"
  assert ((Radix.UInt8.shl ⟨0xFF⟩ ⟨1⟩).toNat == 0xFE) "shl FF<<1=FE"
  assert ((Radix.UInt8.shl ⟨0xFF⟩ ⟨4⟩).toNat == 0xF0) "shl FF<<4=F0"
  assert ((Radix.UInt8.shl ⟨0⟩ ⟨5⟩).toNat == 0) "shl 0<<5=0"

  -- shrLogical
  assert ((Radix.UInt8.shrLogical ⟨128⟩ ⟨3⟩).toNat == 16) "shrL 128>>3=16"
  assert ((Radix.UInt8.shrLogical ⟨255⟩ ⟨4⟩).toNat == 15) "shrL 255>>4=15"
  assert ((Radix.UInt8.shrLogical ⟨1⟩ ⟨1⟩).toNat == 0) "shrL 1>>1=0"
  assert ((Radix.UInt8.shrLogical ⟨0x80⟩ ⟨7⟩).toNat == 1) "shrL 80>>7=1"
  assert ((Radix.UInt8.shrLogical ⟨0xFF⟩ ⟨0⟩).toNat == 255) "shrL FF>>0=FF"
  assert ((Radix.UInt8.shrLogical ⟨0⟩ ⟨3⟩).toNat == 0) "shrL 0>>3=0"

  -- shrArith
  assert ((Radix.UInt8.shrArith ⟨0x80⟩ ⟨1⟩).toNat == 0xC0) "shrA 80>>1=C0"
  assert ((Radix.UInt8.shrArith ⟨0x40⟩ ⟨1⟩).toNat == 0x20) "shrA 40>>1=20"
  assert ((Radix.UInt8.shrArith ⟨0xFF⟩ ⟨1⟩).toNat == 0xFF) "shrA FF>>1=FF"
  assert ((Radix.UInt8.shrArith ⟨0xFF⟩ ⟨4⟩).toNat == 0xFF) "shrA FF>>4=FF"
  assert ((Radix.UInt8.shrArith ⟨0x80⟩ ⟨7⟩).toNat == 0xFF) "shrA 80>>7=FF"
  assert ((Radix.UInt8.shrArith ⟨0x7F⟩ ⟨1⟩).toNat == 0x3F) "shrA 7F>>1=3F"

  -- ## Rotate Operations

  assert ((Radix.UInt8.rotl ⟨0x81⟩ ⟨1⟩).toNat == 0x03) "rotl 81 1=03"
  assert ((Radix.UInt8.rotl ⟨1⟩ ⟨0⟩).toNat == 1) "rotl 1 0=1"
  assert ((Radix.UInt8.rotl ⟨0x80⟩ ⟨1⟩).toNat == 0x01) "rotl 80 1=01"
  assert ((Radix.UInt8.rotl ⟨0xFF⟩ ⟨3⟩).toNat == 0xFF) "rotl FF 3=FF"
  assert ((Radix.UInt8.rotl ⟨0x01⟩ ⟨4⟩).toNat == 0x10) "rotl 01 4=10"
  assert ((Radix.UInt8.rotr ⟨0x81⟩ ⟨1⟩).toNat == 0xC0) "rotr 81 1=C0"
  assert ((Radix.UInt8.rotr ⟨1⟩ ⟨1⟩).toNat == 0x80) "rotr 1 1=80"
  assert ((Radix.UInt8.rotr ⟨0x01⟩ ⟨0⟩).toNat == 0x01) "rotr 01 0=01"
  assert ((Radix.UInt8.rotr ⟨0xFF⟩ ⟨4⟩).toNat == 0xFF) "rotr FF 4=FF"
  assert ((Radix.UInt8.rotr ⟨0x10⟩ ⟨4⟩).toNat == 0x01) "rotr 10 4=01"

  -- ## Scan Operations

  -- clz
  assert (Radix.UInt8.clz ⟨0⟩ == 8) "clz 0=8"
  assert (Radix.UInt8.clz ⟨1⟩ == 7) "clz 1=7"
  assert (Radix.UInt8.clz ⟨2⟩ == 6) "clz 2=6"
  assert (Radix.UInt8.clz ⟨4⟩ == 5) "clz 4=5"
  assert (Radix.UInt8.clz ⟨8⟩ == 4) "clz 8=4"
  assert (Radix.UInt8.clz ⟨16⟩ == 3) "clz 16=3"
  assert (Radix.UInt8.clz ⟨32⟩ == 2) "clz 32=2"
  assert (Radix.UInt8.clz ⟨64⟩ == 1) "clz 64=1"
  assert (Radix.UInt8.clz ⟨128⟩ == 0) "clz 128=0"
  assert (Radix.UInt8.clz ⟨255⟩ == 0) "clz 255=0"
  assert (Radix.UInt8.clz ⟨127⟩ == 1) "clz 127=1"

  -- ctz
  assert (Radix.UInt8.ctz ⟨0⟩ == 8) "ctz 0=8"
  assert (Radix.UInt8.ctz ⟨1⟩ == 0) "ctz 1=0"
  assert (Radix.UInt8.ctz ⟨2⟩ == 1) "ctz 2=1"
  assert (Radix.UInt8.ctz ⟨4⟩ == 2) "ctz 4=2"
  assert (Radix.UInt8.ctz ⟨8⟩ == 3) "ctz 8=3"
  assert (Radix.UInt8.ctz ⟨128⟩ == 7) "ctz 128=7"
  assert (Radix.UInt8.ctz ⟨255⟩ == 0) "ctz 255=0"
  assert (Radix.UInt8.ctz ⟨0x10⟩ == 4) "ctz 10=4"

  -- popcount
  assert (Radix.UInt8.popcount ⟨0⟩ == 0) "popcount 0=0"
  assert (Radix.UInt8.popcount ⟨255⟩ == 8) "popcount FF=8"
  assert (Radix.UInt8.popcount ⟨0xAA⟩ == 4) "popcount AA=4"
  assert (Radix.UInt8.popcount ⟨0x55⟩ == 4) "popcount 55=4"
  assert (Radix.UInt8.popcount ⟨1⟩ == 1) "popcount 1=1"
  assert (Radix.UInt8.popcount ⟨128⟩ == 1) "popcount 128=1"
  assert (Radix.UInt8.popcount ⟨0x0F⟩ == 4) "popcount 0F=4"

  -- ## Bit Field Operations

  -- testBit
  assert (Radix.UInt8.testBit ⟨5⟩ 0 == true) "testBit 5[0]=T"
  assert (Radix.UInt8.testBit ⟨5⟩ 1 == false) "testBit 5[1]=F"
  assert (Radix.UInt8.testBit ⟨5⟩ 2 == true) "testBit 5[2]=T"
  assert (Radix.UInt8.testBit ⟨0x80⟩ 7 == true) "testBit 80[7]=T"
  assert (Radix.UInt8.testBit ⟨0⟩ 0 == false) "testBit 0[0]=F"
  assert (Radix.UInt8.testBit ⟨0xFF⟩ 4 == true) "testBit FF[4]=T"

  -- setBit
  assert ((Radix.UInt8.setBit ⟨0⟩ 0).toNat == 1) "setBit 0[0]=1"
  assert ((Radix.UInt8.setBit ⟨0⟩ 3).toNat == 8) "setBit 0[3]=8"
  assert ((Radix.UInt8.setBit ⟨0⟩ 7).toNat == 128) "setBit 0[7]=128"
  assert ((Radix.UInt8.setBit ⟨0xFF⟩ 0).toNat == 0xFF) "setBit FF[0]=FF"
  assert ((Radix.UInt8.setBit ⟨0x0E⟩ 0).toNat == 0x0F) "setBit 0E[0]=0F"

  -- clearBit
  assert ((Radix.UInt8.clearBit ⟨0xFF⟩ 0).toNat == 0xFE) "clearBit FF[0]=FE"
  assert ((Radix.UInt8.clearBit ⟨0xFF⟩ 7).toNat == 0x7F) "clearBit FF[7]=7F"
  assert ((Radix.UInt8.clearBit ⟨0x01⟩ 0).toNat == 0) "clearBit 01[0]=00"
  assert ((Radix.UInt8.clearBit ⟨0⟩ 3).toNat == 0) "clearBit 0[3]=0"

  -- toggleBit
  assert ((Radix.UInt8.toggleBit ⟨0⟩ 0).toNat == 1) "toggleBit 0[0]=1"
  assert ((Radix.UInt8.toggleBit ⟨1⟩ 0).toNat == 0) "toggleBit 1[0]=0"
  assert ((Radix.UInt8.toggleBit ⟨0xFF⟩ 7).toNat == 0x7F) "toggleBit FF[7]=7F"
  assert ((Radix.UInt8.toggleBit ⟨0x7F⟩ 7).toNat == 0xFF) "toggleBit 7F[7]=FF"

  -- extractBits / insertBits
  assert ((Radix.UInt8.extractBits ⟨0xAB⟩ 4 8 ⟨by omega, by omega⟩).toNat == 0x0A)
    "extractBits AB[4:8]=0A"
  assert ((Radix.UInt8.extractBits ⟨0xFF⟩ 0 4 ⟨by omega, by omega⟩).toNat == 0x0F)
    "extractBits FF[0:4]=0F"
  assert ((Radix.UInt8.extractBits ⟨0x55⟩ 0 8 ⟨by omega, by omega⟩).toNat == 0x55)
    "extractBits 55[0:8]=55"
  assert ((Radix.UInt8.insertBits ⟨0x00⟩ ⟨0x0F⟩ 4 8 ⟨by omega, by omega⟩).toNat == 0xF0)
    "insertBits 00 0F at [4:8]=F0"
  assert ((Radix.UInt8.insertBits ⟨0xFF⟩ ⟨0x00⟩ 4 8 ⟨by omega, by omega⟩).toNat == 0x0F)
    "insertBits FF 00 at [4:8]=0F"

  -- ## bitReverse

  assert ((Radix.UInt8.bitReverse ⟨0x80⟩).toNat == 0x01) "bitReverse 80=01"
  assert ((Radix.UInt8.bitReverse ⟨0x01⟩).toNat == 0x80) "bitReverse 01=80"
  assert ((Radix.UInt8.bitReverse ⟨0x00⟩).toNat == 0x00) "bitReverse 00=00"
  assert ((Radix.UInt8.bitReverse ⟨0xFF⟩).toNat == 0xFF) "bitReverse FF=FF"
  assert ((Radix.UInt8.bitReverse ⟨0x0F⟩).toNat == 0xF0) "bitReverse 0F=F0"
  assert ((Radix.UInt8.bitReverse ⟨0xF0⟩).toNat == 0x0F) "bitReverse F0=0F"
  assert ((Radix.UInt8.bitReverse ⟨0xAA⟩).toNat == 0x55) "bitReverse AA=55"
  assert ((Radix.UInt8.bitReverse ⟨0x55⟩).toNat == 0xAA) "bitReverse 55=AA"

  -- ## hammingDistance

  assert ((Radix.UInt8.hammingDistance ⟨0xFF⟩ ⟨0x00⟩).toNat == 8) "hamming FF,00=8"
  assert ((Radix.UInt8.hammingDistance ⟨0xAA⟩ ⟨0x55⟩).toNat == 8) "hamming AA,55=8"
  assert ((Radix.UInt8.hammingDistance ⟨0xFF⟩ ⟨0xFF⟩).toNat == 0) "hamming same=0"
  assert ((Radix.UInt8.hammingDistance ⟨0⟩ ⟨0⟩).toNat == 0) "hamming 0,0=0"
  assert ((Radix.UInt8.hammingDistance ⟨0x01⟩ ⟨0x00⟩).toNat == 1) "hamming 01,00=1"
  assert ((Radix.UInt8.hammingDistance ⟨0x0F⟩ ⟨0x00⟩).toNat == 4) "hamming 0F,00=4"

  -- ## Exhaustive boundary tests for extreme values

  -- Powers of 2
  for i in [:8] do
    let v : UInt8 := (1 <<< i.toUInt8)
    let rv : Radix.UInt8 := ⟨v⟩
    assert (Radix.UInt8.popcount rv == 1) s!"popcount 2^{i}=1"
    assert ((Radix.UInt8.ctz rv).toNat == i) s!"ctz 2^{i}={i}"

  -- Identity: a + 0 = a for special values
  for v in [0, 1, 2, 127, 128, 254, 255] do
    let a : Radix.UInt8 := ⟨v.toUInt8⟩
    assert (Radix.UInt8.wrappingAdd a ⟨0⟩ == a) s!"identity add {v}"
    assert (Radix.UInt8.wrappingMul a ⟨1⟩ == a) s!"identity mul {v}"
    assert ((Radix.UInt8.wrappingSub a a).toNat == 0) s!"self sub {v}"

  c.get
