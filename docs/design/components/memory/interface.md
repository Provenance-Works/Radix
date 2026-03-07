# Memory Module: Interface

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. メモリバッファの抽象化 (Memory.Buffer)

C の手法（mmap等）ではなく、Lean の安全なネイティブ ByteArray を基盤として構築されます。ByteArray 領域に対する証明付きのゼロコピーな読み書きを提供します。

`lean
import Radix.Word

structure Buffer where
  bytes : ByteArray

def Buffer.size (buf : Buffer) : Nat := buf.bytes.size

-- バイト配列からの安全な読み出し。
-- ここでは、副作用を伴う IO バインドを証明内に混入させず、純粋な命題としてサイズチェックを行います。
def Buffer.readU8 (buf : Buffer) (offset : UWord) (h : offset.val.toNat < buf.bytes.size) : UInt8 :=
  buf.bytes.get offset.val.toNat, h

def Buffer.writeU8 (buf : Buffer) (offset : UWord) (val : UInt8) (h : offset.val.toNat < buf.bytes.size) : Buffer :=
  { bytes := buf.bytes.set offset.val.toNat, h val }
`

### 2. API Definitions

### 2.1 Buffer Management

### 2.2 Tier 2: 境界チェック付き API (Checked Wrapper)
証明が不便なシステムプログラム箇所で使用。境界チェックを行い、範囲外なら Option.none を返します。

`lean
def Buffer.checkedReadU8 (buf : Buffer) (offset : UWord) : Option UInt8 :=
  if h : offset.val.toNat < buf.bytes.size then
    some (Buffer.readU8 buf offset h)
  else
    none
`
