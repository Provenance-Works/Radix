# Binary Module: Interface

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. エンディアン操作 (Binary.Endian)

バイトオーダー変換操作。すべて純粋な数学的関数（Pure function）であり、IOモナドを必要としません。
可能な限り Lean の組み込み関数（もし存在すれば）を利用し、無ければ純粋なビットシフトによる合成と分解を利用します。

`lean
import Radix.Word

def bswap16 (x : UInt16) : UInt16
def bswap32 (x : UInt32) : UInt32
def bswap64 (x : UInt64) : UInt64

-- システムネイティブなバイトオーダーへの変換
def toLittleEndian32 (x : UInt32) : UInt32
def toBigEndian32 (x : UInt32) : UInt32
`

## 2. 直列化型クラス (Binary.Codec)

データのバイト境界への明示的変換。Rustの Borsh や zerocopy に類似した設計を志向します。

`lean
class Encodable (α : Type) where
  -- 要求される静的バイト長
  byteSize : UWord
  encode : α  Memory.Buffer  UWord  Memory.Buffer

class Decodable (α : Type) where
  decode : Memory.Buffer  (offset : UWord)  Except String α
`

## 3. 安全読み出し (Binary.View)

マルチバイト整数の読み出し。ByteArray の連続するバイトからシフトとOR演算で結合します。

`lean
-- メモリバッファから安全に32ビット整数を読み出す
def Buffer.readU32 (buf : Buffer) (offset : UWord) (h : offset.val.toNat + 4  buf.bytes.size) : UInt32
`
