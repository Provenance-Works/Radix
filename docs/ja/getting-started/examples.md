# 使用例

> **対象読者**: ユーザー、開発者

以下の例は `examples/Main.lean` のランナーと `examples/` 配下の個別デモに基づいています。現在のツリーでは、13 個の組み込みウォークスルー、11 個のアプリケーション寄りデモ、そして v0.2.0 / v0.3.0 をまたぐ 10 個の機能デモに整理されています。

## Word 算術

```lean
open Radix

-- ラッピング: mod 2^n
let a := UInt32.wrappingAdd 4000000000 4000000000  -- 3705032704
let b := UInt8.wrappingMul 16 17                    -- 16

-- 飽和: 境界値にクランプ
let c := UInt8.saturatingAdd 255 1                  -- 255
let d := UInt8.saturatingSub 10 20                  -- 0

-- チェック付き: Option を返す
let e := UInt32.checkedMul 100000 100000            -- none (オーバーフロー)
let f := UInt32.checkedAdd 100 200                  -- some 300

-- オーバーフロー付き: 結果 + オーバーフローフラグ
let (g, ov) := UInt32.overflowingAdd 4000000000 4000000000
-- g = 3705032704, ov = true
```

## 符号付き整数

```lean
-- 2の補数、組み込みUInt型のラッピング
let x := Int32.fromInt (-42)
assert (x.toInt == -42)

-- 境界値
let minVal := Int8.fromInt (-128)
let maxVal := Int8.fromInt 127
assert (minVal.toInt == -128)
assert (maxVal.toInt == 127)

-- 符号付き比較（ゼロコスト、ヒープアロケーションなし）
assert (Int32.slt (Int32.fromInt (-1)) (Int32.fromInt 0) == true)
assert (Int32.sge (Int32.fromInt 0) (Int32.fromInt (-1)) == true)
```

## ビット演算

```lean
-- ブール代数
assert (UInt32.band 0xFF00 0x0FF0 == 0x0F00)
assert (UInt32.bor  0xFF00 0x0FF0 == 0xFFF0)
assert (UInt32.bxor 0xFF00 0x0FF0 == 0xF0F0)
assert (UInt32.bnot 0x00000000 == 0xFFFFFFFF)

-- シフト（count % bitWidth）
assert (UInt32.shl 1 31 == 0x80000000)  -- 論理左シフト
assert (UInt8.shrArith 0x80 1 == 0xC0)  -- 算術右シフト（符号保存）

-- ローテート
assert (UInt32.rotl 0x80000001 1 == 0x00000003)
assert (UInt32.rotr 0x80000001 1 == 0xC0000000)
```

## ビットスキャン

```lean
assert (UInt32.clz 1 == 31)           -- 先頭ゼロカウント
assert (UInt32.ctz 8 == 3)            -- 末尾ゼロカウント
assert (UInt32.popcount 0xFF == 8)    -- ポピュレーションカウント
assert (UInt8.bitReverse 0x80 == 0x01) -- ビットリバース
```

## ビットフィールド

```lean
-- 個別ビットのテスト、セット、クリア、トグル
assert (UInt32.testBit 5 0 == true)
assert (UInt32.testBit 5 1 == false)
assert (UInt32.setBit 0 3 == 8)
assert (UInt32.clearBit 0xFF 0 == 0xFE)
assert (UInt32.toggleBit 0xFF 0 == 0xFE)

-- ビットフィールドの抽出と挿入
-- extractBits value low high proof → 抽出されたフィールド
-- insertBits dest value low high proof → 変更されたdest
```

## ビット幅変換

```lean
-- ゼロ拡張（小→大、値を保存）
let a : UInt16 := UInt8.toUInt16 255   -- 255

-- トランケート（大→小、上位ビットを失う）
let b : UInt8 := UInt16.toUInt8 256    -- 0

-- 符号拡張（符号付き解釈を保存）
let c : Int32 := Int8.toInt32 (Int8.fromInt (-1))
assert (c.toInt == -1)

-- レジスタ内部の符号拡張（Wasm サポート）
let d := UInt32.signExtend8 0x000000FF   -- 0xFFFFFFFF
```

## バイトオーダー

```lean
-- バイトスワップ（退化: bswap(bswap(x)) = x、証明済み！）
assert (UInt32.bswap 0x12345678 == 0x78563412)

-- エンディアン変換（ラウンドトリップ証明済み！）
let be := UInt32.toBigEndian 0x12345678
let orig := UInt32.fromBigEndian be
assert (orig == 0x12345678)
```

## LEB128

```lean
-- 符号なしエンコード/デコード（ラウンドトリップ証明済み！）
let encoded := Binary.Leb128.encodeU32 624485
-- encoded = [0xE5, 0x8E, 0x26]

let decoded := Binary.Leb128.decodeU32 encoded 0
-- decoded = some (624485, 3)

-- 符号付き LEB128
let sEncoded := Binary.Leb128.encodeS32 (Int32.fromInt (-123456))
let sDecoded := Binary.Leb128.decodeS32 sEncoded 0
-- ラウンドトリップ: sDecoded = some (Int32.fromInt (-123456), _)

-- サイズ上限（証明済み！）
-- encodeU32 サイズ ≤ 5, encodeU64 サイズ ≤ 10
```

## バイナリフォーマット DSL

```lean
-- ネットワークパケットフォーマットの定義
def packetFormat : Binary.Format :=
  .seq (.uint16 .big)           -- 2バイトヘッダ（ビッグエンディアン）
      (.seq (.uint32 .little)   -- 4バイトペイロード（リトルエンディアン）
           (.padding 2))        -- 2バイトパディング

-- フィールドを ByteArray にシリアライズ
-- ByteArray をフィールドにパース
-- parse ∘ serialize = id  （証明済み！）
```

## メモリバッファ

```lean
-- ゼロ初期化バッファの作成
let buf := Memory.Buffer.zeros 64

-- Tier 2（チェック付き）: 範囲外で Option を返す
let val := buf.checkedReadU8 0    -- some 0
let bad := buf.checkedReadU8 100  -- none

-- ライトとリードバック
let buf2 := (buf.checkedWriteU8 0 42).get!
let read := buf2.checkedReadU8 0  -- some 42
```

## システム I/O

```lean
-- 自動リソース管理付きファイルのライトとリード
System.FD.withFile "test.bin" .write fun fd => do
  let _ ← System.IO.sysWrite fd (ByteArray.mk #[1, 2, 3])

-- 便利関数
let _ ← System.IO.writeFileBytes "out.bin" data
let bytes ← System.IO.readFileBytes "out.bin"
let exists ← System.IO.sysFileExists "out.bin"
```

## アライメントユーティリティ

```lean
open Radix.Alignment

#eval alignUp 1000 16         -- 1008
#eval alignDown 1023 16       -- 1008
#eval isPowerOfTwo 64         -- true
#eval alignUpPow2 12345 256   -- 12544
#eval alignmentOf UInt64      -- 8
```

## Bitmap / Bitset

```lean
open Radix.Bitmap

let bm := Bitmap.zeros 128 |>.set 0 |>.set 7 |>.set 42
#eval bm.popcount             -- 3
#eval bm.test 42              -- true
#eval bm.findFirstSet         -- some 0

let full := Bitmap.ones 8 |>.clear 5
#eval full.findFirstClear     -- some 5
```

## リングバッファ

```lean
open Radix.RingBuffer

let rb := RingBuf.new 8
let some rb := rb.push ⟨10⟩ | unreachable!
let some rb := rb.push ⟨20⟩ | unreachable!
let some (front, rb) := rb.pop | unreachable!

#eval front.toNat             -- 10
#eval rb.peek.map UInt8.toNat -- some 20
```

## CRC-32 / CRC-16

```lean
open Radix.CRC

#eval CRC32.compute "123456789".toUTF8   -- 0xCBF43926

let crc := CRC32.init
let crc := CRC32.update crc "1234".toUTF8
let crc := CRC32.update crc "56789".toUTF8
#eval CRC32.finalize crc                  -- compute と同じ結果
```

## メモリプール

```lean
open Radix.MemoryPool

let pool := BumpPool.new 1024
#eval pool.remaining
#eval (pool.alloc 64).map (fun (off, p) => (off, p.remaining))
```

## Numeric 型クラス

```lean
import Radix.Word.Numeric

open Radix

#eval isZero (α := UInt8) UInt8.minVal
#eval isMax (α := UInt16) UInt16.maxVal
#eval BitwiseOps.popcount (⟨0xDEADBEEF⟩ : UInt32).toNat
```

## 関連ドキュメント

- [クイックスタート](quickstart.md) — 最小限の入門ガイド
- [APIリファレンス](../reference/api/) — 完全なAPIドキュメント
- [English version](../../en/getting-started/examples.md) — 英語版
