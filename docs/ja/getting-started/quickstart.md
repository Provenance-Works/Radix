# クイックスタート

> **対象読者**: ユーザー

5分以内で Radix を動かしましょう。

## 1. Radix をインポート

```lean
import Radix
open Radix
```

## 2. 整数算術

```lean
-- ラッピング算術（mod 2^n）
#eval UInt32.wrappingAdd 4000000000 4000000000  -- 3705032704

-- 飽和算術（境界値にクランプ）
#eval UInt8.saturatingAdd 200 100  -- 255

-- チェック付き算術（Option を返す）
#eval UInt8.checkedAdd 200 100     -- none
#eval UInt8.checkedAdd 100 50      -- some 150

-- オーバーフロー付き算術（結果 + フラグ）
#eval UInt8.overflowingAdd 200 100 -- (44, true)
```

## 3. 符号付き整数

```lean
-- 2の補数による符号付き型
#eval Int8.fromInt (-42)        -- -42
#eval Int32.toInt (Int32.fromInt (-1))  -- -1

-- 符号付き比較（ゼロコスト、Int アロケーションなし）
#eval Int32.slt (Int32.fromInt (-1)) (Int32.fromInt 0)  -- true
```

## 4. ビット演算

```lean
-- AND, OR, XOR, NOT
#eval UInt8.band 0xAA 0x0F      -- 0x0A
#eval UInt8.bor  0xA0 0x0F      -- 0xAF
#eval UInt8.bnot 0x00            -- 0xFF

-- シフトとローテート（count % bitWidth セマンティクス）
#eval UInt32.shl 1 10            -- 1024
#eval UInt8.rotl 0x81 1          -- 0x03

-- ビットスキャン
#eval UInt32.clz 1               -- 31
#eval UInt32.popcount 0xFF       -- 8
```

## 5. バイトオーダー

```lean
-- エンディアン変換
#eval UInt32.bswap 0x12345678           -- 0x78563412
#eval UInt32.toBigEndian 0x12345678     -- （プラットフォーム依存）

-- ラウンドトリップ
-- fromBigEndian (toBigEndian x) = x  （証明済み！）
```

## 6. LEB128

```lean
-- 可変長整数エンコーディング（WebAssembly、DWARF、protobuf で使用）
#eval Binary.Leb128.encodeU32 624485  -- ByteArray [0xE5, 0x8E, 0x26]
-- ラウンドトリップは形式的に証明済み
```

## 7. バイナリフォーマット DSL

```lean
-- パケットフォーマットを定義
def myFormat : Binary.Format :=
  .seq (.uint16 .big) (.seq (.uint32 .little) (.padding 2))

-- 同じフォーマットでパースとシリアライズ
-- parse ∘ serialize = id  （証明済み！）
```

## 8. メモリバッファ

```lean
-- 検証済みメモリバッファの作成と使用
let buf := Memory.Buffer.zeros 64
-- Tier 1: 証明付きリード/ライト（ゼロコスト、コンパイル時に境界を証明）
-- Tier 2: チェック付きリード/ライト（範囲外で Option を返す）
```

## 9. アライメント

```lean
open Radix.Alignment

#eval alignUp 1000 16        -- 1008
#eval alignDown 1023 16      -- 1008
#eval isAligned 1024 64      -- true
#eval alignPadding 1000 16   -- 8
```

## 10. リングバッファとビットマップ

```lean
open Radix.RingBuffer
open Radix.Bitmap

let rb := RingBuf.new 4
let some rb := rb.push ⟨10⟩ | unreachable!
let some rb := rb.push ⟨20⟩ | unreachable!
#eval rb.peek.map UInt8.toNat        -- some 10

let bm := Bitmap.zeros 64 |>.set 0 |>.set 7
#eval bm.test 7                      -- true
#eval bm.popcount                    -- 2
```

## 11. CRC とメモリプール

```lean
open Radix.CRC
open Radix.MemoryPool

#eval CRC32.compute "123456789".toUTF8  -- 0xCBF43926

let pool := BumpPool.new 1024
#eval pool.remaining                          -- 1024
#eval (pool.alloc 64).map (fun (off, p) => (off, p.remaining))
```

## 12. Numeric 型クラス

```lean
import Radix
import Radix.Word.Numeric

open Radix

#eval isZero (α := UInt8) UInt8.minVal -- true
#eval isMax (α := UInt16) UInt16.maxVal -- true
#eval BitwiseOps.popcount (⟨0xFF⟩ : UInt8).toNat -- 8
```

## 13. システム I/O

```lean
-- 自動リソース管理付きファイル I/O
System.FD.withFile "output.bin" .write fun fd => do
  System.IO.sysWrite fd data
-- エラー時もファイルは自動的にクローズ
```

## 次のステップ

- [使用例](examples.md) — より詳細な使用例
- [APIリファレンス](../reference/api/) — 完全なAPIドキュメント
- [アーキテクチャ](../architecture/README.md) — 設計の理解

## 関連ドキュメント

- [English version](../../en/getting-started/quickstart.md) — 英語版
