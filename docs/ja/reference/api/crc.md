# CRC モジュール APIリファレンス

> **モジュール**: `Radix.CRC`
> **ソース**: `Radix/CRC/`

## 概要

リファレンス実装と最適化実装の両方を備えた CRC（巡回冗長検査）計算を提供します。CRC-32（ISO 3309 / ITU-T V.42）および CRC-16/CCITT バリアントを含みます。仕様層は CRC を GF(2) 上の多項式除算としてモデル化し、操作層は256エントリのテーブル駆動実装を提供します。ストリーミング API により、チャンク分割されたデータに対するインクリメンタル計算が可能です。

## 仕様 (`CRC.Spec`)

GF(2) 多項式演算に基づく数学モデル：

```lean
structure CRCParams where
  poly   : Nat        -- 生成多項式
  init   : Nat        -- 初期レジスタ値
  width  : Nat        -- ビット幅（16、32 など）

def crcCompute (params : CRCParams) (data : List UInt8) : Nat
```

仕様レベルの `crcCompute` はデータを GF(2) 上の多項式長除算としてビット単位で処理し、検証の基盤として機能します。

## 操作 — CRC-32 (`CRC.Ops`)

### 定数

```lean
def CRC32.poly : UInt32         -- 0xEDB88320（反転多項式）
def CRC32.initVal : UInt32      -- 0xFFFFFFFF
```

### ルックアップテーブル

```lean
def CRC32.table : Array UInt32   -- 256エントリの事前計算テーブル
```

テーブルは初期化時に `CRC32.poly` から計算されます。各エントリ `table[i]` は単一バイト `i` の CRC を保持します。

### バイトレベル更新

```lean
def CRC32.updateByte (crc : UInt32) (byte : UInt8) : UInt32
```

単一バイト更新: `table[(crc XOR byte) AND 0xFF] XOR (crc >>> 8)`。

### ワンショット API

```lean
def CRC32.compute (data : ByteArray) : Radix.UInt32
```

入力全体の CRC-32 を一括計算します。`finalize (update init data)` と等価です。

### ストリーミング API

```lean
def CRC32.init : UInt32
def CRC32.update (crc : UInt32) (data : ByteArray) : UInt32
def CRC32.finalize (crc : UInt32) : Radix.UInt32
```

チャンク分割されたデータに対するインクリメンタル計算用：

```lean
-- 例: 2つのチャンクに対するストリーミング CRC
let crc := CRC32.init
let crc := CRC32.update crc chunk1
let crc := CRC32.update crc chunk2
let result := CRC32.finalize crc
```

### リファレンス実装

```lean
def CRC32.computeNaive (data : ByteArray) : Radix.UInt32
```

仕様に一致するビット単位のリファレンス実装。テストと検証に使用され、パフォーマンス目的ではありません。

## 操作 — CRC-16 (`CRC.Ops`)

CRC-16/CCITT に対する同一の API パターン：

```lean
def CRC16.poly : UInt16          -- 0x1021（CCITT 多項式）
def CRC16.initVal : UInt16       -- 0xFFFF
def CRC16.table : Array UInt16   -- 256エントリの事前計算テーブル
def CRC16.updateByte (crc : UInt16) (byte : UInt8) : UInt16
def CRC16.compute (data : ByteArray) : Radix.UInt16
def CRC16.init : UInt16
def CRC16.update (crc : UInt16) (data : ByteArray) : UInt16
def CRC16.finalize (crc : UInt16) : Radix.UInt16
def CRC16.computeNaive (data : ByteArray) : Radix.UInt16
```

## 証明 (`CRC.Lemmas`)

### テーブルの性質

- `CRC32.table.size = 256`
- `CRC16.table.size = 256`
- テーブルエントリはビット単位計算と一致

### ストリーミングの一貫性

- `CRC32.compute data = CRC32.finalize (CRC32.update CRC32.init data)`
- `CRC32.update crc (a ++ b) = CRC32.update (CRC32.update crc a) b`

### リファレンス等価性

- `CRC32.compute data = CRC32.computeNaive data`
- `CRC16.compute data = CRC16.computeNaive data`

### GF(2) 代数

- CRC 多項式モデルの線形性
- 仕様から操作への対応証明

## 使用例

```lean
-- ワンショット CRC-32
let data := ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F]   -- "Hello"
#eval CRC32.compute data

-- 2つのチャンクに対するストリーミング CRC-32
let crc := CRC32.init
let crc := CRC32.update crc (ByteArray.mk #[0x48, 0x65])     -- "He"
let crc := CRC32.update crc (ByteArray.mk #[0x6C, 0x6C, 0x6F]) -- "llo"
#eval CRC32.finalize crc    -- ワンショットと同一の結果

-- CRC-16/CCITT
let data := ByteArray.mk #[0x31, 0x32, 0x33, 0x34]           -- "1234"
#eval CRC16.compute data
```

## 関連ドキュメント

- [Binary](binary.md) — バイナリシリアライズとパース
- [Bytes](bytes.md) — バイトレベルのデータ処理
