# ECC モジュール APIリファレンス

> **モジュール**: `Radix.ECC`
> **ソース**: `Radix/ECC/`

## 概要

パリティと Hamming(7,4) 誤り訂正コードのためのコンパクトな代数モデルを提供します。軽量な単一ビット訂正が必要なストレージ、ファームウェアイメージ、転送エンコーディング向けです。

## 仕様 (`ECC.Spec`)

Hamming(7,4) codeword の数学モデルです。

```lean
abbrev Nibble := Fin 16

structure Codeword74 where
  p1 : Bool
  p2 : Bool
  d0 : Bool
  p4 : Bool
  d1 : Bool
  d2 : Bool
  d3 : Bool

def bitVal (b : Bool) : Nat
def xor3 (a b c : Bool) : Bool
def toNibble (c : Codeword74) : Nibble
def ofNibble (n : Nibble) : Codeword74
def syndrome (c : Codeword74) : Nat
def errorIndex? (c : Codeword74) : Option (Fin 7)
def flipAt (c : Codeword74) (idx : Fin 7) : Codeword74
def correct (c : Codeword74) : Codeword74
def evenParity (n width : Nat) : Bool
```

### 意味論

- `syndrome = 0` は受信語がすべてのパリティ式を満たすことを意味します。
- `correct` は Hamming syndrome が指す単一ビット誤りを修復します。
- `evenParity` は自然数の下位 `width` ビットに対するパリティを計算します。

### 訂正の境界

- 素の Hamming(7,4) が保証するのは clean word と単一ビット誤りの訂正までです。
- 多ビット破損では `correct` 後に別の valid codeword へ写ってしまうことがあるため、`correct` を汎用の完全性検査として扱ってはいけません。

## 操作 (`ECC.Ops`)

`UInt8` codeword 上の実行可能ヘルパーです。

```lean
abbrev Nibble := Spec.Nibble
abbrev Codeword74 := Spec.Codeword74

inductive Status where
  | clean
  | corrected (idx : Fin 7)

def toByte (c : Codeword74) : UInt8
def isCodewordByte (b : UInt8) : Bool
def fromByte? (b : UInt8) : Option Codeword74
def encodeNibble (n : Nibble) : UInt8
def encodeByte? (b : UInt8) : Option UInt8
def decode (b : UInt8) : Option UInt8
def syndrome (b : UInt8) : Option Nat
def errorIndex? (b : UInt8) : Option (Fin 7)
def check (b : UInt8) : Bool
def status? (b : UInt8) : Option Status
def correct (b : UInt8) : Option UInt8
def decodeAfterCorrect (b : UInt8) : Option UInt8
def evenParity (b : UInt8) (width : Nat := 8) : Bool
```

- `isCodewordByte` は Hamming(7,4) payload の外側にある高位ビット付きバイトを拒否します。
- `decode` は syndrome が 0 の low-7-bit 入力に対してのみ `some` を返し、パリティ不整合のある語は `correct` 後に decode する必要があります。
- `syndrome`、`errorIndex?`、`status?`、`correct` は checked API であり、不正な 8 ビット入力には `none` を返します。
- `status?` は clean word と単一ビット訂正対象を区別し、`decodeAfterCorrect` は repair 後 decode の代表経路を直接返します。
- `correct` はすべての多ビット誤りを検出できません。多ビット検出が必要な場合は外側に checksum か parity 層を追加してください。

## 証明 (`ECC.Lemmas`)

- `toNibble_ofNibble`: 仕様層で encode してから抽出すると元の nibble に戻る
- `toNibble_correct_single_bit`: どの 1 ビット誤りを訂正しても元の nibble を回復できる
- `errorIndex?_eq_none_iff_syndrome_zero`: clean codeword に correction index は存在しない
- `errorIndex?_flipAt_ofNibble`: 単一ビット破損は flipped bit として分類される
- `decode_encodeNibble`: 実行層の decode after encode が元の payload bit を返す
- `status?_encodeNibble` / `status?_single_bit`: 実行層の分類が clean / corrected を正しく表す
- `decode_correct_single_bit`: 実行層の correction が codeword の nibble を保存する
- `decodeAfterCorrect_single_bit`: どの単一ビット破損でも repair 後 decode に成功する

## 使用例

```lean
import Radix.ECC

def demo : Option UInt8 :=
  let nibble : Radix.ECC.Nibble := ⟨0xB, by decide⟩
  let encoded := Radix.ECC.encodeNibble nibble
  let corrupted := encoded ^^^ 0x04
  Radix.ECC.decodeAfterCorrect corrupted
```

## 関連ドキュメント

- [Bit](bit.md) — パリティ推論の土台になる低レベルビット操作
- [Bytes](bytes.md) — ECC payload を格納するバイト指向プリミティブ
