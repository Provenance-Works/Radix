# Word Module: Behavior Specification

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. ゼロコスト抽象化の振る舞い (Zero-Cost Execution Behavior)

本モジュールの Layer 2 実装は、実行時に Lean 4 のビルトイン `UInt*` インターフェースや演算子 (`+`, `-`, `*`) に直接インライン化されるよう設計されています。

### 1.1 `inline` および `simp` アトリビュート
すべての Tier 2 ラッパー関数は `@[inline]` または `@[simp]` 指定を受けることで、Cバックエンド側のインライン展開を保証します。

```lean
@[inline]
def wrappingAdd (x y : UInt32) : UInt32 :=
  -- バックエンドによって C言語の `x + y` (uint32_t) にコンパイルされる
  ⟨x.val + y.val⟩
```

## 2. パニックの排除と Inhabited 回避 (Panic Safety & Inhabited Fallback Avoidance)

Lean 4 コンパイラによるパニック実装は、内部的な型の `Inhabited` デフォルト値（例: `0`）を返すため、Cなどのシステムレベルで予期しない論理破壊を引き起こす可能性があります（NFR-004）。

### 2.1 ゼロ除算の保証
`x / y` (ビルトイン) はパニックを伴わず `y = 0` なら `0` を返しますが、この動作は明示された API によってのみ露出しなければなりません。

- **Tier 1 (証明つき)**: `y ≠ 0` の証明 `h` が要求されるため、システムにおいて数学的に安全です。
- **Tier 2 (Checked)**: 実行時に `if y = 0 then none else some ⟨x.val / y.val⟩` を評価し、オプション型で安全性を確保します。

### 2.2 サチュレーティング演算 (Saturating)
オーバーフローまたはアンダーフローが発生した場合、パニックせず、その型の最大値または最小値にクランプします。
- 例: `UInt8` での `saturatingAdd 255 1` の結果は `255` となります。

## 3. 型変数のプラットフォーム対応 (Platform Size Dynamics)

`UWord` と `IWord` は、32ビット環境か64ビット環境かを示す型クラス `PlatformWidth n` によりパラメータ化されます。

- **コンパイル時の解決**: コンパイルパイプラインは `UWord 32` や `UWord 64` を解釈し、最終的に `size_t` などのネイティブのポインタワードサイズの型として C 言語のコードを出力します。
- **Lean 側でのサイズ検知の禁止**: ビルド時のマクロ等による `System.Platform.numBits` への依存は禁止されています。クロスコンパイル時にはターゲット基盤に委ねられなければなりません。

## 4. 依存性と定理証明 (Proofs and Automation)

`Word.Lemmas` 内のすべての定理は、`BitVec` (Layer 3 仕様レイヤー) の持つ定理ベースへとマッピングされます。これにより、ビットベクトル算術としての代数的性質を全て活用できます。

- 可換性、結合性などの証明は `simp` ルールとして追加され、Proof-Carrying API の引数として柔軟に証明項目 (`h`) を構成支援します。
