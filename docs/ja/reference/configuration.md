# 構成リファレンス

> **対象読者**: ユーザー、開発者

## lakefile.lean

Radix は Lake（Lean 4 のビルドシステム）を使用し、`lakefile.lean` で構成しています：

```lean
import Lake
open Lake DSL

package radix where
  leanOptions := #[
    ⟨`autoImplicit, false⟩  -- auto-implicit 引数を無効化
  ]

@[default_target]
lean_lib Radix where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "<pinned-rev>"
```

### パッケージオプション

| オプション | 値 | 説明 |
|--------|-------|-------------|
| `autoImplicit` | `false` | すべての暗黙的引数は明示的に宣言する必要があります。意図しない自由変数を防止します。 |

### ビルドターゲット

| ターゲット | 型 | ルートモジュール | 説明 |
|--------|------|-------------|-------------|
| `Radix` | ライブラリ | `Radix` | メインライブラリ（デフォルトターゲット） |
| `test` | 実行可能 | `tests.Main` | ユニットテストと統合テスト |
| `proptest` | 実行可能 | `tests.PropertyTests` | プロパティベーステスト（500イテレーション、LCG PRNG） |
| `bench` | 実行可能 | `benchmarks.Main` | パフォーマンスベンチマーク |
| `examples` | 実行可能 | `examples.Main` | 使用例 |

### ターゲットの実行

```bash
lake build              # ライブラリのビルド
lake build test         # テストのビルド
lake exe test           # テストの実行
lake exe proptest       # プロパティベーステストの実行
lake exe bench          # ベンチマークの実行
lake exe examples       # 使用例の実行
```

## lean-toolchain

Lean 4 バージョンをピン留め：

```
leanprover/lean4:v4.29.0-rc4
```

> **警告:** これを変更すると、ピン留めされた Mathlib バージョンとの互換性が壊れる可能性があります。

## 依存関係

| 依存関係 | ソース | 継承 | 用途 |
|------------|--------|-----------|---------|
| **mathlib** | `leanprover-community/mathlib4` | いいえ | `BitVec`、代数、タクティク |
| **batteries** | `leanprover-community/batteries` | はい（Mathlib経由） | 標準ライブラリ拡張 |
| **plausible** | `leanprover-community/plausible` | はい（Mathlib経由） | プロパティベーステスト |
| **aesop** | `leanprover-community/aesop` | はい（Mathlib経由） | 証明自動化タクティク |
| **Qq** | `leanprover-community/quote4` | はい（Mathlib経由） | クォート式 |
| **proofwidgets** | `leanprover-community/ProofWidgets4` | はい（Mathlib経由） | インタラクティブ証明ウィジェット |

## 関連ドキュメント

- [インストール](../getting-started/installation.md) — セットアップ手順
- [ビルド](../development/build.md) — ビルドシステムの詳細
- [English version](../../en/reference/configuration.md) — 英語版
