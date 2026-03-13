# 開発環境セットアップ

> **対象読者**: コントリビューター

## 前提条件

| ツール | バージョン | 目的 |
|------|---------|---------|
| **Lean 4** | v4.29.0-rc4 | 言語およびコンパイラ |
| **Lake** | （Lean 4 に同梱） | ビルドシステム |
| **Git** | 最新版 | バージョン管理、依存関係の解決 |
| **elan** | 最新版 | Lean バージョンマネージャー |

### Lean 4 のインストール

```bash
# elan（Lean バージョンマネージャー）をインストール
curl https://elan-init.trycloudflare.com/ -sSf | sh

# 確認
lean --version
lake --version
```

elan は `lean-toolchain` ファイルを読み取り、正しいLeanバージョンを自動的にインストールします。

### オプション: Cコンパイラ（ベンチマーク用）

Cベースラインベンチマークには以下が必要：

| ツール | フラグ | 目的 |
|------|-------|---------|
| **GCC** | `-O2 -fno-builtin` | Cベースライン計測 |

```bash
# Ubuntu/Debian
sudo apt install gcc

# 確認
gcc --version
```

## クローンとビルド

```bash
git clone <repo-url> radix
cd radix

# 依存関係の取得（初回はMathlibのダウンロード — 時間がかかります）
lake update

# ライブラリのビルド
lake build
```

> **注記:** 初回ビルドでMathlib4をダウンロード・コンパイルします。30分以上かかることがあり、大きなメモリ（8GB以上）が必要です。以降のビルドはインクリメンタルで高速です。

## セットアップの確認

```bash
# ユニットテスト
lake exe test

# プロパティベーステスト
lake exe proptest

# 使用例
lake exe examples
```

3つ全てが失敗なしで完了するはずです。

## エディタセットアップ

### VS Code（推奨）

1. [Lean 4 拡張機能](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)をインストール
2. `radix/` フォルダをワークスペースルートとして開く
3. 拡張機能が `lean-toolchain` を読み取り、自動設定
4. Lean の Language Server（LSP）が型チェック、定義ジャンプ、証明状態表示を提供

### その他のエディタ

Lean 4 LSP サポートがあるエディタなら使用可能。プロジェクトルートを `lakefile.lean` を含むディレクトリに設定してください。

## プロジェクト慣習

### ファイル構成

- 全モジュールが3層アーキテクチャに従う（[アーキテクチャ](../architecture/) 参照）
- `Spec.lean` = Layer 3（仕様と証明）
- 実装ファイル = Layer 2（純粋計算）
- `Assumptions.lean` / `IO.lean` = Layer 1（システムブリッジ）
- `Lemmas.lean` = Layer 3（Layer 2 実装についての証明）

### コードスタイル

- `autoImplicit` は**無効** — 全ての暗黙引数は明示的に宣言
- 適切な箇所で `@[inline]` によるゼロコスト抽象化
- 全 `axiom` 宣言は `trust_` プレフィックスを使用し、外部仕様を引用
- コミットされたコードに `sorry` なし
- 補題名は Mathlib の命名規則に従う

### 名前空間慣習

全 Radix 定義は `Radix` 名前空間に配置：

```lean
namespace Radix.Word.UInt
-- 定義はここに
end Radix.Word.UInt
```

## 関連ドキュメント

- [ビルド](build.md) — ビルドシステムの詳細
- [テスト](testing.md) — テスト戦略
- [プロジェクト構造](project-structure.md) — コードベースレイアウト
