# インストール

> **対象読者**: ユーザー

## 前提条件

- **Lean 4** v4.29.0-rc4 以降
- **Lake** ビルドシステム（Lean 4 に同梱）
- **Git** 依存関係の解決に必要

### Lean 4 のインストール

```bash
# elan（Lean バージョンマネージャー）をインストール
curl https://elan-init.trycloudflare.com/ -sSf | sh

# インストール確認
lean --version
lake --version
```

## Radix をプロジェクトに追加

### 方法1: Lake 依存関係（推奨）

`lakefile.lean` に Radix を依存関係として追加します：

```lean
import Lake
open Lake DSL

package myProject where
  leanOptions := #[⟨`autoImplicit, false⟩]

require radix from git
  "https://github.com/user/radix" @ "main"

@[default_target]
lean_lib MyLib where
  srcDir := "."
```

依存関係を取得してビルド：

```bash
lake update
lake build
```

### 方法2: ローカルパス依存関係

Radix のローカル開発を並行して行う場合：

```lean
require radix from ".." / "radix"
```

## インストールの確認

テストファイル `Test.lean` を作成します：

```lean
import Radix

open Radix

#eval UInt32.wrappingAdd 4000000000 4000000000
-- 期待値: 3705032704
```

実行：

```bash
lake env lean Test.lean
```

## ツールチェイン要件

Radix は `lean-toolchain` で Lean 4 ツールチェインをピン留めしています：

```
leanprover/lean4:v4.29.0-rc4
```

プロジェクトには互換性のあるツールチェインバージョンを使用してください。

## 依存関係

Radix は **Mathlib** （コミュニティ数学ライブラリ）に依存しています。Lake が自動的に解決します。初回ビルドでは Mathlib4 をダウンロードするため、時間がかかる場合があります。

| 依存関係 | バージョン | 用途 |
|------------|---------|---------|
| Mathlib | rev でピン留め | `BitVec n`、代数構造、証明タクティク |

> **注記:** Mathlib は形式的に検証済みです。信頼コンピューティング基盤（TCB）を拡大し**ません**。

## 関連ドキュメント

- [クイックスタート](quickstart.md) — 5分で動かす
- [構成](../guides/configuration.md) — 構成オプション
- [English version](../../en/getting-started/installation.md) — 英語版
