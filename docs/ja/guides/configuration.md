# 構成ガイド

> **対象読者**: ユーザー、開発者

## Radix を依存関係として追加

プロジェクトの `lakefile.lean` に Radix を追加します：

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

依存関係を解決：

```bash
lake update
lake build
```

## Lean 4 ツールチェイン

Radix は `lean-toolchain` でツールチェインをピン留めしています：

```
leanprover/lean4:v4.29.0-rc4
```

プロジェクトのツールチェインは互換性がある必要があります。異なるバージョンを使用すると、Mathlib のビルドに失敗する場合があります。

> **警告:** `lakefile.lean` の Mathlib リビジョンも同時に更新しない限り、Radix の `lean-toolchain` を変更しないでください。

## パッケージオプション

Radix は `lakefile.lean` で以下の Lean オプションを設定しています：

| オプション | 値 | 効果 |
|--------|-------|--------|
| `autoImplicit` | `false` | 暗黙的引数の自動推論を無効にします。すべての暗黙的引数は明示的に宣言する必要があります。意図しない自由変数を防止します。 |

プロジェクトが Radix に依存する場合、同じオプションを使用する必要はありません。ただし、形式検証を行うプロジェクトでは `autoImplicit := false` を推奨します。

## ビルドターゲット

Radix は以下の Lake ターゲットを定義しています：

| ターゲット | コマンド | 説明 |
|--------|---------|-------------|
| `Radix`（デフォルト） | `lake build` | ライブラリのビルド |
| `test` | `lake build test && lake exe test` | ユニットテストと統合テスト |
| `proptest` | `lake build proptest && lake exe proptest` | プロパティベーステスト（500イテレーション、LCG PRNG） |
| `bench` | `lake build bench && lake exe bench` | パフォーマンスベンチマーク |
| `examples` | `lake build examples && lake exe examples` | アサーション付き使用例 |

## インポートの粒度

ライブラリ全体または個別モジュールをインポートできます：

```lean
-- すべてをインポート
import Radix

-- 個別モジュールをインポート
import Radix.Word       -- 整数型と算術
import Radix.Bit        -- ビット演算
import Radix.Bytes      -- エンディアンとバイトスライス
import Radix.Memory     -- バッファ、ポインタ、レイアウト
import Radix.Binary     -- フォーマットDSL、パーサー、シリアライザー、LEB128
import Radix.System     -- ファイル I/O、エラー処理
import Radix.Concurrency -- アトミック操作モデル
import Radix.BareMetal   -- ベアメタルサポートモデル
```

すべての定義は `Radix` 名前空間にあります。`open Radix` でプレフィックスなしにアクセスできます：

```lean
import Radix
open Radix

#eval UInt32.wrappingAdd 100 200  -- 300
```

## 依存関係

Radix は Mathlib に依存しています。Lake が自動的に解決します。初回ビルドでは Mathlib4 のダウンロードとコンパイルが必要で、かなりの時間がかかります。

| 依存関係 | 継承 | 用途 |
|------------|-----------|---------|
| **mathlib** | いいえ | `BitVec n`、代数構造、証明タクティク |
| **batteries** | はい（Mathlib経由） | 標準ライブラリ拡張 |
| **plausible** | はい（Mathlib経由） | プロパティベーステスト |
| **aesop** | はい（Mathlib経由） | 証明自動化タクティク |
| **Qq** | はい（Mathlib経由） | クォート式 |
| **proofwidgets** | はい（Mathlib経由） | インタラクティブ証明ウィジェット |

> **注記:** Mathlib は形式的に検証済みです。信頼コンピューティング基盤（TCB）を拡大し**ません**。

## ローカル開発

依存プロジェクトと並行して Radix を開発する場合、ローカルパス依存関係を使用します：

```lean
require radix from ".." / "radix"
```

Git フェッチを回避し、両プロジェクトを同時にイテレーションできます。

## 関連ドキュメント

- [インストール](../getting-started/installation.md) — 初回セットアップ
- [構成リファレンス](../reference/configuration.md) — 完全なオプションリファレンス
- [ビルド](../development/build.md) — ビルドシステムの詳細
