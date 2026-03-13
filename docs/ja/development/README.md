# 開発

> **対象読者**: コントリビューター

Radixに貢献する開発者のためのガイド。

| ドキュメント | 説明 |
|----------|-------------|
| [セットアップ](setup.md) | 開発環境のセットアップ |
| [ビルド](build.md) | ビルドシステムとターゲット |
| [テスト](testing.md) | テスト戦略と実行方法 |
| [プロジェクト構造](project-structure.md) | 注釈付きコードベースレイアウト |

## コントリビューター向けクイックスタート

```bash
# クローン
git clone <repo-url> radix
cd radix

# ビルド
lake update
lake build

# テスト
lake exe test
lake exe proptest

# 使用例
lake exe examples
```

## 関連ドキュメント

- [アーキテクチャ](../architecture/) — システム設計
- [設計](../design/) — 設計原則と決定事項
- [English Version](../../en/development/) — 英語版
