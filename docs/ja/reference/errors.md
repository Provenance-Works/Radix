# エラーリファレンス

> **対象読者**: すべてのユーザー

## システムエラー (`Radix.System.Error.SysError`)

Radix は OS レベルのエラーを `SysError` 帰納型（11バリアント）でモデル化しています。これらは `SysError.fromIOError` を通じて Lean 4 の `IO.Error` からマッピングされます。

| バリアント | パラメータ | 説明 | 一般的な原因 |
|---------|-----------|-------------|---------------|
| `permissionDenied` | `msg : String` | OS によりアクセス拒否 | ファイル権限、読み取り専用ファイルシステム |
| `notFound` | `msg : String` | リソースが存在しない | ファイルが見つからない、無効なパス |
| `alreadyExists` | `msg : String` | リソースが既に存在する | 既存ファイルの作成 |
| `resourceBusy` | `msg : String` | リソースが使用中 | ロックされたファイル、ビジーなデバイス |
| `invalidArgument` | `msg : String` | 無効なパラメータ | 負のオフセット、空のパス |
| `noSpace` | `msg : String` | デバイスに空き容量がない | ディスクフル |
| `ioError` | `msg : String` | 一般的な I/O 障害 | ハードウェアエラー、ネットワーク障害 |
| `interrupted` | `msg : String` | 操作が中断された | シグナル受信 |
| `endOfFile` | (なし) | ファイル終端に到達 | ファイル末尾を超えた読み取り |
| `invalidState` | `msg : String` | 無効なリソース状態 | クローズされたファイルへの操作 |
| `unsupported` | `msg : String` | 純粋バックエンドで操作がサポートされていない | 負の SEEK_CUR、FFI を必要とする機能 |

### エラー処理パターン

すべての `System.IO` 関数は `IO (Except SysError α)` を返します：

```lean
-- パターン: 明示的なエラー処理
let result ← System.IO.sysRead fd 1024
match result with
| .ok bytes => -- bytes を処理
| .error e  => -- SysError を処理
```

### Lean 4 IO.Error からのマッピング

`SysError.fromIOError` はすべての `IO.Error` コンストラクタからの完全なマッピングを提供します。カバレッジは Lean 4 が公開する範囲に限定されます — 生の POSIX `errno` 値は直接アクセスできません。

## バイナリパースエラー (`Radix.Binary.Parser.ParseError`)

| バリアント | 説明 |
|---------|-------------|
| `outOfBounds` | 入力 ByteArray の範囲外を読み取ろうとした |
| `internal` | パーサー内部の不整合 |

## バイナリシリアライゼーションエラー (`Radix.Binary.Serial.SerialError`)

| バリアント | 説明 |
|---------|-------------|
| `missingField` | 必須フィールドが提供されていない |
| `typeMismatch` | フィールド値の型がフォーマットと一致しない |

## LEB128 デコード失敗

LEB128 デコード関数は `Option` を返します — `none` は以下を示します：
- 入力の切り詰め（最終バイトの前にバイトが終了）
- 冗長なエンコーディング（最大を超えるバイト数: U32 で5、U64 で10）
- オーバーフロー（デコードされた値が型の範囲を超過）

## 関連ドキュメント

- [用語集](glossary.md) — 用語定義
- [トラブルシューティング](../guides/troubleshooting.md) — よくある問題
- [English version](../../en/reference/errors.md) — 英語版
