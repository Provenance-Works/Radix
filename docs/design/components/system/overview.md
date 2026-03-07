# System Module: Overview

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. モジュールの目的 (Purpose)

Systemモジュールは、Radixライブラリ内でオペレーティングシステム（OS）に直接依存する機能（ファイル入出力、システム時刻、その他のPOSIX準拠システムコールなど）の抽象化を提供します。
これらのシステムリソースは、Lean 4 の純粋なビルトイン IO （IO.FS 等）のラッパーとして提供されます。

## 2. アーキテクチャ構成 (Architecture Structure)

Systemモジュールは、以下のサブコンポーネントから構成されます。

### 2.1 トップレベル (System)
OS環境とのやり取りや、全体的なシステム状態（リソースの割り当て状況など）を表現します。

- `System.Environment`: プロセス環境変数、コマンドライン引数へのアクセス
- `System.Time`: 高精度な時刻取得機構。
- `System.Error`: OS固有のエラーコード（POSIX `errno` 等）の `UWord` または `UInt32` ラッパーと解釈ロジック。

### 2.2 システム抽象化 (System.Platform / System.Posix)
Lean 4 レベルから直接呼び出される、低レベルのOSインターフェース。

- Lean4標準の IO.FS などへのラッパー
- POSIX APIの直接呼び出し（FFI）は固く禁じられているため、標準ライブラリへと処理を委譲します。
- 外部リソース（ファイル記述子など）の所有権モデル（Owned / Borrowed / Shared）の宣言

## 3. 依存関係 (Dependencies)

- **依存先**: `Word` (エラーコード、ファイル記述子、メタデータ用の整数型として利用)

## 4. TCBの運用ルール (TCB Rules)

