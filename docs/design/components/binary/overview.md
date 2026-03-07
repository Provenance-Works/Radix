# Binary Module: Overview

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. モジュールの目的 (Purpose)

Binaryモジュールは、Radixライブラリにおいて、連続するメモリ領域やバイト列データに対する高レベルの直列化・非直列化（Serialization/Deserialization）操作、およびエンディアン（バイトオーダー）の安全な相互変換を提供します。
`Word` 型と `Memory` (または `ByteArray`) をやり取りし、ゼロコピーまたは最小コストでの構造体・通信パケットの操作基盤となります。

## 2. アーキテクチャ構成 (Architecture Structure)

Binaryモジュールは、以下のサブコンポーネントから構成されます。

### 2.1 トップレベル (Binary)
各種データ操作のユーティリティの統合ポイント。

- `Binary.Endian`: ネットワークバイトオーダー（ビッグエンディアン）や、ローカルマシンのバイトオーダー（リトルエンディアン等）の検証・変換、スワップ操作（`bswap`）の抽象化。
- `Binary.Codec`: Lean の構造体等に実装される直列化型クラス（Typeclass）。
- `Binary.View`: 型のキャストや、`Memory` モジュールの生バッファ領域を論理的なデータ構造（配列等）として「ゼロコピー・ビュー」として読み書きするための型安全なポインタ操作。

## 3. 依存関係 (Dependencies)

- **依存先**: `Word` (エンディアン変換対象としての整数値), `Memory` (読み書きバッファ領域の提供元)
- **依存元**: アプリケーション（Layer 1/Layer 2のネットワーク処理やファイル永続化ロジック）

## 4. 特記事項 (Key Characteristics)

- 本モジュールの機能は、可能であれば Cのコンパイラ組込み関数（例: `__builtin_bswap32`）に直接インラインされるよう実装およびFFI定義が行われます（NFR-002: Zero-cost C equivalents）。
- バースト読み出し時のアライメント違反などの「アーキテクチャ依存未定義動作 (Undefined Behaviors)」を防止するための抽象層を持ち、C側で安全な `memcpy` 等を用いたアクセスへのコンパイルを保証します。
