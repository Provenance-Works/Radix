# Memory Module: Behavior Specification

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. ネイティブGCへの完全な迎合 (Safe Memory Lifecycle)

### 1.1 ガベージコレクションによるライフタイム管理
FFIや手動管理ポインタ（Cの struct による Opaque クラスなど）を介した外的なアロケーションは一切行いません（ADR C-001の制約に基づく）。
すべてのバッファ（ByteArray等）の確保、参照カウント、および解放は、完全に Lean 4 のネイティブな実行時ガベージコレクションによって自動的かつ安全に行われます。これにより、Use-After-Free (UAF) や Memory Leak が原理上発生しないことが保証されます。

## 2. 境界チェックの排除と証明の推論 (Zero-Cost Memory Operations)

Tier 1 API の呼び出し（例：offset < buf.bytes.size の証明 h を要するもの）は、Cのコンパイルレベルにおいて、Leanコンパイラが備える「境界チェック削除（Bounds Check Elimination）」によってインライン展開されるべきです。

### 2.1 範囲チェックのコンパイル時解決
証明 h を満たした呼び出しでは、実行時の境界アサートを含めず、Leanの証明器によるコンパイル時保証に依存します（NFR-002: Zero-cost Abstraction への準拠）。

### 2.2 Proof Erasing (実行時の証明削除)
API定義に渡された証明オブジェクト h は、Lean4 のコンパイル時イレース機構によりバイトコードや C 実行形式の生成時点において無視され、実行性能へのオーバーヘッドは全く与えません。
