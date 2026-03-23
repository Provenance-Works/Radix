# コンポーネントアーキテクチャ

> **対象読者**: 開発者、コントリビューター

## コンポーネント概要

Radix は 18 個のトップレベルモジュールを公開しており、それぞれがシステムプログラミングのプリミティブを提供します。17 個の実行時・モデルモジュールは 3 層アーキテクチャ（仕様 → 実装 → ブリッジ）に従い、`ProofAutomation` は再利用可能なタクティクマクロを提供するメタレベル補助モジュールです。v0.3.0 では v0.2.0 の基盤に加えて、UTF-8 検証、誤り訂正、DMA 推論、タイマ補助、領域代数サポートが追加されました。

```mermaid
graph TD
    subgraph "コア純粋モジュール"
        Word["Word<br/>10整数型<br/>5算術モード + Numeric"]
        Bit["Bit<br/>ビット演算<br/>走査 + フィールド"]
        Bytes["Bytes<br/>バイトオーダー<br/>ByteSlice"]
        Memory["Memory<br/>抽象メモリ<br/>Buffer、Ptr、Layout、領域代数"]
        Binary["Binary<br/>フォーマットDSL<br/>パーサー、シリアライザー、LEB128"]
    end
    subgraph "v0.2.0 純粋モジュール"
        Alignment["Alignment<br/>アライメント計算<br/>2の冪高速パス"]
        RingBuffer["RingBuffer<br/>固定容量FIFO<br/>Bufferベース"]
        Bitmap["Bitmap<br/>高密度ビット集合<br/>ワード単位演算"]
        CRC["CRC<br/>CRC-32 / CRC-16<br/>ストリーミング API"]
        MemoryPool["MemoryPool<br/>bump + slab アロケータ<br/>純粋モデル"]
    end
    subgraph "v0.3.0 純粋モジュール"
        UTF8["UTF8<br/>Unicode スカラモデル<br/>エンコード + デコード"]
        ECC["ECC<br/>Hamming(7,4)<br/>シンドローム + 訂正"]
        DMA["DMA<br/>ディスクリプタモデル<br/>検査付きコピーシミュレータ"]
        Timer["Timer<br/>単調クロック<br/>デッドライン + 期限切れ"]
    end
    subgraph "ブリッジ / モデルモジュール"
        System["System<br/>OSインターフェース<br/>ファイルI/O、Error、FD"]
        Concurrency["Concurrency<br/>アトミック操作モデル<br/>C11メモリオーダリング"]
        BareMetal["BareMetal<br/>プラットフォームモデル<br/>リンカー、スタートアップ、GCFree"]
    end
    subgraph "メタレベル証明支援"
        ProofAutomation["ProofAutomation<br/>タクティクマクロ<br/>radix_decide + radix_omega + radix_simp + radix_finish"]
    end
    Bit --> Word
    Bytes --> Word
    Bytes --> Bit
    Memory --> Word
    Memory --> Bytes
    Binary --> Word
    Binary --> Memory
    Binary --> Bit
    Binary --> Bytes
    Alignment --> Word
    RingBuffer --> Memory
    Bitmap --> Word
    Bitmap --> Bit
    CRC --> Word
    CRC --> Bit
    MemoryPool --> Memory
    MemoryPool --> Word
    DMA --> Memory
    DMA -.-> Concurrency
    System --> Word
    System --> Bytes
    System --> Memory
    Concurrency -.-> Word
    BareMetal -.-> Memory
    style Word fill:#4CAF50,color:white
    style Bit fill:#66BB6A,color:white
    style Bytes fill:#42A5F5,color:white
    style Memory fill:#29B6F6,color:white
    style Binary fill:#26C6DA,color:white
    style Alignment fill:#66BB6A,color:white
    style RingBuffer fill:#29B6F6,color:white
    style Bitmap fill:#26C6DA,color:white
    style CRC fill:#26C6DA,color:white
    style MemoryPool fill:#29B6F6,color:white
    style UTF8 fill:#26A69A,color:white
    style ECC fill:#26A69A,color:white
    style DMA fill:#26A69A,color:white
    style Timer fill:#26A69A,color:white
    style System fill:#FFA726,color:white
    style Concurrency fill:#AB47BC,color:white
    style BareMetal fill:#8D6E63,color:white
    style ProofAutomation fill:#5C6BC0,color:white
```

## モジュール詳細

### Word — 固定幅整数型と算術

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Word.Spec` | 3 | `BitVec n` を用いた数学的仕様 |
| `Word.UInt` | 2 | Lean 4 組み込みをラップした `UInt8`, `UInt16`, `UInt32`, `UInt64` |
| `Word.Int` | 2 | 2の補数による `Int8`, `Int16`, `Int32`, `Int64` |
| `Word.Size` | 2 | `UWord`, `IWord` — プラットフォーム幅型（32/64パラメトリック） |
| `Word.Arith` | 2 | ラッピング、飽和、チェック付き、オーバーフロー付き算術 |
| `Word.Conv` | 2 | ビット幅変換、符号変換、符号拡張 |
| `Word.Lemmas.*` | 3 | 環、オーバーフロー、BitVec、変換の証明 |

**主要設計**: 型は Lean 4 組み込み `UIntN` をラップし、ゼロコスト抽象化を実現（NFR-002）。Layer 3 仕様は `BitVec n` を使用。等価性は `Word.Lemmas.BitVec` で証明済み。

### Bit — ビット演算

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Bit.Spec` | 3 | ビット演算の仕様 |
| `Bit.Ops` | 2 | AND、OR、XOR、NOT、シフト、回転 |
| `Bit.Scan` | 2 | `clz`、`ctz`、`popcount`、`bitReverse`、`hammingDistance` |
| `Bit.Field` | 2 | `testBit`、`setBit`、`clearBit`、`toggleBit`、`extractBits`、`insertBits` |
| `Bit.Lemmas` | 3 | ブール代数、ド・モルガン、シフト恒等式、フィールドのラウンドトリップ |

**主要設計**: 全シフト/回転操作は `count % bitWidth` でカウントを正規化（Rustセマンティクス、FR-002.1a）。

### Bytes — バイトオーダー操作

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Bytes.Spec` | 3 | エンディアンとバイトスワップの仕様 |
| `Bytes.Order` | 2 | `bswap`、`toBigEndian`/`fromBigEndian`、`toLittleEndian`/`fromLittleEndian` |
| `Bytes.Slice` | 2 | `ByteSlice` — 境界チェック付き `ByteArray` ビューとエンディアン対応読み取り |
| `Bytes.Lemmas` | 3 | `bswap` 退化、BE/LE ラウンドトリップ、符号付き型のラウンドトリップ |

### Memory — 抽象メモリモデル

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Memory.Spec` | 3 | 領域、アライメント、分離性、領域代数の定義 |
| `Memory.Model` | 2 | `Buffer` — 証明付き読み書きの `ByteArray` ベースメモリ |
| `Memory.Ptr` | 2 | `Ptr n` — バイト幅パラメトリックなポインタ抽象化 |
| `Memory.Layout` | 2 | `FieldDesc`、`LayoutDesc` — パックド構造体レイアウト計算 |
| `Memory.Lemmas` | 3 | バッファサイズ保存、領域分離性、アライメントの証明 |

### Binary — バイナリフォーマットDSL

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Binary.Spec` | 3 | `FormatSpec` と妥当性条件 |
| `Binary.Format` | 2 | `Format` 帰納型 — バイナリレイアウト記述用DSL |
| `Binary.Parser` | 2 | エンディアンサポート付きフォーマット駆動パーサー |
| `Binary.Serial` | 2 | フォーマット駆動シリアライザー |
| `Binary.Leb128` | 2 | LEB128 可変長整数エンコード/デコード |
| `Binary.Leb128.Spec` | 3 | LEB128 数学的仕様 |
| `Binary.Leb128.Lemmas` | 3 | ラウンドトリップ証明、サイズ上限 |
| `Binary.Lemmas` | 3 | フォーマット証明、パーサー/シリアライザーの性質 |

### System — システムコールインターフェース

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `System.Spec` | 3 | `FileState` 状態機械、事前/事後条件、`ReadSpec`/`WriteSpec` |
| `System.Error` | 2 | 10バリアントの `SysError` 帰納型、`fromIOError` マッピング |
| `System.FD` | 2 | `FD`（ファイルディスクリプタ）、`Ownership`、`OpenMode`、`withFile` ブラケット |
| `System.IO` | 1 | `sysRead`、`sysWrite`、`sysSeek`、ファイル便利関数 |
| `System.Assumptions` | 1 | POSIX.1-2024 を引用する `trust_*` 公理 |

### Concurrency — アトミック操作モデル

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Concurrency.Spec` | 3 | `MemoryOrder`、`MemoryEvent`、`happensBefore`、`isDataRace`、`isLinearizable` |
| `Concurrency.Ordering` | 2 | オーダリング強度比較、強化、結合 |
| `Concurrency.Atomic` | 2 | `AtomicCell`、アトミック load/store/CAS、フェッチ操作 |
| `Concurrency.Lemmas` | 3 | オーダリング強度の証明、DRF証明、線形化可能性 |
| `Concurrency.Assumptions` | 1 | `trust_atomic_word_access`、`trust_cas_atomicity` 等 |

### BareMetal — ベアメタルサポート

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `BareMetal.Spec` | 3 | `Platform`、`RegionKind`、`MemoryMap`、`StartupPhase`、`BootInvariant` |
| `BareMetal.GCFree` | 2 | `Lifetime`、`ForbiddenPattern`、`GCFreeConstraint`、スタック解析 |
| `BareMetal.Linker` | 2 | `LinkerScript`、`Section`、`Symbol`、アドレスアライメント |
| `BareMetal.Startup` | 2 | `StartupAction`、最小/完全スタートアップアクション、バリデーション |
| `BareMetal.Lemmas` | 3 | 領域分離性、メモリマップ、アライメント、スタートアップの証明 |
| `BareMetal.Assumptions` | 1 | `trust_reset_entry`、`trust_bss_zeroed` 等 |

### Alignment — アライメントユーティリティ

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Alignment.Spec` | 3 | 数学的なアライメント仕様と 2 の冪ルール |
| `Alignment.Ops` | 2 | `alignUp`、`alignDown`、`isAligned`、`alignPadding`、高速パス |
| `Alignment.Lemmas` | 3 | 挟み込み境界、ラウンドトリップ、仕様一致の証明 |

### RingBuffer — 固定容量リングキュー

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `RingBuffer.Spec` | 3 | FIFO キュー状態モデルと不変条件 |
| `RingBuffer.Impl` | 2 | `push`、`pop`、`peek`、`pushForce`、バッチ操作 |
| `RingBuffer.Lemmas` | 3 | 容量保存、FIFO 順序、不変条件保持の証明 |

### Bitmap — 高密度ビット配列

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Bitmap.Spec` | 3 | 抽象ビット集合モデルと末尾ワード不変条件 |
| `Bitmap.Ops` | 2 | ビット更新、集合演算、popcount、探索操作 |
| `Bitmap.Lemmas` | 3 | ブール代数性質と不変条件保持の証明 |

### CRC — チェックサムアルゴリズム

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `CRC.Spec` | 3 | CRC-32 / CRC-16 の GF(2) 多項式モデル |
| `CRC.Ops` | 2 | テーブル駆動 CRC 実装とストリーミング API |
| `CRC.Lemmas` | 3 | ストリーミング一貫性と代数的正しさの証明 |

### MemoryPool — アロケータモデル

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `MemoryPool.Spec` | 3 | Bump/slab アロケータ状態モデルと安全不変条件 |
| `MemoryPool.Model` | 2 | `Memory.Buffer` を用いる純粋アロケータモデル |
| `MemoryPool.Lemmas` | 3 | 容量追跡、リセット正しさ、二重解放防止の証明 |

### UTF8 — 検証済み UTF-8 モデル

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `UTF8.Spec` | 3 | Unicode スカラ妥当性と生バイト上の正準 UTF-8 セマンティクス |
| `UTF8.Ops` | 2 | スカラ構築、エンコード/デコード補助、well-formedness 判定 |
| `UTF8.Lemmas` | 3 | ラウンドトリップ、バイト数、正準 well-formedness の証明 |

### ECC — 誤り訂正プリミティブ

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `ECC.Spec` | 3 | Hamming(7,4) コード語構造、パリティ、シンドローム仕様 |
| `ECC.Ops` | 2 | バイト詰め込み、エンコード、訂正、デコード補助 |
| `ECC.Lemmas` | 3 | 1 ビット訂正と encode/decode 正しさの証明 |

### DMA — DMA 転送モデル

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `DMA.Spec` | 3 | コヒーレンス・アトミシティ契約付きの領域ベースディスクリプタ |
| `DMA.Ops` | 2 | ディスクリプタ検証、ステップ数計算、検査付きバイトコピーシミュレーション |
| `DMA.Lemmas` | 3 | 妥当性反映、ステップ数、シミュレータ正しさの補題 |

### Timer — 単調クロックモデル

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `Timer.Spec` | 3 | 論理クロック、デッドライン、経過/残時間、期限切れ述語 |
| `Timer.Ops` | 2 | tick 前進、デッドライン生成、真偽値期限切れ補助 |
| `Timer.Lemmas` | 3 | 単調性、経過時間、期限切れ、残時間の証明 |

### ProofAutomation — メタレベル証明支援

| サブモジュール | レイヤー | 説明 |
|-----------|-------|-------------|
| `ProofAutomation` | Meta | Radix の典型的な証明義務向け `radix_decide` / `radix_omega` / `radix_simp` / `radix_finish` タクティクマクロ |

## 関連ドキュメント

- [アーキテクチャ概要](README.md) — ハイレベルアーキテクチャ
- [モジュール依存関係](module-dependency.md) — 依存関係グラフ
- [データモデル](data-model.md) — コアデータ構造
- [APIリファレンス](../reference/api/) — モジュール別の詳細API
