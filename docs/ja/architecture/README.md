# アーキテクチャ概要

> **対象読者**: 開発者、アーキテクト、コントリビューター

## システムコンテキスト

Radixは、Lean 4向けの形式検証済み低レベルシステムプログラミングライブラリです。C言語と同等の機能 — 固定幅整数、ビット演算、バイトオーダー変換、メモリ抽象化、バイナリフォーマットDSL、システムI/O、並行処理モデル、ベアメタルサポート — を、Mathlibグレードの形式証明とともに提供します。

```mermaid
graph TD
    UserCode["ユーザーコード<br/>(Lean 4 アプリケーション)"] -->|"imports"| Radix["Radix ライブラリ"]
    Radix -->|"依存"| Mathlib["Mathlib<br/>(BitVec, 代数的構造)"]
    Radix -->|"Layer 1 がラップ"| Lean4IO["Lean 4 ランタイム<br/>(IO.FS, IO.Process)"]
    Lean4IO -->|"委譲"| OS["オペレーティングシステム<br/>(POSIX / Linux)"]
    style Radix fill:#4CAF50,color:white
    style Mathlib fill:#2196F3,color:white
    style Lean4IO fill:#FF9800,color:white
    style OS fill:#9E9E9E,color:white
```

## 3層アーキテクチャ

Radixは、seL4、CertiKOS、F*/Low*に着想を得た3層アーキテクチャを採用しています：

```mermaid
graph TD
    subgraph "Layer 3: 検証済み仕様"
        L3["純粋な数学的定義と定理。<br/>実行可能コードなし — 仕様と証明のみ。<br/><i>「正しい振る舞いとは何か？」</i>"]
    end
    subgraph "Layer 2: 検証済み実装"
        L2["Layer 3 の仕様を満たすことが証明された<br/>純粋な Lean 4 実装。<br/>正しさの証明が付いた計算可能な関数。<br/><i>「証明済みの正しい実装」</i>"]
    end
    subgraph "Layer 1: システムブリッジ"
        L1["Lean 4 組み込み IO API のラッパー。<br/>名前付き信頼仮定（axiom 宣言）を含む。<br/><i>「最小限の信頼境界」</i>"]
    end
    subgraph "ハードウェア / OS"
        HW["Lean 4 ランタイム経由の OS"]
    end
    L3 --- L2
    L2 --- L1
    L1 --- HW
    style L3 fill:#4CAF50,color:white
    style L2 fill:#2196F3,color:white
    style L1 fill:#FF9800,color:white
    style HW fill:#9E9E9E,color:white
```

### レイヤー間の規則

1. Layer 3（仕様）は Layer 2 や Layer 1 を**インポートしてはならない**
2. Layer 2（実装）は Layer 3 を**インポートしなければならない**（仕様への適合を証明するため）
3. Layer 2（実装）は Layer 1 を**インポートしてはならない**（純粋計算、IOなし）
4. Layer 1（ブリッジ）は Layer 3 を**インポートしなければならない**（どの仕様を実装するか明示するため）
5. Layer 1（ブリッジ）は Layer 2 を**インポートしてもよい**（検証済み純粋ロジックの再利用）

### 各モジュールのレイヤーマッピング

| モジュール | Layer 3（仕様） | Layer 2（実装） | Layer 1（ブリッジ） |
|--------|---------------|----------------|-----------------|
| Word | `Word.Spec` | `Word.UInt`, `Word.Int`, `Word.Arith`, `Word.Conv`, `Word.Size` | — |
| Bit | `Bit.Spec` | `Bit.Ops`, `Bit.Scan`, `Bit.Field` | — |
| Bytes | `Bytes.Spec` | `Bytes.Order`, `Bytes.Slice` | — |
| Memory | `Memory.Spec` | `Memory.Model`, `Memory.Ptr`, `Memory.Layout` | — |
| Binary | `Binary.Spec`, `Leb128.Spec` | `Binary.Format`, `Binary.Parser`, `Binary.Serial`, `Leb128` | — |
| System | `System.Spec` | `System.Error`, `System.FD` | `System.IO`, `System.Assumptions` |
| Concurrency | `Concurrency.Spec` | `Concurrency.Ordering`, `Concurrency.Atomic` | `Concurrency.Assumptions` |
| BareMetal | `BareMetal.Spec` | `BareMetal.GCFree`, `BareMetal.Linker`, `BareMetal.Startup` | `BareMetal.Assumptions` |

> **注記:** Word から Binary は**純粋**モジュール（Layer 2-3 のみ）です。System、Concurrency、BareMetal は Layer 1 コンポーネントを持ちます。

## モジュール依存関係グラフ

```mermaid
graph TD
    Bit["Bit<br/>(ビット演算)"] --> Word["Word<br/>(固定幅整数)"]
    Bytes["Bytes<br/>(バイトオーダー)"] --> Word
    Bytes --> Bit
    Memory["Memory<br/>(抽象メモリ)"] --> Word
    Memory --> Bytes
    Binary["Binary<br/>(フォーマットDSL)"] --> Word
    Binary --> Memory
    Binary --> Bit
    Binary --> Bytes
    System["System<br/>(OSインターフェース)"] --> Word
    System --> Bytes
    System --> Memory
    Concurrency["Concurrency<br/>(アトミック操作)"] -.->|"モデルのみ"| Word
    BareMetal["BareMetal<br/>(OS無しサポート)"] -.->|"モデルのみ"| Memory
    style Word fill:#4CAF50,color:white
    style Bit fill:#4CAF50,color:white
    style Bytes fill:#2196F3,color:white
    style Memory fill:#2196F3,color:white
    style Binary fill:#2196F3,color:white
    style System fill:#FF9800,color:white
    style Concurrency fill:#9C27B0,color:white
    style BareMetal fill:#9C27B0,color:white
```

依存関係は `Word` から上方向に流れます。各上位モジュールは下位モジュール上に構築されます。

## 信頼計算基盤（TCB）

TCBは、正しさが**証明されるのではなく仮定される**コンポーネントの集合です：

| コンポーネント | 状態 |
|-----------|--------|
| Lean 4 コンパイラおよびランタイム | プラットフォームとして受容 |
| Lean 4 組み込み IO 実装 | 名前付き公理で信頼 |
| Lean 4 デフォルト公理（`propext`, `Quot.sound`, `Classical.choice`） | 標準 |
| `System.Assumptions` の `trust_*` 公理 | リリース毎に監査 |
| `Concurrency.Assumptions` の `trust_*` 公理 | リリース毎に監査 |
| `BareMetal.Assumptions` の `trust_*` 公理 | リリース毎に監査 |

**TCBに明示的に含まれないもの：**
- Mathlib（形式検証済み）
- Radix Layer 2-3（証明済み）
- Radix Layer 1 の Lean 4 コード（検証済み。TCBに含まれるのは*IO動作についての仮定*のみ）

## 主要な設計判断

| 判断 | 概要 | ADR |
|----------|---------|-----|
| 3層アーキテクチャ | 検証済みコードの最大化、信頼コードの最小化 | [ADR-001](../design/adr.md) |
| Mathlib BitVec の採用 | `BitVec n` を仕様レベルの正準表現として使用 | [ADR-002](../design/adr.md) |
| 2の補数による符号付き整数 | 符号なし型をラップし、MSBを符号として解釈 | [ADR-003](../design/adr.md) |

## 関連ドキュメント

- [コンポーネント](components.md) — 詳細なコンポーネント分析
- [モジュール依存関係](module-dependency.md) — 完全な依存関係グラフ
- [データモデル](data-model.md) — コアデータ構造
- [データフロー](data-flow.md) — システム内のデータフロー
- [設計原則](../design/principles.md) — 設計哲学
