# データフロー

> **対象読者**: 開発者、コントリビューター

## Layer 3 → Layer 2 → Layer 1 フロー

Radixのデータは3層アーキテクチャを通じて流れます。仕様（Layer 3）が正しさを定義し、実装（Layer 2）が計算を行い、ブリッジ（Layer 1）がOSに接続します。

```mermaid
sequenceDiagram
    participant User as ユーザーコード
    participant L2 as Layer 2（実装）
    participant L3 as Layer 3（仕様）
    participant L1 as Layer 1（ブリッジ）
    participant OS as OS / ランタイム

    User->>L2: wrappingAdd(x, y) 呼び出し
    L2->>L2: x.val + y.val を計算（インライン）
    L2-->>User: 結果を返す（ゼロコスト）

    Note over L3,L2: 証明: wrappingAdd は BitVec 仕様と一致

    User->>L1: sysRead(fd, count) 呼び出し
    L1->>OS: IO.FS.Handle.read(count)
    OS-->>L1: ByteArray
    L1->>L2: ByteSlice を構築（検証済み）
    L1-->>User: IO (Except SysError ByteArray)

    Note over L3,L1: 公理: trust_lean_io_faithful
```

## ファイル読み取りフロー（エンドツーエンド）

```mermaid
sequenceDiagram
    participant App as アプリケーション
    participant SIO as System.IO
    participant SFD as System.FD
    participant SErr as System.Error
    participant SSpec as System.Spec
    participant Lean4 as Lean 4 IO.FS

    App->>SFD: withFile "data.bin" .read
    SFD->>Lean4: IO.FS.Handle.mk
    Lean4-->>SFD: Handle
    SFD->>SFD: FD を作成（owned）
    SFD->>App: callback(fd)
    App->>SIO: sysRead fd 1024
    SIO->>Lean4: handle.read 1024
    Lean4-->>SIO: ByteArray（または IO.Error）
    alt 成功
        SIO-->>App: Except.ok bytes
    else 失敗
        SIO->>SErr: fromIOError error
        SErr-->>SIO: SysError
        SIO-->>App: Except.error sysError
    end
    App->>SFD: withFile が自動でクローズ
    SFD->>Lean4: handle.close
```

## バイナリ パース/シリアライズ ラウンドトリップ

```mermaid
sequenceDiagram
    participant App as アプリケーション
    participant Fmt as Binary.Format
    participant Ser as Binary.Serial
    participant Par as Binary.Parser
    participant Buf as Memory.Buffer

    App->>Fmt: フォーマット定義（u16be, u32le, pad 2）
    App->>Ser: serializeFormat format values
    Ser->>Buf: エンディアン付きフィールド書き込み
    Buf-->>Ser: ByteArray
    Ser-->>App: ByteArray（シリアライズ済み）

    App->>Par: parseFormatExact data format
    Par->>Buf: エンディアン付きフィールド読み取り
    Buf-->>Par: FieldValues
    Par-->>App: List FieldValue（パース済み）

    Note over Ser,Par: exact parse は余剰バイトを拒否し、prefix parse は parsePrefix を使う
```

## LEB128 エンコード/デコードフロー

```mermaid
flowchart LR
    subgraph エンコード
        V["UInt32 値"] --> E1["下位7ビットを抽出"]
        E1 --> E2{"value >= 128?"}
        E2 -->|Yes| E3["継続ビットをセット<br/>バイトをプッシュ<br/>value /= 128"]
        E3 --> E1
        E2 -->|No| E4["最終バイトをプッシュ"]
    end
    subgraph デコード
        D1["バイトを読む"] --> D2["7データビットを抽出"]
        D2 --> D3["シフト位置に蓄積"]
        D3 --> D4{"継続ビット?"}
        D4 -->|Yes| D5["shift += 7"]
        D5 --> D1
        D4 -->|No| D6["値を返す"]
    end
    E4 --> |"ByteArray"| D1
```

## 算術モード選択

```mermaid
flowchart TD
    Start["整数演算"] --> Q1{"オーバーフロー証明<br/>を持っている？"}
    Q1 -->|Yes| T1["Tier 1: 証明付き<br/>addChecked(x, y, h)"]
    Q1 -->|No| Q2{"正確な結果が必要？"}
    Q2 -->|Yes| Checked["checkedAdd(x, y)<br/>Option を返す"]
    Q2 -->|No| Q3{"オーバーフロー<br/>フラグが必要？"}
    Q3 -->|Yes| Overflowing["overflowingAdd(x, y)<br/>(結果, フラグ) を返す"]
    Q3 -->|No| Q4{"クランプを許容？"}
    Q4 -->|Yes| Saturating["saturatingAdd(x, y)<br/>境界にクランプ"]
    Q4 -->|No| Wrapping["wrappingAdd(x, y)<br/>mod 2^n でラップ"]
```

## リングバッファの push/pop フロー

```mermaid
sequenceDiagram
    participant App as アプリケーション
    participant RB as RingBuffer.Impl
    participant Mem as Memory.Buffer
    participant Spec as RingBuffer.Spec

    App->>RB: push(rb, byte)
    alt count < capacity
        RB->>Mem: writeU8 tail byte
        Mem-->>RB: 更新済みバッファ
        RB->>RB: tail := wrapSuccFast tail capacity
        RB->>RB: count := count + 1
        RB-->>App: some 更新済み RingBuf
    else full
        RB-->>App: none
    end

    App->>RB: pop(rb)
    alt count > 0
        RB->>Mem: readU8 head
        Mem-->>RB: byte
        RB->>RB: head := wrapSuccFast head capacity
        RB->>RB: count := count - 1
        RB-->>App: some (byte, 更新済み RingBuf)
    else empty
        RB-->>App: none
    end

    Note over Spec,RB: FIFO 順序と容量不変条件は証明で維持される
```

## CRC ストリーミングフロー

```mermaid
sequenceDiagram
    participant App as アプリケーション
    participant Ops as CRC.Ops
    participant Table as ルックアップテーブル
    participant Spec as CRC.Spec

    App->>Ops: init
    Ops-->>App: 実行中 CRC レジスタ
    App->>Ops: update(crc, chunk1)
    Ops->>Table: 各バイトに updateByte
    Table-->>Ops: 事前計算済み剰余エントリ
    Ops-->>App: crc1
    App->>Ops: update(crc1, chunk2)
    Ops->>Table: 各バイトに updateByte
    Table-->>Ops: 事前計算済み剰余エントリ
    Ops-->>App: crc2
    App->>Ops: finalize(crc2)
    Ops-->>App: 最終 CRC-32 / CRC-16

    Note over Spec,Ops: update(init, a ++ b) = update(update(init, a), b) が補題で保証される
```

## 関連ドキュメント

- [アーキテクチャ概要](README.md) — 3層モデル
- [コンポーネント](components.md) — モジュール詳細
- [モジュール依存関係](module-dependency.md) — 依存関係グラフ
