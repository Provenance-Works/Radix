# APIリファレンス

> **対象読者**: 開発者

現在の Radix サーフェス全体と v0.3.0 の composable 追加分を対象にしたモジュール別 API ドキュメントです。

## モジュール索引

| モジュール | 説明 | ソース |
|--------|-------------|--------|
| [Word](word.md) | 固定幅整数、算術モード、変換 | `Radix/Word/` |
| [Numeric](numeric.md) | Word / Bit 上の幅非依存な数値型クラス | `Radix/Word/Numeric.lean` |
| [Bit](bit.md) | ビット演算、スキャン、ビットフィールド | `Radix/Bit/` |
| [Bytes](bytes.md) | バイトオーダー、エンディアン、ByteSlice | `Radix/Bytes/` |
| [Memory](memory.md) | バッファ、ポインタ、レイアウト、領域代数 | `Radix/Memory/` |
| [Binary](binary.md) | フォーマット DSL、パーサー、シリアライザー、LEB128 | `Radix/Binary/` |
| [System](system.md) | エラー、FD、IO、仮定 | `Radix/System/` |
| [Concurrency](concurrency.md) | アトミック操作モデル、メモリ順序 | `Radix/Concurrency/` |
| [BareMetal](baremetal.md) | ベアメタルサポート、リンカー、スタートアップ、GCフリー | `Radix/BareMetal/` |
| [Alignment](alignment.md) | アドレスアライメント、パディング、2の冪高速パス | `Radix/Alignment/` |
| [RingBuffer](ringbuffer.md) | Memory.Buffer ベースの固定容量 FIFO | `Radix/RingBuffer/` |
| [Bitmap](bitmap.md) | `Array UInt64` ベースの高密度ビット集合 | `Radix/Bitmap/` |
| [CRC](crc.md) | ストリーミング API 付き CRC-32 / CRC-16 | `Radix/CRC/` |
| [MemoryPool](memorypool.md) | bump / slab アロケータモデル | `Radix/MemoryPool/` |
| [UTF8](utf8.md) | 検証済み UTF-8 スカラモデルと実行可能コーデック | `Radix/UTF8/` |
| [ECC](ecc.md) | Hamming(7,4) パリティと単一ビット訂正ヘルパー | `Radix/ECC/` |
| [DMA](dma.md) | DMA ディスクリプタ検証とコピーシミュレーション | `Radix/DMA/` |
| [Timer](timer.md) | 単調クロックと期限管理ヘルパー | `Radix/Timer/` |
| [ProofAutomation](proofautomation.md) | Radix 専用 tactic マクロ | `Radix/ProofAutomation.lean` |

## 関連ドキュメント

- [アーキテクチャ: コンポーネント](../../architecture/components.md) — コンポーネント概要
- [English version](../../../en/reference/api/) — 英語版
