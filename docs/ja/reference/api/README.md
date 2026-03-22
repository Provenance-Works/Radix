# APIリファレンス

> **対象読者**: 開発者

Radix v0.2.0 の全モジュールと拡張面に対するモジュール別 API ドキュメントです。

## モジュール索引

| モジュール | 説明 | ソース |
|--------|-------------|--------|
| [Word](word.md) | 固定幅整数、算術モード、変換 | `Radix/Word/` |
| [Numeric](numeric.md) | Word / Bit 上の幅非依存な数値型クラス | `Radix/Word/Numeric.lean` |
| [Bit](bit.md) | ビット演算、スキャン、ビットフィールド | `Radix/Bit/` |
| [Bytes](bytes.md) | バイトオーダー、エンディアン、ByteSlice | `Radix/Bytes/` |
| [Memory](memory.md) | バッファ、ポインタ、レイアウト | `Radix/Memory/` |
| [Binary](binary.md) | フォーマット DSL、パーサー、シリアライザー、LEB128 | `Radix/Binary/` |
| [System](system.md) | エラー、FD、IO、仮定 | `Radix/System/` |
| [Concurrency](concurrency.md) | アトミック操作モデル、メモリ順序 | `Radix/Concurrency/` |
| [BareMetal](baremetal.md) | ベアメタルサポート、リンカー、スタートアップ、GCフリー | `Radix/BareMetal/` |
| [Alignment](alignment.md) | アドレスアライメント、パディング、2の冪高速パス | `Radix/Alignment/` |
| [RingBuffer](ringbuffer.md) | Memory.Buffer ベースの固定容量 FIFO | `Radix/RingBuffer/` |
| [Bitmap](bitmap.md) | `Array UInt64` ベースの高密度ビット集合 | `Radix/Bitmap/` |
| [CRC](crc.md) | ストリーミング API 付き CRC-32 / CRC-16 | `Radix/CRC/` |
| [MemoryPool](memorypool.md) | bump / slab アロケータモデル | `Radix/MemoryPool/` |

## 関連ドキュメント

- [アーキテクチャ: コンポーネント](../../architecture/components.md) — コンポーネント概要
- [English version](../../../en/reference/api/) — 英語版
