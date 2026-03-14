# トラブルシューティング

> **対象読者**: すべてのユーザー

## ビルドの問題

### 初回ビルドで `lake build` が Mathlib エラーで失敗する

**原因:** Mathlib のダウンロードまたはコンパイルが途中で失敗しました。

**解決策:**
```bash
lake clean
lake update
lake build
```

Mathlib のコンパイルが非常に遅い場合、十分なメモリがあることを確認してください（8 GB以上推奨）。Mathlib のコンパイルはメモリ集約的です。

### ツールチェインのバージョン不一致

**症状:** `unknown package 'Init'` や `import Mathlib failed` などのエラー。

**原因:** プロジェクトの `lean-toolchain` が Radix のピン留めされたツールチェイン（`leanprover/lean4:v4.29.0-rc4`）と一致しません。

**解決策:** プロジェクトの `lean-toolchain` を Radix と整合させます：
```
leanprover/lean4:v4.29.0-rc4
```

### `unknown identifier 'Radix.UInt32'`

**原因:** `open Radix` が不足しているか、インポートが不完全です。

**解決策:**
```lean
import Radix
open Radix

-- これで UInt32.wrappingAdd がプレフィックスなしで利用可能
```

または完全修飾名を使用：
```lean
import Radix
#eval Radix.UInt32.wrappingAdd 100 200
```

### `UInt8`、`UInt16` 等で `ambiguous, possible interpretations`

**原因:** Radix の `UInt8` 等が Lean 4 の同名の組み込み型をシャドウしています。

**解決策:** `open Radix` 内では Radix の型が優先されます。組み込み型が必要な場合は `_root_.UInt8` を使用してください。変換方法：
```lean
let radixVal : Radix.UInt32 := ...
let builtinVal : _root_.UInt32 := radixVal.toBuiltin
let backToRadix : Radix.UInt32 := Radix.UInt32.fromBuiltin builtinVal
```

## 型エラー

### `type mismatch: expected BitVec n, got UInt32`

**原因:** Radix 型（Layer 2）と Mathlib の `BitVec`（Layer 3）の変換なしの混在。

**解決策:** `toBitVec` / `fromBitVec` を使用：
```lean
let x : UInt32 := ...
let bv : BitVec 32 := x.toBitVec    -- Layer 2 → Layer 3
let y : UInt32 := UInt32.fromBitVec bv  -- Layer 3 → Layer 2
```

### Tier 1 API: `failed to synthesize proof`

**原因:** Tier 1（証明付き）API はコンパイル時の境界証明を必要とします。証明義務が自動的に解消できない場合、このエラーが発生します。

**解決策:** 証明を手動で提供するか、Tier 2（チェック付き）API を使用：
```lean
-- Tier 1: 証明が必要
let result := buf.readU8 0 (by omega)  -- omega による証明

-- Tier 2: 証明不要、Option を返す
let result := buf.checkedReadU8 0  -- Option UInt8 を返す
```

### 証明内の `sorry`

**症状:** ビルド後に公理 `sorry` についての警告。

**原因:** 依存関係チェインのどこかに未完了の証明があります。

**解決策:** Radix のリリースは `sorry` がゼロでなければなりません。この警告が表示される場合、開発ブランチではなく公式リリースを使用していることを確認してください。

## システム I/O エラー

### ファイル書き込み時の `SysError.permissionDenied`

**原因:** ターゲットパスに書き込み権限がないか、読み取り専用ファイルシステムです。

**解決策:** ファイル権限を確認：
```bash
ls -la /path/to/file
chmod u+w /path/to/file
```

### ファイル読み取り時の `SysError.notFound`

**原因:** 指定されたファイルが存在しません。

**解決策:** パスを確認し、事前にファイルの存在を確認：
```lean
let exists ← System.IO.sysFileExists "myfile.bin"
match exists with
| .ok true => -- ファイルが存在、安全に読み取り可能
| _ => -- ファイルが見つからない場合の処理
```

### `sysRead` 中の `SysError.endOfFile`

**原因:** ファイルの末尾を超えて読み取ろうとしました。

**解決策:** これは期待される動作です。`sysRead` はデータがなくなると `endOfFile` を返します。結果を確認：
```lean
let result ← System.IO.sysRead fd 1024
match result with
| .ok bytes => if bytes.size == 0 then /- EOF -/ else /- bytes を処理 -/
| .error .endOfFile => /- 明示的に EOF に到達 -/
| .error e => /- その他のエラー -/
```

## パフォーマンスの問題

### C に比べて操作が遅い

**原因:** Radix は Lean 4 の組み込み型をラップしていますが、Lean 4 ランタイムはベア C に比べてオーバーヘッドがあります（GC、参照カウント）。

**解決策:**
- 最適化付きでビルドしていることを確認：`lake build`（リリースモード）を使用
- `@[inline]` 操作を使用（多くの Radix 操作はすでにインライン化済み）
- ホットループでは、ラッピング算術バリアントの使用を検討（分岐オーバーヘッドなし）
- C とのベースライン比較については[ベンチマーク](../../benchmarks/)を参照

### プロパティテストが遅い

**原因:** プロパティベーステストはデフォルトでテストあたり500イテレーション実行します。

**解決策:** これは徹底的なカバレッジのための設計上の仕様です。開発中に高速なイテレーションが必要な場合は、テストコード内のイテレーション数を一時的に減らすことができます。

## LEB128 の問題

### `decodeU32` が `none` を返す

**原因:**
- 入力の切り詰め（継続ビット = 0 の最終バイトの前にバイトシーケンスが終了）
- 冗長なエンコーディング（U32 で5バイト超、U64 で10バイト超）
- オーバーフロー（デコードされた値が型の範囲を超過）

**解決策:** 入力に有効な LEB128 エンコーディングが含まれていることを確認してください。エンコーディングはビット7がクリアされたバイトで終了する必要があります。

## 関連ドキュメント

- [エラーリファレンス](../reference/errors.md) — 完全なエラーカタログ
- [構成](configuration.md) — ビルド構成
- [インストール](../getting-started/installation.md) — セットアップ手順
