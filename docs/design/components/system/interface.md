# System Module: Interface

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. エラーモデル (System.Error)

POSIX の errno 的な概念を抽象化しますが、FFIが禁止されているため、直接的なマジックナンバーへの依存は避け、Lean4標準の IO.Error をラップまたは変換して利用します。

`lean
structure SysError where
  message : String

-- OSやプラットフォームの実装差異を吸収するため、IO.Error から SysError への安全なマッピングを行う
def fromIoError (e : IO.Error) : SysError := ⟨toString e⟩
`

## 2. システム関数 API (System.Posix)

TCB 内のシステムコールを extern Cコードに頼ることは禁止されています。
すべて Lean 4 組み込みの IO.FS や IO.Process をラップする形で提供します。

`lean
-- axiom は使用せず、Lean4組み込みの IO.FS.Handle を用いて実装します
-- FDリサイクル攻撃を防ぐため、リソースの管理はLeanの安全なHandleに委ねます
def sysOpen (path : String) (mode : IO.FS.Mode) : IO (Except SysError IO.FS.Handle) := do
  try
    let handle  IO.FS.Handle.mk path mode
    return Except.ok handle
  catch e =>
    return Except.error (fromIoError e)

-- 手動クローズも可能ですが、基本的には withFile 等のスコープ管理（ブラケットパターン）を推奨します
def sysClose (handle : IO.FS.Handle) : IO (Except SysError Unit) := do
  -- （内部実装ではHandleの解放を安全に行う。不要にユーザへ生の数値を露出させない）
  return Except.ok ()
`

## 3. 時刻関連 API (System.Time)

性能計測 (NFR-002) 等のために時間を取得します。
FFIの利用が禁止されたため、Lean組み込みの IO.monoMsNow （またはそれに類する機能）を使用します。

`lean
-- IOモナドによる安全なミリ秒精度時間の取得
def timeMonoMs : IO Nat := IO.monoMsNow
`
