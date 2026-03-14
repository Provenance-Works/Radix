# System モジュール APIリファレンス

> **モジュール**: `Radix.System`
> **ソース**: `Radix/System/`

## 概要

システム操作のための抽象 POSIX ライクなモデルを提供します。Layer 1（システムブリッジ）コンポーネントを持つ唯一の Radix モジュールです。すべての IO 操作は例外フリーのエラー処理のため `IO (Except SysError α)` を返します。

## エラーモデル (`System.Error`)

```lean
inductive SysError where
  | permissionDenied (msg : String) | notFound (msg : String)
  | alreadyExists (msg : String) | resourceBusy (msg : String)
  | invalidArgument (msg : String) | noSpace (msg : String)
  | ioError (msg : String) | interrupted (msg : String)
  | endOfFile | invalidState (msg : String) | unsupported (msg : String)

def SysError.fromIOError : IO.Error → SysError  -- 完全マッピング
def liftIO : IO α → IO (Except SysError α)      -- 例外キャプチャコンビネータ
instance : ToString SysError
```

## ファイルディスクリプタ (`System.FD`)

```lean
inductive Ownership where
  | owned     -- FD を所有; クローズされる
  | borrowed  -- FD は借用; 呼び出し元がライフタイムを管理

inductive OpenMode where
  | read | write | readWrite | append

def OpenMode.toFSMode : OpenMode → IO.FS.Mode

structure FD where
  handle : IO.FS.Handle
  ownership : Ownership

def FD.ofHandle (h : IO.FS.Handle) (own : Ownership) : FD
def FD.borrow (fd : FD) : FD
def FD.isOwned (fd : FD) : Bool
```

### リソースセーフなファイルアクセス

```lean
def FD.withFile (path : String) (mode : OpenMode) (f : FD → IO α) : IO α
```

ファイルを開き、FD をコールバックに渡し、終了時に**自動クローズ**します（エラー時も）。ブラケットパターンでリソースリークを防止。

## I/O 操作 (`System.IO`)

すべての関数は `IO (Except SysError α)` を返します：

### リード操作

```lean
def sysRead (fd : FD) (count : Nat) : IO (Except SysError ByteArray)
def sysReadLine (fd : FD) : IO (Except SysError String)
def sysReadAll (fd : FD) : IO (Except SysError ByteArray)
```

### ライト操作

```lean
def sysWrite (fd : FD) (data : ByteArray) : IO (Except SysError Nat)
def sysWriteString (fd : FD) (s : String) : IO (Except SysError Nat)
```

### シーク

```lean
def sysSeek (fd : FD) (offset : Int) (mode : SeekMode) : IO (Except SysError Unit)
```

### メタデータ

```lean
def sysFileMeta (path : String) : IO (Except SysError FileInfo)
def sysFileExists (path : String) : IO (Except SysError Bool)
def sysDirEntries (path : String) : IO (Except SysError (List String))
```

### 便利関数

```lean
def readFileBytes (path : String) : IO (Except SysError ByteArray)
def writeFileBytes (path : String) (data : ByteArray) : IO (Except SysError Unit)
def readFileString (path : String) : IO (Except SysError String)
def writeFileString (path : String) (s : String) : IO (Except SysError Unit)
```

## 仕様 (`System.Spec`)

```lean
inductive FileState where | open | closed
inductive SeekMode where | set | cur | end_

structure FileInfo where
  size : Nat
  isFile : Bool
  isDir : Bool

-- 事前条件（すべて open 状態が必要）
def readPre (state : FileState) : Prop := state = .open
def writePre (state : FileState) : Prop := state = .open
def seekPre (state : FileState) : Prop := state = .open
def closePre (state : FileState) : Prop := state = .open

-- 事後条件
def closePost (pre post : FileState) : Prop := pre = .open ∧ post = .closed
def readPost (pre post : FileState) (count actual : Nat) : Prop
-- ライフサイクルモデル
inductive LifecycleStep | openStep | readStep | writeStep | seekStep | closeStep
```

## 信頼仮定 (`System.Assumptions`)

すべての公理は `Prop` 型、`trust_` プレフィックス付きで、POSIX.1-2024 を引用：

| 公理 | 参照 | 主張 |
|-------|-----------|---------|
| `trust_read_bounded` | POSIX read(2) | 成功したリードは ≤ count バイトを返す |
| `trust_write_bounded` | POSIX write(2) | 成功したライトは ≤ count バイトを書き込む |
| `trust_lean_io_faithful` | Lean 4 ランタイム | IO.FS.Handle は忠実に POSIX に委譲する |
| `trust_close_invalidates` | POSIX close(2) | クローズはファイルディスクリプタを無効化する |
| `trust_seek_succeeds` | POSIX lseek(2) | 有効な開いたファイルでシークは成功する |

## 関連ドキュメント

- [エラー](../errors.md) — エラーバリアントの詳細
- [アーキテクチャ: TCB](../../architecture/README.md) — TCB 分析
