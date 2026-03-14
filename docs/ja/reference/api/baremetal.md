# BareMetal モジュール APIリファレンス

> **モジュール**: `Radix.BareMetal`
> **ソース**: `Radix/BareMetal/`

## 概要

組み込みシステム向けのベアメタル（OS なし）実行環境をモデル化します。プラットフォーム定義、メモリ領域モデリング、ELF リンカースクリプト抽象化、スタートアップシーケンスバリデーション、GCフリー制約チェックを提供します。これは**純粋モデル**であり、実際のハードウェアとの対話はありません。すべての定義は検証と推論に使用される Lean 4 データ構造と関数です。

## ターゲットプラットフォーム (`BareMetal.Spec`)

```lean
inductive Platform where
  | x86_64
  | aarch64
  | riscv64
  deriving DecidableEq, Repr

def Platform.wordBits : Platform → Nat     -- 全プラットフォームで 64
def Platform.naturalAlign : Platform → Nat  -- 全プラットフォームで 8バイト
```

## メモリ領域モデル (`BareMetal.Spec`)

### 領域種別

```lean
inductive RegionKind where
  | flash     -- 読み取り専用の実行可能コードと定数データ（ROM）
  | ram       -- 読み書きデータ
  | mmio      -- メモリマップド I/O レジスタ（アクセスに副作用あり）
  | reserved  -- マップ解除済み; アクセスは未定義
  deriving DecidableEq, Repr
```

### パーミッション

```lean
structure Permissions where
  read    : Bool
  write   : Bool
  execute : Bool
  deriving DecidableEq, Repr

-- 標準パーミッションセット
def Permissions.readOnly : Permissions      -- r--
def Permissions.readWrite : Permissions     -- rw-
def Permissions.readExecute : Permissions   -- r-x
def Permissions.none : Permissions          -- ---
```

### メモリ領域

```lean
structure MemRegion where
  name        : String       -- 例: ".text", "SRAM1", "UART0"
  baseAddr    : Nat
  size        : Nat
  kind        : RegionKind
  permissions : Permissions
  deriving Repr

def MemRegion.endAddr (r : MemRegion) : Nat            -- baseAddr + size
def MemRegion.overlaps (a b : MemRegion) : Prop         -- 決定可能
def MemRegion.disjoint (a b : MemRegion) : Prop         -- 決定可能
def MemRegion.contains (r : MemRegion) (addr : Nat) : Prop  -- 決定可能
```

### メモリマップ

```lean
structure MemoryMap where
  regions  : List MemRegion
  platform : Platform
  deriving Repr

def MemoryMap.isNonOverlapping (mm : MemoryMap) : Prop
def MemoryMap.allNonEmpty (mm : MemoryMap) : Prop
def MemoryMap.isValid (mm : MemoryMap) : Prop      -- isNonOverlapping ∧ allNonEmpty
def MemoryMap.findRegion (mm : MemoryMap) (addr : Nat) : Option MemRegion
def MemoryMap.totalSize (mm : MemoryMap) : Nat
```

## ブートシーケンス (`BareMetal.Spec`)

### スタートアップフェーズ

```lean
inductive StartupPhase where
  | reset         -- プロセッサリセット、最小限のハードウェア初期化
  | earlyInit     -- スタックポインタ、BSS、データセクション
  | platformInit  -- クロック、ペリフェラル、割り込み
  | runtimeInit   -- ヒープ（もしあれば）、グローバルコンストラクタ
  | appEntry      -- アプリケーションエントリ（main）
  deriving DecidableEq, Repr

def StartupPhase.order : StartupPhase → Nat   -- 0..4
def StartupPhase.precedes (a b : StartupPhase) : Bool
```

### スタートアップステップとシーケンス

```lean
structure StartupStep where
  source : StartupPhase
  target : StartupPhase

def StartupStep.isValid (s : StartupStep) : Prop   -- target.order = source.order + 1

structure StartupSequence where
  steps : List StartupStep

def StartupSequence.isComplete (seq : StartupSequence) : Prop
  -- 4ステップ、すべて有効、reset で開始、appEntry で終了
```

### ブート不変条件

```lean
structure BootInvariant where
  stackAligned    : Nat → Platform → Prop   -- SP % naturalAlign = 0
  stackInRAM      : Nat → MemoryMap → Prop  -- SP が RAM 領域内
  bssZeroed       : Prop
  dataInitialized : Prop
```

### アロケーション戦略

```lean
inductive AllocStrategy where
  | static  -- コンパイル時アロケーション（グローバル/スタティック）
  | stack   -- 関数ローカルアロケーション
  | arena   -- アリーナ/プールアロケーション（呼び出し元がライフタイムを管理）
  | none    -- 純粋計算、アロケーションなし
  deriving DecidableEq, Repr

def AllocStrategy.isGCFree : AllocStrategy → Bool  -- 全バリアントで true

structure AllocProfile where
  name     : String
  strategy : AllocStrategy
  maxStack : Option Nat
```

## GCフリー制約 (`BareMetal.GCFree`)

### ライフタイム分類

```lean
inductive Lifetime where
  | static      -- プログラム全体
  | stack       -- 囲む関数呼び出し
  | arena       -- 囲むアリーナスコープ
  | compileTime -- コンパイル時定数
  deriving DecidableEq, Repr

def Lifetime.isBounded : Lifetime → Bool  -- 全バリアントで true
```

### 禁止パターン

```lean
inductive ForbiddenPattern where
  | unboundedAlloc   -- 無制限のヒープ成長
  | mutableCapture   -- 可変参照のクロージャキャプチャ
  | dynamicDispatch  -- オブジェクトポリモーフィズム
  | lazyThunk        -- 遅延サンクの作成
  | heapException    -- ヒープアロケートされた例外オブジェクト
  deriving DecidableEq, Repr

def ForbiddenPattern.description : ForbiddenPattern → String
```

### 制約チェック

```lean
structure GCFreeConstraint where
  maxStackBytes     : Nat
  allowedStrategies : List AllocStrategy
  forbidden         : List ForbiddenPattern

def GCFreeConstraint.default : GCFreeConstraint
  -- maxStack=4096, strategies=[static,stack,none], 全パターン禁止

def GCFreeConstraint.withArena (maxStack : Nat := 8192) : GCFreeConstraint
  -- arena を許可戦略に追加

inductive CheckResult where
  | pass
  | failStrategy (name : String) (strategy : AllocStrategy)
  | failStackOverflow (name : String) (used limit : Nat)

def checkProfile (constraint : GCFreeConstraint) (profile : AllocProfile) : Bool
def checkProfileDetailed (constraint : GCFreeConstraint) (profile : AllocProfile) : CheckResult
def checkModule (constraint : GCFreeConstraint) (profiles : List AllocProfile) : List CheckResult
```

### スタック使用量モデル

```lean
structure StackFrame where
  name       : String
  localBytes : Nat
  savedRegs  : Nat
  padding    : Nat

def StackFrame.totalSize (f : StackFrame) : Nat  -- localBytes + savedRegs + padding
def worstCaseStackDepth (frames : List StackFrame) : Nat
```

## リンカースクリプトモデル (`BareMetal.Linker`)

### セクションフラグ

```lean
structure SectionFlags where
  write : Bool
  alloc : Bool
  exec  : Bool
  deriving DecidableEq, Repr

-- 標準フラグセット
def SectionFlags.text : SectionFlags      -- alloc + exec
def SectionFlags.rodata : SectionFlags    -- alloc のみ
def SectionFlags.data : SectionFlags      -- alloc + write
def SectionFlags.bss : SectionFlags       -- alloc + write
```

### セクション

```lean
structure Section where
  name  : String     -- 例: ".text", ".data", ".bss"
  lma   : Nat        -- ロードメモリアドレス（ロード元）
  vma   : Nat        -- 仮想メモリアドレス（実行時位置）
  size  : Nat
  flags : SectionFlags

def Section.endAddr (s : Section) : Nat   -- vma + size
def Section.overlaps (a b : Section) : Prop
def Section.disjoint (a b : Section) : Prop
```

### シンボル

```lean
structure Symbol where
  name        : String
  addr        : Nat
  sectionName : String
```

### リンカースクリプト

```lean
structure LinkerScript where
  sections   : List Section
  symbols    : List Symbol
  entryPoint : String
  platform   : Platform

def LinkerScript.findSection (ls : LinkerScript) (name : String) : Option Section
def LinkerScript.findSymbol (ls : LinkerScript) (name : String) : Option Symbol
def LinkerScript.entryAddr (ls : LinkerScript) : Option Nat
def LinkerScript.isNonOverlapping (ls : LinkerScript) : Prop
def LinkerScript.allNonEmpty (ls : LinkerScript) : Prop
def LinkerScript.isValid (ls : LinkerScript) : Prop
  -- isNonOverlapping ∧ allNonEmpty ∧ entryAddr.isSome
def LinkerScript.totalSize (ls : LinkerScript) : Nat
```

### アドレスアライメント

```lean
def alignUp (addr align : Nat) : Nat      -- 次の倍数に切り上げ
def alignDown (addr align : Nat) : Nat    -- 前の倍数に切り下げ
def isAligned (addr align : Nat) : Bool    -- addr % align == 0
```

### メモリマップ構築

```lean
def sectionToRegion (s : Section) : MemRegion   -- exec→flash, write→ram, それ以外→flash
def toMemoryMap (ls : LinkerScript) : MemoryMap
```

## スタートアップシーケンス (`BareMetal.Startup`)

### スタートアップアクション

```lean
inductive StartupAction where
  | setStackPointer (addr : Nat)
  | zeroBSS (baseAddr size : Nat)
  | copyData (lma vma size : Nat)
  | setVectorTable (addr : Nat)
  | setInterrupts (enable : Bool)
  | configClock
  | callConstructors
  | jumpToEntry (addr : Nat)
  deriving Repr
```

### スタートアップテンプレート

```lean
def minimalStartupActions (stackTop bssBase bssSize dataLMA dataVMA dataSize entry : Nat)
    : List StartupAction
  -- [disableIRQ, setSP, zeroBSS, copyData, enableIRQ, jumpToEntry]

def fullStartupActions (stackTop bssBase bssSize dataLMA dataVMA dataSize vectorTable entry : Nat)
    : List StartupAction
  -- [disableIRQ, setSP, setVectorTable, configClock, zeroBSS, copyData,
  --  callConstructors, enableIRQ, jumpToEntry]
```

### スタートアップバリデーション

```lean
def startsWithInterruptsDisabled (actions : List StartupAction) : Bool
def setsStackBeforeUse (actions : List StartupAction) : Bool
def endsWithJump (actions : List StartupAction) : Bool
def isValidStartupSequence (actions : List StartupAction) : Bool
  -- length > 0 ∧ startsWithInterruptsDisabled ∧ setsStackBeforeUse ∧ endsWithJump
```

### リンカースクリプトからの生成

```lean
def extractStartupParams (ls : LinkerScript)
    : Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  -- (stackTop, bssBase, bssSize, dataLMA, dataVMA, dataSize, entry)

def generateStartup (ls : LinkerScript) : Option (List StartupAction)
```

## 証明 (`BareMetal.Lemmas`)

### メモリ領域の性質
- `MemRegion.disjoint_comm`: 分離性は対称
- `MemRegion.disjoint_of_endAddr_le`: 分離性の十分条件
- `MemRegion.not_contains_of_disjoint`: 分離した領域はアドレスを共有しない
- `MemRegion.endAddr_eq`: `endAddr = baseAddr + size`

### メモリマップの性質
- `MemoryMap.empty_isValid`: 空のメモリマップは有効
- `MemoryMap.empty_totalSize`: 空のメモリマップのサイズは 0
- `MemoryMap.empty_findRegion`: 空のマップは何も見つけない

### セクションとリンカースクリプトの性質
- `Section.disjoint_comm`: セクション分離性は対称
- `LinkerScript.empty_isNonOverlapping`: 空のリンカースクリプトは非重複
- `LinkerScript.empty_totalSize`: 空のリンカースクリプトの合計サイズは 0

### アライメントの性質
- `alignUp_ge`: `alignUp addr align ≥ addr`
- `alignDown_le`: `alignDown addr align ≤ addr`
- `alignUp_zero`: `alignUp 0 align = 0`
- `alignDown_zero`: `alignDown 0 align = 0`
- `isAligned_zero`: `isAligned 0 align = true`

### GCフリーの性質
- `AllocStrategy.all_isGCFree`: 全戦略が GCフリー
- `GCFreeConstraint.default_allows_static`: デフォルトは static を許可
- `GCFreeConstraint.default_allows_stack`: デフォルトは stack を許可
- `GCFreeConstraint.default_forbids_arena`: デフォルトは arena を禁止
- `GCFreeConstraint.withArena_allows_arena`: withArena は arena を許可
- `checkModule_empty`: 空モジュールは通過

### スタックフレームの性質
- `StackFrame.totalSize_eq`: `totalSize = localBytes + savedRegs + padding`
- `worstCaseStackDepth_nil`: 空リストの深さは 0
- `worstCaseStackDepth_cons`: `depth(f::fs) = depth(fs) + f.totalSize`

### スタートアップの性質
- `minimalStartup_startsWithInterruptsDisabled`: minimal は IRQ オフで開始
- `minimalStartup_endsWithJump`: minimal はジャンプで終了
- `minimalStartup_isValid`: minimal スタートアップは有効
- `fullStartup_isValid`: full スタートアップは有効

### プラットフォームの性質
- `Platform.wordBits_pos`: ワードビット > 0
- `Platform.naturalAlign_pos`: ナチュラルアライメント > 0
- `StartupPhase.reset_precedes_appEntry`: reset は appEntry より前
- `StartupPhase.order_injective`: フェーズ順序は単射

## 信頼仮定 (`BareMetal.Assumptions`)

すべての公理は `Prop` 型、`trust_` プレフィックス付きで、ハードウェア仕様を引用：

| 公理 | 参照 | 主張 |
|-------|-----------|---------|
| `trust_reset_entry` | ARM D1.6.1, RISC-V §3.4 | プロセッサは指定されたリセットベクタで開始 |
| `trust_static_allocation_stable` | System V ABI, ELF §2-2 | スタティックメモリアロケーションは実行時に再配置されない |
| `trust_mmio_volatile` | ARM B2.1, RISC-V PMA | MMIO アクセスは正確に1回のバストランザクションを生成し、並べ替えられない |
| `trust_bss_zeroed` | System V ABI, Process Init | BSS 領域はスタートアップ初期化後にゼロとして読める |
| `trust_stack_grows_down` | AMD64 ABI §3.2.2, AAPCS64 §6.2.2 | スタックポインタはプッシュ前にデクリメントされる |

## 関連ドキュメント

- [Concurrency](concurrency.md) — 並行性モデル
- [アーキテクチャ: コンポーネント](../../architecture/components.md) — モジュール概要
