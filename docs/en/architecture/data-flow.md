# Data Flow

> **Audience**: Developers, Contributors

## Layer 3 → Layer 2 → Layer 1 Flow

Data in Radix flows through the three-layer architecture. Specifications (Layer 3) define correctness, implementations (Layer 2) perform computation, and the bridge (Layer 1) connects to the OS.

```mermaid
sequenceDiagram
    participant User as User Code
    participant L2 as Layer 2 (Impl)
    participant L3 as Layer 3 (Spec)
    participant L1 as Layer 1 (Bridge)
    participant OS as OS / Runtime

    User->>L2: Call wrappingAdd(x, y)
    L2->>L2: Compute x.val + y.val (inline)
    L2-->>User: Return result (zero-cost)

    Note over L3,L2: Proof: wrappingAdd matches BitVec spec

    User->>L1: Call sysRead(fd, count)
    L1->>OS: IO.FS.Handle.read(count)
    OS-->>L1: ByteArray
    L1->>L2: Construct ByteSlice (verified)
    L1-->>User: IO (Except SysError ByteArray)

    Note over L3,L1: Axiom: trust_lean_io_faithful
```

## File Read Flow (End-to-End)

```mermaid
sequenceDiagram
    participant App as Application
    participant SIO as System.IO
    participant SFD as System.FD
    participant SErr as System.Error
    participant SSpec as System.Spec
    participant Lean4 as Lean 4 IO.FS

    App->>SFD: withFile "data.bin" .read
    SFD->>Lean4: IO.FS.Handle.mk
    Lean4-->>SFD: Handle
    SFD->>SFD: Create FD (owned)
    SFD->>App: callback(fd)
    App->>SIO: sysRead fd 1024
    SIO->>Lean4: handle.read 1024
    Lean4-->>SIO: ByteArray (or IO.Error)
    alt Success
        SIO-->>App: Except.ok bytes
    else Failure
        SIO->>SErr: fromIOError error
        SErr-->>SIO: SysError
        SIO-->>App: Except.error sysError
    end
    App->>SFD: withFile closes automatically
    SFD->>Lean4: handle.close
```

## Binary Parse/Serialize Round-Trip

```mermaid
sequenceDiagram
    participant App as Application
    participant Fmt as Binary.Format
    participant Ser as Binary.Serial
    participant Par as Binary.Parser
    participant Buf as Memory.Buffer

    App->>Fmt: Define format (u16be, u32le, pad 2)
    App->>Ser: serializeFormat format values
    Ser->>Buf: Write fields with endianness
    Buf-->>Ser: ByteArray
    Ser-->>App: ByteArray (serialized)

    App->>Par: parseFormat format data
    Par->>Buf: Read fields with endianness
    Buf-->>Par: FieldValues
    Par-->>App: List FieldValue (parsed)

    Note over Ser,Par: Proof: parse ∘ serialize = id
```

## LEB128 Encode/Decode Flow

```mermaid
flowchart LR
    subgraph Encode
        V["UInt32 value"] --> E1["Extract 7 low bits"]
        E1 --> E2{"value >= 128?"}
        E2 -->|Yes| E3["Set continue bit<br/>Push byte<br/>value /= 128"]
        E3 --> E1
        E2 -->|No| E4["Push final byte"]
    end
    subgraph Decode
        D1["Read byte"] --> D2["Extract 7 data bits"]
        D2 --> D3["Accumulate at shift position"]
        D3 --> D4{"Continue bit set?"}
        D4 -->|Yes| D5["shift += 7"]
        D5 --> D1
        D4 -->|No| D6["Return value"]
    end
    E4 --> |"ByteArray"| D1
```

## Arithmetic Mode Selection

```mermaid
flowchart TD
    Start["Integer Operation"] --> Q1{"Have overflow proof?"}
    Q1 -->|Yes| T1["Tier 1: Proof-Carrying<br/>addChecked(x, y, h)"]
    Q1 -->|No| Q2{"Need exact result?"}
    Q2 -->|Yes| Checked["checkedAdd(x, y)<br/>Returns Option"]
    Q2 -->|No| Q3{"Need overflow flag?"}
    Q3 -->|Yes| Overflowing["overflowingAdd(x, y)<br/>Returns (result, flag)"]
    Q3 -->|No| Q4{"Accept clamping?"}
    Q4 -->|Yes| Saturating["saturatingAdd(x, y)<br/>Clamps to bounds"]
    Q4 -->|No| Wrapping["wrappingAdd(x, y)<br/>Wraps mod 2^n"]
```

## Related Documents

- [Architecture Overview](README.md) — Three-layer model
- [Components](components.md) — Module details
- [Module Dependencies](module-dependency.md) — Dependency graph
