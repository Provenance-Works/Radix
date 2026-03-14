import Radix.Binary.Format
import Radix.Binary.Parser
import Radix.Binary.Serial
import Radix.Bit.Field

/-!
# Example: IPv4 Header Parser

Parses an IPv4 packet header using Radix's Binary Format DSL.
Demonstrates:

- Declarative binary format definition
- Serialization and parsing of network data
- Bit field extraction from packed fields
-/

namespace Examples.IPv4Header

/-- IPv4 header format (first 20 bytes, no options):
    - version_ihl : u8 (4 bits version + 4 bits IHL, packed)
    - dscp_ecn    : u8 (6 bits DSCP + 2 bits ECN)
    - total_length: u16be
    - identification: u16be
    - flags_frag  : u16be (3 bits flags + 13 bits fragment offset)
    - ttl         : u8
    - protocol    : u8
    - checksum    : u16be
    - src_addr    : u32be
    - dst_addr    : u32be -/
private def ipv4HeaderFormat : Radix.Binary.Format :=
  Radix.Binary.Format.byte "version_ihl" ++
  Radix.Binary.Format.byte "dscp_ecn" ++
  Radix.Binary.Format.u16be "total_length" ++
  Radix.Binary.Format.u16be "identification" ++
  Radix.Binary.Format.u16be "flags_frag" ++
  Radix.Binary.Format.byte "ttl" ++
  Radix.Binary.Format.byte "protocol" ++
  Radix.Binary.Format.u16be "checksum" ++
  Radix.Binary.Format.u32be "src_addr" ++
  Radix.Binary.Format.u32be "dst_addr"

/-- Extract IP version (high 4 bits of version_ihl). -/
private def ipVersion (versionIhl : Radix.UInt8) : Nat :=
  (Radix.UInt8.extractBits versionIhl 4 8 ⟨by omega, by omega⟩).toNat

/-- Extract IHL (low 4 bits of version_ihl) in 32-bit words. -/
private def ipIHL (versionIhl : Radix.UInt8) : Nat :=
  (Radix.UInt8.extractBits versionIhl 0 4 ⟨by omega, by omega⟩).toNat

/-- Format an IPv4 address from a 32-bit value. -/
private def formatIPv4 (addr : Radix.UInt32) : String :=
  let b0 := (Radix.UInt32.extractBits addr 24 32 ⟨by omega, by omega⟩).toNat
  let b1 := (Radix.UInt32.extractBits addr 16 24 ⟨by omega, by omega⟩).toNat
  let b2 := (Radix.UInt32.extractBits addr 8 16 ⟨by omega, by omega⟩).toNat
  let b3 := (Radix.UInt32.extractBits addr 0 8 ⟨by omega, by omega⟩).toNat
  s!"{b0}.{b1}.{b2}.{b3}"

/-- Protocol number to name. -/
private def protocolName (proto : Nat) : String :=
  match proto with
  | 1  => "ICMP"
  | 6  => "TCP"
  | 17 => "UDP"
  | n  => s!"Unknown({n})"

def run : IO Unit := do
  IO.println "=== IPv4 Header Parser ==="
  IO.println ""

  -- Construct a sample IPv4 packet header (20 bytes)
  -- Version=4, IHL=5 (no options), total_length=40, TTL=64, protocol=TCP(6)
  -- Source: 192.168.1.100, Dest: 10.0.0.1
  let rawPacket : ByteArray := ByteArray.mk #[
    0x45,       -- version=4, IHL=5
    0x00,       -- DSCP=0, ECN=0
    0x00, 0x28, -- total_length=40
    0x1c, 0x46, -- identification
    0x40, 0x00, -- flags=Don't Fragment, fragment_offset=0
    0x40,       -- TTL=64
    0x06,       -- protocol=TCP(6)
    0xB1, 0xE6, -- checksum
    0xC0, 0xA8, 0x01, 0x64, -- src: 192.168.1.100
    0x0A, 0x00, 0x00, 0x01  -- dst: 10.0.0.1
  ]

  IO.println s!"  Format size: {ipv4HeaderFormat.fixedSize}"
  IO.println s!"  Fields: {ipv4HeaderFormat.fieldNames}"
  IO.println s!"  Raw packet: {rawPacket.size} bytes"
  IO.println ""

  -- Parse the packet
  match Radix.Binary.parseFormat rawPacket ipv4HeaderFormat with
  | .ok parsed =>
    IO.println "  Parsed IPv4 Header:"

    -- Version/IHL
    match Radix.Binary.findField "version_ihl" parsed with
    | some (.byte _ v) =>
      IO.println s!"    Version: {ipVersion v}"
      IO.println s!"    IHL: {ipIHL v} ({ipIHL v * 4} bytes)"
    | _ => IO.println "    version_ihl: not found"

    -- Total length
    match Radix.Binary.findField "total_length" parsed with
    | some (.uint16 _ v) =>
      IO.println s!"    Total Length: {v.toNat} bytes"
    | _ => IO.println "    total_length: not found"

    -- TTL
    match Radix.Binary.findField "ttl" parsed with
    | some (.byte _ v) =>
      IO.println s!"    TTL: {v.toNat}"
    | _ => IO.println "    ttl: not found"

    -- Protocol
    match Radix.Binary.findField "protocol" parsed with
    | some (.byte _ v) =>
      IO.println s!"    Protocol: {protocolName v.toNat}"
    | _ => IO.println "    protocol: not found"

    -- Source IP
    match Radix.Binary.findField "src_addr" parsed with
    | some (.uint32 _ v) =>
      IO.println s!"    Source: {formatIPv4 v}"
    | _ => IO.println "    src_addr: not found"

    -- Destination IP
    match Radix.Binary.findField "dst_addr" parsed with
    | some (.uint32 _ v) =>
      IO.println s!"    Destination: {formatIPv4 v}"
    | _ => IO.println "    dst_addr: not found"

    -- Flags
    match Radix.Binary.findField "flags_frag" parsed with
    | some (.uint16 _ v) =>
      let flags := (Radix.UInt16.extractBits v 13 16 ⟨by omega, by omega⟩).toNat
      let df := flags &&& 0x2 != 0
      let mf := flags &&& 0x1 != 0
      IO.println s!"    Flags: DF={df}, MF={mf}"
    | _ => IO.println "    flags_frag: not found"
  | .error e =>
    throw (IO.userError s!"Parse failed: {e}")

  IO.println ""

  -- Serialize back and verify round-trip
  IO.println "  Round-trip test:"
  let fields : List Radix.Binary.FieldValue := [
    .byte "version_ihl" ⟨0x45⟩,
    .byte "dscp_ecn" ⟨0x00⟩,
    .uint16 "total_length" ⟨0x0028⟩,
    .uint16 "identification" ⟨0x1C46⟩,
    .uint16 "flags_frag" ⟨0x4000⟩,
    .byte "ttl" ⟨0x40⟩,
    .byte "protocol" ⟨0x06⟩,
    .uint16 "checksum" ⟨0xB1E6⟩,
    .uint32 "src_addr" ⟨0xC0A80164⟩,
    .uint32 "dst_addr" ⟨0x0A000001⟩
  ]

  match Radix.Binary.serializeFormat ipv4HeaderFormat fields with
  | .ok bytes =>
    IO.println s!"    Serialized: {bytes.size} bytes"
    if bytes == rawPacket then
      IO.println "    ✓ Round-trip matches original packet"
    else
      IO.println "    ✗ Round-trip mismatch"
  | .error e =>
    IO.println s!"    Serialize error: {e}"

  IO.println ""

end Examples.IPv4Header
