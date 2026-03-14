import Radix.Binary.Format
import Radix.Binary.Parser
import Radix.Binary.Serial
import Radix.Bytes.Order

/-!
# Example: Network Protocol Builder

Builds and serializes network protocol headers with correct byte
ordering. Demonstrates:

- Binary Format DSL for protocol headers
- Byte order conversions (big-endian for network)
- Multi-layer protocol composition
-/

namespace Examples.NetworkPacket

/-- Ethernet frame type constants. -/
private def etherTypeIPv4 : Radix.UInt16 := ⟨0x0800⟩
private def etherTypeARP  : Radix.UInt16 := ⟨0x0806⟩
private def etherTypeIPv6 : Radix.UInt16 := ⟨0x86DD⟩

/-- Format a MAC address. -/
private def formatMAC (bytes : List Nat) : String :=
  let hexBytes := bytes.map fun b =>
    let digits := Nat.toDigits 16 b
    let padded := List.replicate (2 - digits.length) '0' ++ digits
    String.ofList padded
  ":".intercalate hexBytes

/-- TCP header format. -/
private def tcpHeaderFormat : Radix.Binary.Format :=
  Radix.Binary.Format.u16be "src_port" ++
  Radix.Binary.Format.u16be "dst_port" ++
  Radix.Binary.Format.u32be "seq_num" ++
  Radix.Binary.Format.u32be "ack_num" ++
  Radix.Binary.Format.u16be "data_offset_flags" ++
  Radix.Binary.Format.u16be "window_size" ++
  Radix.Binary.Format.u16be "checksum" ++
  Radix.Binary.Format.u16be "urgent_ptr"

/-- UDP header format. -/
private def udpHeaderFormat : Radix.Binary.Format :=
  Radix.Binary.Format.u16be "src_port" ++
  Radix.Binary.Format.u16be "dst_port" ++
  Radix.Binary.Format.u16be "length" ++
  Radix.Binary.Format.u16be "checksum"

def run : IO Unit := do
  IO.println "=== Network Protocol Builder ==="
  IO.println ""

  -- 1. Byte order conversions
  IO.println "  1. Byte Order for Network Protocols"
  IO.println "  ---"

  let port : Radix.UInt16 := ⟨0x1F90⟩  -- port 8080
  let portBE := Radix.UInt16.toBigEndian port
  let portBack := Radix.UInt16.fromBigEndian portBE
  IO.println s!"    Port 8080 (0x1F90):"
  IO.println s!"      Host order:    {port.toNat}"
  IO.println s!"      Network order: {portBE.toNat}"
  IO.println s!"      Round-trip:    {portBack.toNat}"

  let addr : Radix.UInt32 := ⟨0xC0A80001⟩  -- 192.168.0.1
  let addrSwapped := Radix.UInt32.bswap addr
  IO.println s!"    IP 192.168.0.1 (0xC0A80001):"
  IO.println s!"      bswap: 0x{String.ofList (Nat.toDigits 16 addrSwapped.toNat)}"
  IO.println ""

  -- 2. UDP packet
  IO.println "  2. UDP Packet"
  IO.println "  ---"

  IO.println s!"    Format: {udpHeaderFormat.fieldNames}"
  IO.println s!"    Header size: {udpHeaderFormat.fixedSize}"

  let payload := "Hello, UDP!".toUTF8
  let udpLen := 8 + payload.size  -- header + payload
  let udpFields : List Radix.Binary.FieldValue := [
    .uint16 "src_port" ⟨12345⟩,
    .uint16 "dst_port" ⟨53⟩,        -- DNS
    .uint16 "length" ⟨udpLen.toUInt16⟩,
    .uint16 "checksum" ⟨0⟩          -- Checksum disabled
  ]

  match Radix.Binary.serializeFormat udpHeaderFormat udpFields with
  | .ok headerBytes =>
    let packet := headerBytes ++ payload
    IO.println s!"    Header: {headerBytes.size} bytes"
    IO.println s!"    Payload: {payload.size} bytes"
    IO.println s!"    Total: {packet.size} bytes"

    -- Parse it back
    match Radix.Binary.parseFormat headerBytes udpHeaderFormat with
    | .ok parsed =>
      for field in parsed do
        match field with
        | .uint16 name v => IO.println s!"    {name}: {v.toNat}"
        | _ => pure ()
    | .error e => IO.println s!"    Parse error: {e}"
  | .error e => IO.println s!"    Serialize error: {e}"
  IO.println ""

  -- 3. TCP header
  IO.println "  3. TCP Header (SYN packet)"
  IO.println "  ---"

  IO.println s!"    Format: {tcpHeaderFormat.fieldNames}"
  IO.println s!"    Header size: {tcpHeaderFormat.fixedSize}"

  -- TCP SYN: data offset=5 (20 bytes), SYN flag (bit 1)
  let dataOffsetFlags : Nat := (5 * 4096) ||| 0x0002  -- offset=5 in high nibble, SYN
  let tcpFields : List Radix.Binary.FieldValue := [
    .uint16 "src_port" ⟨49152⟩,     -- Ephemeral port
    .uint16 "dst_port" ⟨443⟩,       -- HTTPS
    .uint32 "seq_num" ⟨0x12345678⟩,
    .uint32 "ack_num" ⟨0⟩,
    .uint16 "data_offset_flags" ⟨dataOffsetFlags.toUInt16⟩,
    .uint16 "window_size" ⟨65535⟩,
    .uint16 "checksum" ⟨0⟩,
    .uint16 "urgent_ptr" ⟨0⟩
  ]

  match Radix.Binary.serializeFormat tcpHeaderFormat tcpFields with
  | .ok bytes =>
    IO.println s!"    Serialized: {bytes.size} bytes"
    -- Show first few bytes in hex
    let hexStr := bytes.toList.take 8 |>.map fun b =>
      let digits := Nat.toDigits 16 b.toNat
      let padded := List.replicate (2 - digits.length) '0' ++ digits
      String.ofList padded
    IO.println s!"    First 8 bytes: {hexStr}"
  | .error e => IO.println s!"    Serialize error: {e}"
  IO.println ""

  -- 4. Protocol type identification
  IO.println "  4. EtherType Identification"
  IO.println "  ---"
  let types := [(etherTypeIPv4, "IPv4"), (etherTypeARP, "ARP"), (etherTypeIPv6, "IPv6")]
  for (et, name) in types do
    IO.println s!"    0x{String.ofList (Nat.toDigits 16 et.toNat)}: {name}"
  IO.println ""

end Examples.NetworkPacket
