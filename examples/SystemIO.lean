import Radix.System
import Radix.Binary

/-!
# Example: System I/O Operations

Demonstrates file I/O using Radix's system call model. Shows:

- Writing and reading files (binary and text)
- File metadata inspection
- Directory listing
- Multi-file processing pipeline
- Config file pattern
-/

namespace Examples.SystemIO

open Radix.System
open Radix.System.IO

private def exampleFileFormat : Radix.Binary.Format :=
  Radix.Binary.Format.constBytes (ByteArray.mk #[0x52, 0x44, 0x58, 0x21]) ++
  Radix.Binary.Format.u16le "version" ++
  Radix.Binary.Format.lengthPrefixedBytes "payload" 2 .little

/-- Run an IO operation returning Except, throwing on error. -/
private def runChecked {α : Type} (desc : String)
    (op : IO (Except SysError α)) : IO α := do
  let result ← op
  match result with
  | .ok v => return v
  | .error e => throw (IO.userError s!"[{desc}] failed: {reprStr e}")

/-- Create temp directory for examples. -/
private def tmpDir : String := "/tmp/radix_sysio_example"

def run : IO Unit := do
  IO.println "=== System I/O Operations ==="
  IO.println ""

  IO.FS.createDirAll tmpDir

  -- 1. Binary file I/O
  IO.println "  1. Binary File I/O"
  IO.println "  ---"

  let magic : ByteArray := ⟨#[0x52, 0x44, 0x58, 0x21]⟩  -- "RDX!"
  let version : ByteArray := ⟨#[0x01, 0x00]⟩
  let payload : ByteArray := ⟨#[0xDE, 0xAD, 0xBE, 0xEF, 0xCA, 0xFE]⟩
  let payloadLen : ByteArray := ⟨#[payload.size.toUInt8, 0x00]⟩

  let data := magic ++ version ++ payloadLen ++ payload
  IO.println s!"    Writing {data.size} bytes (magic=RDX!, payload={payload.size})"

  let binPath := s!"{tmpDir}/data.rdx"
  runChecked "write binary" (writeFileBytes binPath data)

  let readData ← runChecked "read binary" (readFileBytes binPath)
  IO.println s!"    Read back: {readData.size} bytes"

  match Radix.Binary.parseFormatExact readData exampleFileFormat with
  | .error e => throw (IO.userError s!"binary parse mismatch: {e}")
  | .ok fields =>
    IO.println "    ✓ Magic verified (RDX!)"
    IO.println s!"    ✓ Payload length verified ({payload.size} bytes)"

    match Radix.Binary.findField "payload" fields with
    | some (.bytes _ readPayload) =>
      if readPayload != payload then throw (IO.userError "payload mismatch")
      IO.println "    ✓ Payload data verified"
    | _ => throw (IO.userError "payload field missing")
  IO.println ""

  -- 2. Text file I/O
  IO.println "  2. Text File I/O"
  IO.println "  ---"

  let content := "Hello from Radix!\nLine 2\nLine 3\n"
  let txtPath := s!"{tmpDir}/test.txt"
  runChecked "write text" (writeFileString txtPath content)
  IO.println s!"    Written: {content.length} chars"

  let readContent ← runChecked "read text" (readFileString txtPath)
  if readContent != content then throw (IO.userError "text mismatch")
  IO.println "    ✓ Text round-trip verified"
  IO.println ""

  -- 3. Config file pattern
  IO.println "  3. Config File Pattern"
  IO.println "  ---"

  let configContent :=
    "# Application Config\n" ++
    "host=0.0.0.0\n" ++
    "port=3000\n" ++
    "max_connections=256\n" ++
    "log_level=debug\n" ++
    "database_url=postgres://db.example.com:5432/myapp\n"

  let configPath := s!"{tmpDir}/app.conf"
  runChecked "write config" (writeFileString configPath configContent)

  let configRead ← runChecked "read config" (readFileString configPath)
  let lines := configRead.splitOn "\n" |>.filter (· != "")
  let mut settings : List (String × String) := []
  for line in lines do
    let trimmed := line.trimAscii.toString
    if !trimmed.isEmpty && !trimmed.startsWith "#" then
      match trimmed.splitOn "=" with
      | key :: rest =>
        let value := "=".intercalate rest
        settings := settings ++ [(key.trimAscii.toString, value.trimAscii.toString)]
      | _ => pure ()

  IO.println s!"    Parsed {settings.length} settings:"
  for (key, value) in settings do
    IO.println s!"      {key} = {value}"
  IO.println ""

  -- 4. File metadata
  IO.println "  4. File Metadata"
  IO.println "  ---"

  let fileMeta ← runChecked "file meta" (sysFileMeta binPath)
  IO.println s!"    data.rdx:"
  IO.println s!"      Size: {fileMeta.size} bytes"
  IO.println s!"      Is file: {fileMeta.isFile}"
  IO.println s!"      Is directory: {fileMeta.isDir}"

  let exists1 ← runChecked "exists check" (sysFileExists binPath)
  IO.println s!"    data.rdx exists: {exists1}"
  IO.println ""

  -- 5. Directory listing
  IO.println "  5. Directory Listing"
  IO.println "  ---"

  let entries ← runChecked "list dir" (sysDirEntries tmpDir)
  IO.println s!"    {tmpDir}:"
  for entry in entries.toList do
    IO.println s!"      - {entry}"
  IO.println ""

  -- 6. Multi-file processing pipeline
  IO.println "  6. Log Analysis Pipeline"
  IO.println "  ---"

  let logFiles : List (String × String) := [
    ("log_jan.txt", "INFO server started\nWARN high memory\nERROR disk full\nINFO request served\n"),
    ("log_feb.txt", "INFO server started\nINFO request served\nINFO request served\nWARN slow query\nERROR timeout\nINFO cleanup\n"),
    ("log_mar.txt", "INFO server started\nINFO request served\nWARN deprecated API\n")
  ]

  for (name, contents) in logFiles do
    runChecked s!"write {name}" (writeFileString s!"{tmpDir}/{name}" contents)
  IO.println s!"    Created {logFiles.length} log files"

  let mut totalLines := 0
  let mut infoCount := 0
  let mut warnCount := 0
  let mut errorCount := 0

  for (name, _) in logFiles do
    let fileContent ← runChecked s!"read {name}" (readFileString s!"{tmpDir}/{name}")
    let fileLines := fileContent.splitOn "\n" |>.filter (· != "")
    totalLines := totalLines + fileLines.length
    for line in fileLines do
      if line.startsWith "INFO"  then infoCount  := infoCount + 1
      if line.startsWith "WARN"  then warnCount  := warnCount + 1
      if line.startsWith "ERROR" then errorCount := errorCount + 1

  IO.println s!"    Processed {totalLines} entries across {logFiles.length} files"
  IO.println s!"    INFO:  {infoCount}"
  IO.println s!"    WARN:  {warnCount}"
  IO.println s!"    ERROR: {errorCount}"

  -- Write summary
  let report :=
    s!"Log Analysis Report\n" ++
    s!"Files: {logFiles.length}\n" ++
    s!"Total: {totalLines}\n" ++
    s!"INFO={infoCount} WARN={warnCount} ERROR={errorCount}\n"
  runChecked "write report" (writeFileString s!"{tmpDir}/report.txt" report)
  IO.println s!"    Report written to report.txt"
  IO.println ""

  -- Cleanup
  let cleanEntries ← runChecked "cleanup list" (sysDirEntries tmpDir)
  for entry in cleanEntries.toList do
    IO.FS.removeFile s!"{tmpDir}/{entry}"
  IO.FS.removeDirAll tmpDir
  IO.println "  Cleanup: temp files removed"
  IO.println ""

end Examples.SystemIO
