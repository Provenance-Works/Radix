import tests.ComprehensiveTests.Framework
import Radix.System.IO
import Radix.System.FD

/-!
# System IO Tests (actual IO with temp files)
## Spec References
- FR-006: File I/O operations, withFile bracket
-/

open ComprehensiveTests

def runSystemIOTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    System IO tests..."

  -- ## Write and read file bytes
  let tmpDir := "/tmp/radix_test_" ++ toString (← IO.monoMsNow)
  IO.FS.createDirAll tmpDir

  let testFile := tmpDir ++ "/test.bin"
  let testData := ByteArray.mk #[0x01, 0x02, 0x03, 0x04, 0x05]

  let wr ← Radix.System.IO.writeFileBytes testFile testData
  match wr with
  | .ok () =>
    let rd ← Radix.System.IO.readFileBytes testFile
    match rd with
    | .ok bytes =>
      assert (bytes.size == 5) "readFileBytes size"
      assert (bytes == testData) "readFileBytes data match"
    | .error e => assert false s!"readFileBytes error: {e}"
  | .error e => assert false s!"writeFileBytes error: {e}"

  -- ## Write and read file string
  let strFile := tmpDir ++ "/test.txt"
  let testStr := "Hello, Radix! 日本語テスト"
  let ws ← Radix.System.IO.writeFileString strFile testStr
  match ws with
  | .ok () =>
    let rs ← Radix.System.IO.readFileString strFile
    match rs with
    | .ok rd => assert (rd == testStr) "readFileString match"
    | .error e => assert false s!"readFileString error: {e}"
  | .error e => assert false s!"writeFileString error: {e}"

  -- ## File exists
  let fe ← Radix.System.IO.sysFileExists testFile
  match fe with
  | .ok found => assert (found == true) "sysFileExists true"
  | .error e => assert false s!"sysFileExists error: {e}"

  let fe2 ← Radix.System.IO.sysFileExists (tmpDir ++ "/nonexistent")
  match fe2 with
  | .ok found => assert (found == false) "sysFileExists false"
  | .error _ => assert true "sysFileExists nonexistent (error ok)"

  let feDir ← Radix.System.IO.sysFileExists tmpDir
  match feDir with
  | .ok found => assert (found == false) "sysFileExists directory is false"
  | .error e => assert false s!"sysFileExists directory error: {e}"

  -- ## File metadata
  let fm ← Radix.System.IO.sysFileMeta testFile
  match fm with
  | .ok info =>
    assert (info.size == 5) "fileMeta size"
    assert (info.isFile == true) "fileMeta isFile"
    assert (info.isDir == false) "fileMeta isDir"
  | .error e => assert false s!"sysFileMeta error: {e}"

  let fm2 ← Radix.System.IO.sysFileMeta tmpDir
  match fm2 with
  | .ok info =>
    assert (info.isDir == true) "fileMeta dir isDir"
    assert (info.isFile == false) "fileMeta dir isFile"
  | .error e => assert false s!"sysFileMeta dir error: {e}"

  let fmMissing ← Radix.System.IO.sysFileMeta (tmpDir ++ "/ghost")
  match fmMissing with
  | .ok _ => assert false "fileMeta missing should fail"
  | .error err =>
    assert (match err with | .notFound _ => true | _ => false) "fileMeta missing returns notFound"

  -- ## Dir entries
  let de ← Radix.System.IO.sysDirEntries tmpDir
  match de with
  | .ok entries =>
    assert (entries.size ≥ 2) "dirEntries count"
    assert (entries.contains "test.bin") "dirEntries include test.bin"
    assert (entries.contains "test.txt") "dirEntries include test.txt"
  | .error e => assert false s!"sysDirEntries error: {e}"

  let deMissing ← Radix.System.IO.sysDirEntries (tmpDir ++ "/ghost_dir")
  match deMissing with
  | .ok _ => assert false "dirEntries missing should fail"
  | .error err =>
    assert (match err with | .notFound _ => true | _ => false) "dirEntries missing returns notFound"

  -- ## withFile bracket
  let bracketFile := tmpDir ++ "/bracket.txt"
  let bw ← Radix.System.withFile bracketFile .write (fun fd => do
    Radix.System.IO.sysWriteString fd "bracket test")
  match bw with
  | .ok () =>
    let br ← Radix.System.IO.readFileString bracketFile
    match br with
    | .ok rd => assert (rd == "bracket test") "withFile write-read"
    | .error e => assert false s!"withFile read error: {e}"
  | .error e => assert false s!"withFile write error: {e}"

  let withMissingRead ← Radix.System.withFile (tmpDir ++ "/ghost.txt") .read (fun fd => do
    Radix.System.IO.sysReadAll fd)
  match withMissingRead with
  | .ok _ => assert false "withFile read missing should fail"
  | .error err =>
    assert (match err with | .notFound _ => true | _ => false) "withFile missing file returns notFound"

  let bracketBodyError : Except Radix.System.SysError Unit ←
    Radix.System.withFile (tmpDir ++ "/body_error.txt") .write (fun _ => do
      pure (.error (.invalidState "body failed")))
  match bracketBodyError with
  | .ok _ => assert false "withFile body error should propagate"
  | .error err =>
    assert (match err with | .invalidState msg => msg == "body failed" | _ => false)
      "withFile propagates body error unchanged"

  -- ## Read from non-existent file
  let rn ← Radix.System.IO.readFileBytes (tmpDir ++ "/nope.bin")
  match rn with
  | .ok _    => assert false "read nonexistent should fail"
  | .error _ => assert true "read nonexistent errors"

  -- ## Empty file
  let emptyFile := tmpDir ++ "/empty.bin"
  let we ← Radix.System.IO.writeFileBytes emptyFile ByteArray.empty
  match we with
  | .ok () =>
    let re ← Radix.System.IO.readFileBytes emptyFile
    match re with
    | .ok rd => assert (rd.size == 0) "empty file size 0"
    | .error e => assert false s!"read empty error: {e}"
  | .error e => assert false s!"write empty error: {e}"

  -- ## Seeking and partial reads
  let seekFile := tmpDir ++ "/seek.bin"
  let seekData := ByteArray.mk #[10, 20, 30, 40, 50]
  let seekWrite ← Radix.System.IO.writeFileBytes seekFile seekData
  match seekWrite with
  | .error e => assert false s!"seek test write error: {e}"
  | .ok () =>
    let seekRead ← Radix.System.withFile seekFile .read (fun fd => do
      let seekResult ← Radix.System.IO.sysSeek fd .set 2
      match seekResult with
      | .error e => pure (.error e)
      | .ok () => Radix.System.IO.sysRead fd 2)
    match seekRead with
    | .ok bytes => assert (bytes.toList == [30, 40]) "seek set then read"
    | .error e => assert false s!"seek test read error: {e}"

  let seekNegative ← Radix.System.withFile seekFile .read (fun fd => do
    Radix.System.IO.sysSeek fd .set (-1))
  match seekNegative with
  | .ok _ => assert false "negative SEEK_SET should fail"
  | .error err =>
    assert (match err with | .invalidArgument _ => true | _ => false) "negative SEEK_SET returns invalidArgument"

  let seekCurNegative ← Radix.System.withFile seekFile .read (fun fd => do
    Radix.System.IO.sysSeek fd .cur (-1))
  match seekCurNegative with
  | .ok _ => assert false "negative SEEK_CUR should fail"
  | .error err =>
    assert (match err with | .unsupported _ => true | _ => false) "negative SEEK_CUR returns unsupported"

  let seekEnd ← Radix.System.withFile seekFile .read (fun fd => do
    Radix.System.IO.sysSeek fd .end_ 0)
  match seekEnd with
  | .ok _ => assert false "SEEK_END should fail"
  | .error err =>
    assert (match err with | .unsupported _ => true | _ => false) "SEEK_END returns unsupported"

  -- ## Access mode mismatches
  let readFromWriteOnly ← Radix.System.withFile seekFile .write (fun fd => do
    Radix.System.IO.sysRead fd 1)
  match readFromWriteOnly with
  | .ok _ => assert false "read from write-only handle should fail"
  | .error err =>
    assert (match err with | .permissionDenied _ => true | .ioError _ => true | _ => false)
      "read from write-only handle fails with mapped IO error"

  let writeToReadOnly ← Radix.System.withFile seekFile .read (fun fd => do
    Radix.System.IO.sysWrite fd (ByteArray.mk #[0x99]))
  match writeToReadOnly with
  | .ok _ => assert false "write to read-only handle should fail"
  | .error err =>
    assert (match err with | .permissionDenied _ => true | .ioError _ => true | _ => false)
      "write to read-only handle fails with mapped IO error"

  -- ## Append mode semantics
  let appendFile := tmpDir ++ "/append.txt"
  let appendInit ← Radix.System.IO.writeFileString appendFile "A"
  match appendInit with
  | .error e => assert false s!"append init write error: {e}"
  | .ok () =>
    let appendWrite ← Radix.System.withFile appendFile .append (fun fd => do
      Radix.System.IO.sysWriteString fd "BC")
    match appendWrite with
    | .error e => assert false s!"append write error: {e}"
    | .ok () =>
      let appendRead ← Radix.System.IO.readFileString appendFile
      match appendRead with
      | .ok content => assert (content == "ABC") "append mode appends instead of truncating"
      | .error e => assert false s!"append read error: {e}"

  -- ## Large file write-read
  let largeFile := tmpDir ++ "/large.bin"
  let largeData := ByteArray.mk (Array.mkEmpty 10000 |>.append (List.replicate 10000 0x42).toArray)
  let wl ← Radix.System.IO.writeFileBytes largeFile largeData
  match wl with
  | .ok () =>
    let rl ← Radix.System.IO.readFileBytes largeFile
    match rl with
    | .ok rd =>
      assert (rd.size == 10000) "large file size"
      assert (rd == largeData) "large file data"
    | .error e => assert false s!"large read error: {e}"
  | .error e => assert false s!"large write error: {e}"

  -- ## liftIO
  let li ← Radix.System.liftIO (pure 42)
  match li with
  | .ok v   => assert (v == 42) "liftIO success"
  | .error _ => assert false "liftIO should succeed"

  -- Cleanup
  IO.FS.removeDirAll tmpDir

  c.get
