import tests.ComprehensiveTests.Framework
import Radix.UTF8

/-!
# UTF-8 Tests
-/

open ComprehensiveTests

namespace UTF8Test

private def scalar (n : Nat) : IO Radix.UTF8.Scalar := do
  match Radix.UTF8.ofNat? n with
  | some s => pure s
  | none => throw (IO.userError s!"invalid scalar {n}")

  private def scalarList (values : List Nat) : IO (List Radix.UTF8.Scalar) :=
    values.mapM scalar

private def byteArray (bytes : List UInt8) : ByteArray :=
  ByteArray.mk bytes.toArray

private def scalarValues (scalars : List Radix.UTF8.Scalar) : List Nat :=
  scalars.map (·.val)

private def graphemeScalarValues (graphemes : List Radix.UTF8.Grapheme) : List (List Nat) :=
  graphemes.map (fun grapheme => scalarValues grapheme.scalars)

private def utf16Values (units : Array UInt16) : List Nat :=
  units.toList.map UInt16.toNat

private def replacementValue : Nat :=
  Radix.UTF8.replacement.val

private def strictReplacementValues (bytes : List UInt8) : List Nat :=
  Radix.UTF8.scalarsToNats (Radix.UTF8.decodeListReplacingMaximalSubparts bytes)

private def hexDigitValue? (c : Char) : Option Nat :=
  match c with
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'A' => some 10
  | 'B' => some 11
  | 'C' => some 12
  | 'D' => some 13
  | 'E' => some 14
  | 'F' => some 15
  | 'a' => some 10
  | 'b' => some 11
  | 'c' => some 12
  | 'd' => some 13
  | 'e' => some 14
  | 'f' => some 15
  | _ => none

private def parseHexNat? (token : String) : Option Nat :=
  token.toList.foldlM (fun acc c => do
    let digit ← hexDigitValue? c
    pure (acc * 16 + digit)) 0

private def stripLineComment (line : String) : String :=
  match line.splitOn "#" with
  | [] => line
  | head :: _ => head

private def graphemeBreakTokens (line : String) : List String :=
  let body := (stripLineComment line).replace "\t" " "
  (body.splitOn " ").filter (fun token => token != "")

private def parseOfficialGraphemeBreakLine
    (lineNumber : Nat)
    (line : String) : Except String (Option (List (List Nat))) := do
  let tokens := graphemeBreakTokens line
  if tokens.isEmpty then
    pure none
  else
    match tokens with
    | [] => pure none
    | "÷" :: rest =>
      let rec go
          (remaining : List String)
          (currentRev : List Nat)
          (clustersRev : List (List Nat)) : Except String (List (List Nat)) := do
        match remaining with
        | [] =>
          if currentRev.isEmpty then
            pure clustersRev.reverse
          else
            throw s!"unterminated grapheme cluster at line {lineNumber}"
        | scalarToken :: boundary :: tail =>
          let scalarValue ←
            match parseHexNat? scalarToken with
            | some value => pure value
            | none => throw s!"invalid scalar token '{scalarToken}' at line {lineNumber}"
          let nextClusterRev := scalarValue :: currentRev
          match boundary with
          | "×" => go tail nextClusterRev clustersRev
          | "÷" => go tail [] (nextClusterRev.reverse :: clustersRev)
          | _ => throw s!"invalid boundary token '{boundary}' at line {lineNumber}"
        | _ => throw s!"dangling token sequence at line {lineNumber}"
      return some (← go rest [] [])
    | first :: _ => throw s!"expected initial break marker at line {lineNumber}, got '{first}'"

private def parseHexNatList? (field : String) : Option (List Nat) := do
  let normalized := (field.replace "\t" " ").trimAscii.toString
  let tokens := (normalized.splitOn " ").filter (fun token => token != "")
  tokens.mapM parseHexNat?

private def parseOfficialCaseFoldingLine
    (lineNumber : Nat)
    (line : String) : Except String (Option (Nat × String × List Nat)) := do
  let body := (stripLineComment line).trimAscii.toString
  if body == "" then
    pure none
  else
    match (body.splitOn ";").map (fun part => part.trimAscii.toString) with
    | sourceField :: statusField :: mappingField :: _ =>
      let source ←
        match parseHexNat? sourceField with
        | some value => pure value
        | none => throw s!"invalid case folding source '{sourceField}' at line {lineNumber}"
      let mapping ←
        match parseHexNatList? mappingField with
        | some values => pure values
        | none => throw s!"invalid case folding mapping '{mappingField}' at line {lineNumber}"
      pure (some (source, statusField, mapping))
    | _ => throw s!"invalid case folding record at line {lineNumber}"

private def parseGeneralCategory?
    (lineNumber : Nat)
    (field : String) : Except String Radix.UTF8.Spec.GeneralCategory := do
  match field.trimAscii.toString with
  | "Lu" => pure .uppercaseLetter
  | "Ll" => pure .lowercaseLetter
  | "Lt" => pure .titlecaseLetter
  | "Lm" => pure .modifierLetter
  | "Lo" => pure .otherLetter
  | "Mn" => pure .nonspacingMark
  | "Mc" => pure .spacingMark
  | "Me" => pure .enclosingMark
  | "Nd" => pure .decimalNumber
  | "Nl" => pure .letterNumber
  | "No" => pure .otherNumber
  | "Pc" => pure .connectorPunctuation
  | "Pd" => pure .dashPunctuation
  | "Ps" => pure .openPunctuation
  | "Pe" => pure .closePunctuation
  | "Pi" => pure .initialPunctuation
  | "Pf" => pure .finalPunctuation
  | "Po" => pure .otherPunctuation
  | "Sm" => pure .mathSymbol
  | "Sc" => pure .currencySymbol
  | "Sk" => pure .modifierSymbol
  | "So" => pure .otherSymbol
  | "Zs" => pure .spaceSeparator
  | "Zl" => pure .lineSeparator
  | "Zp" => pure .paragraphSeparator
  | "Cc" => pure .control
  | "Cf" => pure .format
  | "Cs" => pure .surrogate
  | "Co" => pure .privateUse
  | "Cn" => pure .unassigned
  | other => throw s!"invalid Unicode general category '{other}' at line {lineNumber}"

private def generalCategoryFamily
    (category : Radix.UTF8.Spec.GeneralCategory) : Radix.UTF8.Spec.GeneralCategoryFamily :=
  Radix.UTF8.Spec.GeneralCategory.family category

private def isPrintableGeneralCategory
    (category : Radix.UTF8.Spec.GeneralCategory) : Bool :=
  Radix.UTF8.Spec.GeneralCategory.isPrintable category

private def parseOptionalHexNat
    (lineNumber : Nat)
    (fieldName : String)
    (field : String) : Except String (Option Nat) := do
  let token := field.trimAscii.toString
  if token == "" then
    pure none
  else
    match parseHexNat? token with
    | some value => pure (some value)
    | none => throw s!"invalid {fieldName} '{field}' at line {lineNumber}"

private def parseOfficialUnicodeDataLine
    (lineNumber : Nat)
    (line : String)
  : Except String (Option (Nat × String × Radix.UTF8.Spec.GeneralCategory × Option Nat × Option Nat)) := do
  let body := line.trimAscii.toString
  if body == "" then
    pure none
  else
    let fields := ((body.splitOn ";").map (fun part => part.trimAscii.toString)).toArray
    if fields.size < 14 then
      throw s!"invalid UnicodeData record at line {lineNumber}"
    let codePoint ←
      match parseHexNat? fields[0]! with
      | some value => pure value
      | none => throw s!"invalid UnicodeData code point '{fields[0]!}' at line {lineNumber}"
    let category ← parseGeneralCategory? lineNumber fields[2]!
    let uppercaseMapping ← parseOptionalHexNat lineNumber "uppercase mapping" fields[12]!
    let lowercaseMapping ← parseOptionalHexNat lineNumber "lowercase mapping" fields[13]!
    pure (some (codePoint, fields[1]!, category, uppercaseMapping, lowercaseMapping))

  private def parseOfficialNormalizationLine
      (lineNumber : Nat)
      (line : String)
      : Except String (Option (List Nat × List Nat × List Nat × List Nat × List Nat)) := do
    let body := (stripLineComment line).trimAscii.toString
    if body == "" then
      pure none
    else
      match body.toList.head? with
      | some '@' => pure none
      | _ =>
        match (body.splitOn ";").map (fun part => part.trimAscii.toString) with
        | c1Field :: c2Field :: c3Field :: c4Field :: c5Field :: _ =>
          let c1 ←
            match parseHexNatList? c1Field with
            | some values => pure values
            | none => throw s!"invalid normalization source '{c1Field}' at line {lineNumber}"
          let c2 ←
            match parseHexNatList? c2Field with
            | some values => pure values
            | none => throw s!"invalid NFC field '{c2Field}' at line {lineNumber}"
          let c3 ←
            match parseHexNatList? c3Field with
            | some values => pure values
            | none => throw s!"invalid NFD field '{c3Field}' at line {lineNumber}"
          let c4 ←
            match parseHexNatList? c4Field with
            | some values => pure values
            | none => throw s!"invalid NFKC field '{c4Field}' at line {lineNumber}"
          let c5 ←
            match parseHexNatList? c5Field with
            | some values => pure values
            | none => throw s!"invalid NFKD field '{c5Field}' at line {lineNumber}"
          pure (some (c1, c2, c3, c4, c5))
        | _ => throw s!"invalid normalization record at line {lineNumber}"

private def runOfficialGraphemeBreakTests
    (assert : Bool → String → IO Unit) : IO Unit := do
  let path := "tests/data/unicode/17.0.0/GraphemeBreakTest.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let rec go (remaining : List String) (lineNumber caseCount : Nat) : IO Nat := do
    match remaining with
    | [] => pure caseCount
    | line :: rest =>
      match parseOfficialGraphemeBreakLine lineNumber line with
      | .error err =>
        assert false s!"official grapheme test parse failed: {err}"
        go rest (lineNumber + 1) caseCount
      | .ok none =>
        go rest (lineNumber + 1) caseCount
      | .ok (some expectedClusters) =>
        let flatScalars := expectedClusters.foldr List.append []
        let scalars ← flatScalars.mapM scalar
        let encoded := Radix.UTF8.encodeScalars scalars
        match Radix.UTF8.decodeGraphemes? encoded with
        | some graphemes =>
          let actualClusters := graphemeScalarValues graphemes
          assert (actualClusters == expectedClusters)
            s!"Unicode GraphemeBreakTest mismatch at case {caseCount + 1}: expected {expectedClusters}, got {actualClusters}"
        | none =>
          assert false s!"Unicode GraphemeBreakTest decode failed at case {caseCount + 1}"
        go rest (lineNumber + 1) (caseCount + 1)
  let caseCount ← go lines 1 0
  assert (caseCount == 766) s!"official GraphemeBreakTest case count changed: {caseCount}"

private def runOfficialCaseFoldingTests
    (assert : Bool → String → IO Unit) : IO Unit := do
  let path := "tests/data/unicode/17.0.0/CaseFolding.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let rec go
      (remaining : List String)
      (lineNumber simpleCount fullCount : Nat) : IO (Nat × Nat) := do
    match remaining with
    | [] => pure (simpleCount, fullCount)
    | line :: rest =>
      match parseOfficialCaseFoldingLine lineNumber line with
      | .error err =>
        assert false s!"official case folding parse failed: {err}"
        go rest (lineNumber + 1) simpleCount fullCount
      | .ok none =>
        go rest (lineNumber + 1) simpleCount fullCount
      | .ok (some (source, status, mapping)) =>
        let nextSimpleCount :=
          if status == "C" || status == "S" then simpleCount + 1 else simpleCount
        let nextFullCount :=
          if status == "C" || status == "F" then fullCount + 1 else fullCount
        if status == "C" || status == "S" then
          let actualSimple := Radix.UTF8.CaseFoldingTables.simpleCaseFold? source
          assert (actualSimple == some mapping)
            s!"Unicode CaseFolding simple table mismatch at line {lineNumber} for U+{Nat.toDigits 16 source |> String.ofList}: expected {mapping}, got {actualSimple}"
          match Radix.UTF8.ofNat? source, mapping with
          | some sourceScalar, [mappedValue] =>
            match Radix.UTF8.ofNat? mappedValue with
            | some mappedScalar =>
              assert (Radix.UTF8.caseFoldSimple sourceScalar == mappedScalar)
                s!"Unicode CaseFolding direct simple fold mismatch at line {lineNumber} for U+{Nat.toDigits 16 source |> String.ofList}"
            | none =>
              assert false s!"invalid direct simple fold target at line {lineNumber}: {mapping}"
          | _, _ => pure ()
        if status == "C" || status == "F" then
          let actualFull := Radix.UTF8.CaseFoldingTables.fullCaseFold? source
          assert (actualFull == some mapping)
            s!"Unicode CaseFolding full table mismatch at line {lineNumber} for U+{Nat.toDigits 16 source |> String.ofList}: expected {mapping}, got {actualFull}"
        go rest (lineNumber + 1) nextSimpleCount nextFullCount
  let (simpleCount, fullCount) ← go lines 1 0 0
  assert (simpleCount == 1512) s!"official simple case folding count changed: {simpleCount}"
  assert (fullCount == 1585) s!"official full case folding count changed: {fullCount}"

private def runOfficialUnicodeDataTests
    (assert : Bool → String → IO Unit) : IO Unit := do
  let path := "tests/data/unicode/17.0.0/UnicodeData.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"

  let verifyCategoryRange
      (startValue endValue : Nat)
      (expectedCategory : Radix.UTF8.Spec.GeneralCategory)
      (lineNumber : Nat) : IO Unit := do
    let rec loop (fuel current : Nat) : IO Unit := do
      match fuel with
      | 0 => pure ()
      | fuel + 1 => do
        match Radix.UTF8.ofNat? current with
        | some scalar =>
          assert (Radix.UTF8.Spec.classifyCategory scalar == expectedCategory)
            s!"UnicodeData broad-category mismatch in range at line {lineNumber} for U+{Nat.toDigits 16 current |> String.ofList}"
        | none => pure ()
        loop fuel (current + 1)
    loop (endValue + 1 - startValue) startValue

  let rec go
      (remaining : List String)
      (lineNumber : Nat)
      (pendingRange : Option (Nat × Radix.UTF8.Spec.GeneralCategory))
      (lowercaseCount uppercaseCount : Nat) : IO (Nat × Nat) := do
    match remaining with
    | [] =>
      match pendingRange with
      | some _ =>
        assert false "UnicodeData range start without matching end"
        pure (lowercaseCount, uppercaseCount)
      | none => pure (lowercaseCount, uppercaseCount)
    | line :: rest =>
      match parseOfficialUnicodeDataLine lineNumber line with
      | .error err =>
        assert false s!"official UnicodeData parse failed: {err}"
        go rest (lineNumber + 1) pendingRange lowercaseCount uppercaseCount
      | .ok none =>
        go rest (lineNumber + 1) pendingRange lowercaseCount uppercaseCount
      | .ok (some (codePoint, name, category, uppercaseMapping, lowercaseMapping)) =>
        if name.endsWith ", First>" then
          match pendingRange with
          | some _ =>
            assert false s!"nested UnicodeData range start at line {lineNumber}"
            go rest (lineNumber + 1) pendingRange lowercaseCount uppercaseCount
          | none =>
            go rest (lineNumber + 1) (some (codePoint, category)) lowercaseCount uppercaseCount
        else if name.endsWith ", Last>" then
          match pendingRange with
          | some (startValue, startCategory) =>
            assert (startCategory == category)
              s!"UnicodeData broad-category range mismatch at line {lineNumber}"
            verifyCategoryRange startValue codePoint category lineNumber
            go rest (lineNumber + 1) none lowercaseCount uppercaseCount
          | none =>
            assert false s!"UnicodeData range end without start at line {lineNumber}"
            go rest (lineNumber + 1) none lowercaseCount uppercaseCount
        else
          match pendingRange with
          | some _ =>
            assert false s!"UnicodeData range start not closed before line {lineNumber}"
            go rest (lineNumber + 1) none lowercaseCount uppercaseCount
          | none =>
            let nextLowercaseCount := if lowercaseMapping.isSome then lowercaseCount + 1 else lowercaseCount
            let nextUppercaseCount := if uppercaseMapping.isSome then uppercaseCount + 1 else uppercaseCount
            match Radix.UTF8.ofNat? codePoint with
            | some scalar =>
              assert (Radix.UTF8.Spec.classifyCategory scalar == category)
                s!"UnicodeData general-category mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              let expectedFamily := UTF8Test.generalCategoryFamily category
              assert (Radix.UTF8.Spec.classifyCategoryFamily scalar == expectedFamily)
                s!"UnicodeData general-category family mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              let expectsUppercase := category == .uppercaseLetter
              let expectsLowercase := category == .lowercaseLetter
              let expectsDigit := category == .decimalNumber
              assert (Radix.UTF8.Spec.Scalar.isUppercase scalar == expectsUppercase)
                s!"UnicodeData uppercase predicate mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              assert (Radix.UTF8.Spec.Scalar.isLowercase scalar == expectsLowercase)
                s!"UnicodeData lowercase predicate mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              assert (Radix.UTF8.Spec.Scalar.isDigit scalar == expectsDigit)
                s!"UnicodeData decimal-digit predicate mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              assert (Radix.UTF8.Spec.Scalar.isAlpha scalar == (expectedFamily == .letter))
                s!"UnicodeData alpha predicate mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              assert (Radix.UTF8.Spec.Scalar.isPrintable scalar == UTF8Test.isPrintableGeneralCategory category)
                s!"UnicodeData printable predicate mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              match lowercaseMapping with
              | some mappedValue =>
                match Radix.UTF8.ofNat? mappedValue with
                | some mappedScalar =>
                  assert (Radix.UTF8.toLowerSimple scalar == mappedScalar)
                    s!"UnicodeData simple lowercase mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
                | none =>
                  assert false s!"invalid UnicodeData lowercase mapping at line {lineNumber}: U+{Nat.toDigits 16 mappedValue |> String.ofList}"
              | none =>
                assert (Radix.UTF8.toLowerSimple scalar == scalar)
                  s!"UnicodeData lowercase identity mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
              match uppercaseMapping with
              | some mappedValue =>
                match Radix.UTF8.ofNat? mappedValue with
                | some mappedScalar =>
                  assert (Radix.UTF8.toUpperSimple scalar == mappedScalar)
                    s!"UnicodeData simple uppercase mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
                | none =>
                  assert false s!"invalid UnicodeData uppercase mapping at line {lineNumber}: U+{Nat.toDigits 16 mappedValue |> String.ofList}"
              | none =>
                assert (Radix.UTF8.toUpperSimple scalar == scalar)
                  s!"UnicodeData uppercase identity mismatch at line {lineNumber} for U+{Nat.toDigits 16 codePoint |> String.ofList}"
            | none => pure ()
            go rest (lineNumber + 1) none nextLowercaseCount nextUppercaseCount

  let (lowercaseCount, uppercaseCount) ← go lines 1 none 0 0
  assert (lowercaseCount == 1488) s!"official UnicodeData lowercase mapping count changed: {lowercaseCount}"
  assert (uppercaseCount == 1505) s!"official UnicodeData uppercase mapping count changed: {uppercaseCount}"

  for sample in [0x0378, 0x0380, 0x0381] do
    match Radix.UTF8.ofNat? sample with
    | some scalar =>
      assert (Radix.UTF8.Spec.classifyCategory scalar == .unassigned)
        s!"UnicodeData gap sample should classify as unassigned: U+{Nat.toDigits 16 sample |> String.ofList}"
    | none => pure ()

private def runOfficialNormalizationTests
    (assert : Bool → String → IO Unit) : IO Unit := do
  let path := "tests/data/unicode/17.0.0/NormalizationTest.txt"
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n"
  let rec go (remaining : List String) (lineNumber caseCount : Nat) : IO Nat := do
    match remaining with
    | [] => pure caseCount
    | line :: rest =>
      match parseOfficialNormalizationLine lineNumber line with
      | .error err =>
        assert false s!"official normalization parse failed: {err}"
        go rest (lineNumber + 1) caseCount
      | .ok none =>
        go rest (lineNumber + 1) caseCount
      | .ok (some (c1, c2, c3, c4, c5)) =>
        let sourceScalars ← scalarList c1
        let nfcScalars ← scalarList c2
        let nfdScalars ← scalarList c3
        let nfkcScalars ← scalarList c4
        let nfkdScalars ← scalarList c5
        let actualNFCSource := scalarValues (Radix.UTF8.normalizeScalarsNFC sourceScalars)
        let actualNFCNFC := scalarValues (Radix.UTF8.normalizeScalarsNFC nfcScalars)
        let actualNFCNFD := scalarValues (Radix.UTF8.normalizeScalarsNFC nfdScalars)
        let actualNFCNFKC := scalarValues (Radix.UTF8.normalizeScalarsNFC nfkcScalars)
        let actualNFCNFKD := scalarValues (Radix.UTF8.normalizeScalarsNFC nfkdScalars)
        let actualNFDSource := scalarValues (Radix.UTF8.normalizeScalarsNFD sourceScalars)
        let actualNFDNFC := scalarValues (Radix.UTF8.normalizeScalarsNFD nfcScalars)
        let actualNFDNFD := scalarValues (Radix.UTF8.normalizeScalarsNFD nfdScalars)
        let actualNFDNFKC := scalarValues (Radix.UTF8.normalizeScalarsNFD nfkcScalars)
        let actualNFDNFKD := scalarValues (Radix.UTF8.normalizeScalarsNFD nfkdScalars)
        let actualNFKCSource := scalarValues (Radix.UTF8.normalizeScalarsNFKC sourceScalars)
        let actualNFKCNFC := scalarValues (Radix.UTF8.normalizeScalarsNFKC nfcScalars)
        let actualNFKCNFD := scalarValues (Radix.UTF8.normalizeScalarsNFKC nfdScalars)
        let actualNFKCNFKC := scalarValues (Radix.UTF8.normalizeScalarsNFKC nfkcScalars)
        let actualNFKCNFKD := scalarValues (Radix.UTF8.normalizeScalarsNFKC nfkdScalars)
        let actualNFKDSource := scalarValues (Radix.UTF8.normalizeScalarsNFKD sourceScalars)
        let actualNFKDNFC := scalarValues (Radix.UTF8.normalizeScalarsNFKD nfcScalars)
        let actualNFKDNFD := scalarValues (Radix.UTF8.normalizeScalarsNFKD nfdScalars)
        let actualNFKDNFKC := scalarValues (Radix.UTF8.normalizeScalarsNFKD nfkcScalars)
        let actualNFKDNFKD := scalarValues (Radix.UTF8.normalizeScalarsNFKD nfkdScalars)

        assert (actualNFCSource == c2 && actualNFCNFC == c2 && actualNFCNFD == c2)
          s!"NormalizationTest NFC invariant failed at case {caseCount + 1}"
        assert (actualNFCNFKC == c4 && actualNFCNFKD == c4)
          s!"NormalizationTest NFC compatibility invariant failed at case {caseCount + 1}"
        assert (actualNFDSource == c3 && actualNFDNFC == c3 && actualNFDNFD == c3)
          s!"NormalizationTest NFD invariant failed at case {caseCount + 1}"
        assert (actualNFDNFKC == c5 && actualNFDNFKD == c5)
          s!"NormalizationTest NFD compatibility invariant failed at case {caseCount + 1}"
        assert (actualNFKCSource == c4 && actualNFKCNFC == c4 && actualNFKCNFD == c4 &&
            actualNFKCNFKC == c4 && actualNFKCNFKD == c4)
          s!"NormalizationTest NFKC invariant failed at case {caseCount + 1}"
        assert (actualNFKDSource == c5 && actualNFKDNFC == c5 && actualNFKDNFD == c5 &&
            actualNFKDNFKC == c5 && actualNFKDNFKD == c5)
          s!"NormalizationTest NFKD invariant failed at case {caseCount + 1}"

        go rest (lineNumber + 1) (caseCount + 1)
  let caseCount ← go lines 1 0
  assert (caseCount > 0) "official normalization corpus should contain at least one case"

private def runUTF8CursorTests
    (assert : Bool → String → IO Unit)
    (ascii twoByte threeByte fourByte : Radix.UTF8.Scalar) : IO Unit := do
  let cursorInput := Radix.UTF8.encodeScalars [ascii, twoByte, threeByte, fourByte]
  let cursor0 := Radix.UTF8.Cursor.init cursorInput
  assert (Radix.UTF8.Cursor.byteOffset cursor0 == 0) "cursor starts at offset zero"
  assert ((Radix.UTF8.Cursor.current? cursor0).map (·.val) == some 0x41)
    "cursor current? reads first scalar"

  let cursor1 ←
    match Radix.UTF8.Cursor.advance? cursor0 with
    | some (s0, cursor1) => do
      assert (s0.val == 0x41) "cursor advance decodes first ASCII scalar"
      assert (Radix.UTF8.Cursor.byteOffset cursor1 == 1) "cursor advance moves by ASCII width"
      pure cursor1
    | none => do
      assert false "cursor failed on first scalar"
      pure cursor0
  let cursor2 ←
    match Radix.UTF8.Cursor.advance? cursor1 with
    | some (s1, cursor2) => do
      assert (s1.val == 0x00A2) "cursor advance decodes second scalar"
      assert (Radix.UTF8.Cursor.byteOffset cursor2 == 3) "cursor advance moves by two-byte width"
      pure cursor2
    | none => do
      assert false "cursor failed on second scalar"
      pure cursor1
  let cursor3 ←
    match Radix.UTF8.Cursor.advance? cursor2 with
    | some (s2, cursor3) => do
      assert (s2.val == 0x20AC) "cursor advance decodes third scalar"
      assert (Radix.UTF8.Cursor.byteOffset cursor3 == 6) "cursor advance moves by three-byte width"
      pure cursor3
    | none => do
      assert false "cursor failed on third scalar"
      pure cursor2
  let cursor4 ←
    match Radix.UTF8.Cursor.advance? cursor3 with
    | some (s3, cursor4) => do
      assert (s3.val == 0x1F642) "cursor advance decodes fourth scalar"
      assert (Radix.UTF8.Cursor.byteOffset cursor4 == 10) "cursor reaches end after final scalar"
      pure cursor4
    | none => do
      assert false "cursor failed on fourth scalar"
      pure cursor3
  assert (Radix.UTF8.Cursor.advance? cursor4 == none) "cursor cannot advance past end"

  assert (Radix.UTF8.decodeWithCursor? cursorInput == Radix.UTF8.decodeBytes? cursorInput)
    "decodeWithCursor? matches decodeBytes? on valid input"

  match Radix.UTF8.Cursor.atOffset? cursorInput 0 with
  | some cursor => assert (Radix.UTF8.Cursor.byteOffset cursor == 0) "Cursor.atOffset? accepts start boundary"
  | none => assert false "Cursor.atOffset? rejected start boundary"
  match Radix.UTF8.Cursor.atOffset? cursorInput 1 with
  | some cursor => assert ((Radix.UTF8.Cursor.current? cursor).map (·.val) == some 0x00A2) "Cursor.atOffset? accepts next scalar boundary"
  | none => assert false "Cursor.atOffset? rejected valid second boundary"
  assert (Radix.UTF8.Cursor.atOffset? cursorInput 2 == none) "Cursor.atOffset? rejects interior continuation offset"
  match Radix.UTF8.Cursor.atOffset? cursorInput 10 with
  | some cursor => assert (Radix.UTF8.Cursor.byteOffset cursor == 10) "Cursor.atOffset? accepts end boundary"
  | none => assert false "Cursor.atOffset? rejected end boundary"
  assert (Radix.UTF8.Cursor.atOffset? cursorInput 11 == none)
    "Cursor.atOffset? rejects out-of-range offset"

  let cursorMalformed := UTF8Test.byteArray [0xE1, 0x80, 0x41]
  let malformedCursor0 := Radix.UTF8.Cursor.init cursorMalformed
  assert (Radix.UTF8.Cursor.current? malformedCursor0 == none) "cursor current? rejects malformed prefix"
  match Radix.UTF8.Cursor.currentError? malformedCursor0 with
  | some err => do
    assert (err.kind == Radix.UTF8.Spec.DecodeErrorKind.invalidContinuationByte)
      "cursor currentError? reports invalid continuation kind"
    assert (err.consumed == 2) "cursor currentError? reports maximal subpart width"
  | none => assert false "cursor currentError? missing malformed prefix error"
  assert (Radix.UTF8.decodeWithCursor? cursorMalformed == none)
    "decodeWithCursor? rejects malformed input"

  let perByteCursorValues :=
    Radix.UTF8.decodeWithCursorReplacing .perByte cursorMalformed |>.map (·.val)
  assert (perByteCursorValues == [UTF8Test.replacementValue, UTF8Test.replacementValue, 0x41])
    "cursor per-byte replacement matches legacy semantics"

  let maximalCursorValues :=
    Radix.UTF8.decodeWithCursorReplacing .maximalSubpart cursorMalformed |>.map (·.val)
  assert (maximalCursorValues == [UTF8Test.replacementValue, 0x41])
    "cursor maximal-subpart replacement collapses malformed prefix"

  let laterUTF8Error := UTF8Test.byteArray [0x41, 0xE1, 0x80]
  assert (Radix.UTF8.firstDecodeErrorBytes? laterUTF8Error ==
    some { kind := .truncatedSequence, expectedLength := 3, consumed := 2 })
    "firstDecodeErrorBytes? scans past valid prefixes to report the first later UTF-8 error"

  match Radix.UTF8.Cursor.advanceReplacing .maximalSubpart malformedCursor0 with
  | some (replacementScalar, malformedCursor1) => do
    assert (replacementScalar.val == UTF8Test.replacementValue)
      "cursor maximal-subpart replacement returns replacement scalar"
    assert (Radix.UTF8.Cursor.byteOffset malformedCursor1 == 2)
      "cursor maximal-subpart replacement advances by maximal subpart length"
    match Radix.UTF8.Cursor.advanceReplacing .maximalSubpart malformedCursor1 with
    | some (asciiScalar, malformedCursor2) => do
      assert (asciiScalar.val == 0x41) "cursor resumes at ASCII successor after replacement"
      assert (Radix.UTF8.Cursor.byteOffset malformedCursor2 == 3) "cursor reaches end after successor scalar"
    | none => assert false "cursor failed to resume after maximal-subpart replacement"
  | none => assert false "cursor maximal-subpart replacement failed on malformed prefix"

private def runUTF8GraphemeTests
    (assert : Bool → String → IO Unit)
    (ascii : Radix.UTF8.Scalar) : IO Unit := do
  let acute ← UTF8Test.scalar 0x0301
  let letterB ← UTF8Test.scalar 0x42
  let carriageReturn ← UTF8Test.scalar 0x000D
  let lineFeed ← UTF8Test.scalar 0x000A
  let hangulL ← UTF8Test.scalar 0x1100
  let hangulV ← UTF8Test.scalar 0x1161
  let hangulT ← UTF8Test.scalar 0x11A8
  let hangulLV ← UTF8Test.scalar 0xAC00
  let regionalA ← UTF8Test.scalar 0x1F1E6
  let regionalB ← UTF8Test.scalar 0x1F1E7
  let regionalC ← UTF8Test.scalar 0x1F1E8
  let thumbsUp ← UTF8Test.scalar 0x1F44D
  let mediumSkinTone ← UTF8Test.scalar 0x1F3FD
  let man ← UTF8Test.scalar 0x1F468
  let woman ← UTF8Test.scalar 0x1F469
  let girl ← UTF8Test.scalar 0x1F467
  let boy ← UTF8Test.scalar 0x1F466
  let redHeart ← UTF8Test.scalar 0x2764
  let variationSelector16 ← UTF8Test.scalar 0xFE0F
  let fire ← UTF8Test.scalar 0x1F525
  let zwj ← UTF8Test.scalar 0x200D
  let arabicNumberSign ← UTF8Test.scalar 0x0600
  let devanagariKa ← UTF8Test.scalar 0x0915
  let devanagariNukta ← UTF8Test.scalar 0x093C
  let devanagariVowelAa ← UTF8Test.scalar 0x093E
  let devanagariVirama ← UTF8Test.scalar 0x094D
  let byteOrderMark ← UTF8Test.scalar 0xFEFF

  let combiningInput := Radix.UTF8.encodeScalars [ascii, acute, letterB]
  match Radix.UTF8.decodeGraphemes? combiningInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x41, 0x0301], [0x42]])
      "grapheme decode groups base + combining mark"
    match graphemes with
    | [first, second] =>
      assert (Radix.UTF8.Grapheme.byteLength first == 3) "first grapheme spans base + combining bytes"
      assert (Radix.UTF8.Grapheme.byteLength second == 1) "second grapheme spans trailing ASCII byte"
      assert (first.startOffset == 0 && first.endOffset == 3) "first grapheme offsets are correct"
      assert (second.startOffset == 3 && second.endOffset == 4) "second grapheme offsets are correct"
    | _ => assert false "unexpected grapheme decomposition for combining input"
  | none => assert false "grapheme decode rejected valid combining-mark input"

  let crlfInput := Radix.UTF8.encodeScalars [carriageReturn, lineFeed, ascii]
  match Radix.UTF8.decodeGraphemes? crlfInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x000D, 0x000A], [0x41]])
      "grapheme decode keeps CRLF in one cluster"
  | none => assert false "grapheme decode rejected valid CRLF input"

  let hangulInput := Radix.UTF8.encodeScalars [hangulL, hangulV, hangulT, ascii]
  match Radix.UTF8.decodeGraphemes? hangulInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x1100, 0x1161, 0x11A8], [0x41]])
      "grapheme decode groups Hangul jamo LVT sequence"
  | none => assert false "grapheme decode rejected valid Hangul jamo input"

  let precomposedHangulInput := Radix.UTF8.encodeScalars [hangulLV, hangulT, ascii]
  match Radix.UTF8.decodeGraphemes? precomposedHangulInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0xAC00, 0x11A8], [0x41]])
      "grapheme decode groups precomposed Hangul LV with trailing T"
  | none => assert false "grapheme decode rejected valid precomposed Hangul input"

  let regionalInput := Radix.UTF8.encodeScalars [regionalA, regionalB, regionalC]
  match Radix.UTF8.decodeGraphemes? regionalInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x1F1E6, 0x1F1E7], [0x1F1E8]])
      "grapheme decode pairs regional indicators"
    assert (Radix.UTF8.graphemeCount? regionalInput == some 2) "graphemeCount? matches regional-indicator pairing"
  | none => assert false "grapheme decode rejected valid regional-indicator input"

  let emojiModifierInput := Radix.UTF8.encodeScalars [thumbsUp, mediumSkinTone, ascii]
  match Radix.UTF8.decodeGraphemes? emojiModifierInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x1F44D, 0x1F3FD], [0x41]])
      "grapheme decode keeps emoji modifier sequences in one cluster"
  | none => assert false "grapheme decode rejected valid emoji modifier input"

  let familyInput := Radix.UTF8.encodeScalars [man, zwj, woman, zwj, girl, zwj, boy, ascii]
  match Radix.UTF8.decodeGraphemes? familyInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x1F468, 0x200D, 0x1F469, 0x200D, 0x1F467, 0x200D, 0x1F466], [0x41]])
      "grapheme decode keeps emoji family ZWJ sequences in one cluster"
    assert (Radix.UTF8.graphemeCount? familyInput == some 2)
      "graphemeCount? treats emoji family ZWJ sequence as one cluster"
  | none => assert false "grapheme decode rejected valid emoji family input"

  let heartOnFireInput := Radix.UTF8.encodeScalars [redHeart, variationSelector16, zwj, fire]
  match Radix.UTF8.decodeGraphemes? heartOnFireInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x2764, 0xFE0F, 0x200D, 0x1F525]])
      "grapheme decode keeps emoji variation-selector ZWJ sequences in one cluster"
  | none => assert false "grapheme decode rejected valid emoji variation-selector input"

  let prependInput := Radix.UTF8.encodeScalars [arabicNumberSign, ascii]
  match Radix.UTF8.decodeGraphemes? prependInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x0600, 0x41]])
      "grapheme decode applies Unicode Prepend characters before the following base"
  | none => assert false "grapheme decode rejected valid Prepend input"

  let spacingMarkInput := Radix.UTF8.encodeScalars [devanagariKa, devanagariVowelAa, ascii]
  match Radix.UTF8.decodeGraphemes? spacingMarkInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x0915, 0x093E], [0x41]])
      "grapheme decode keeps Unicode SpacingMark vowels in the same cluster"
  | none => assert false "grapheme decode rejected valid SpacingMark input"

  let indicConjunctInput := Radix.UTF8.encodeScalars [devanagariKa, devanagariNukta, devanagariVirama, devanagariKa, ascii]
  match Radix.UTF8.decodeGraphemes? indicConjunctInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0x0915, 0x093C, 0x094D, 0x0915], [0x41]])
      "grapheme decode keeps Indic virama conjuncts in one cluster under GB9c"
  | none => assert false "grapheme decode rejected valid Indic conjunct input"

  let controlInput := Radix.UTF8.encodeScalars [byteOrderMark, ascii]
  match Radix.UTF8.decodeGraphemes? controlInput with
  | some graphemes =>
    assert (UTF8Test.graphemeScalarValues graphemes == [[0xFEFF], [0x41]])
      "grapheme decode breaks around Unicode control-property scalars outside ASCII"
  | none => assert false "grapheme decode rejected valid control-property input"

  let graphemeCursor := Radix.UTF8.Cursor.init combiningInput
  match Radix.UTF8.Cursor.currentGrapheme? graphemeCursor with
  | some grapheme =>
    assert (UTF8Test.scalarValues grapheme.scalars == [0x41, 0x0301])
      "currentGrapheme? inspects first grapheme"
  | none => assert false "currentGrapheme? failed on valid combining-mark input"
  match Radix.UTF8.Cursor.advanceGrapheme? graphemeCursor with
  | some (first, cursor1) =>
    assert (UTF8Test.scalarValues first.scalars == [0x41, 0x0301])
      "advanceGrapheme? returns first grapheme"
    assert (Radix.UTF8.Cursor.byteOffset cursor1 == 3) "advanceGrapheme? moves to the next grapheme boundary"
    match Radix.UTF8.Cursor.currentGrapheme? cursor1 with
    | some second =>
      assert (UTF8Test.scalarValues second.scalars == [0x42])
        "currentGrapheme? sees the second grapheme after advancing"
    | none => assert false "currentGrapheme? failed after grapheme advance"
  | none => assert false "advanceGrapheme? failed on valid combining-mark input"

  match Radix.UTF8.Cursor.advanceGrapheme? (Radix.UTF8.Cursor.init familyInput) with
  | some (familyGrapheme, familyCursor) =>
    assert (UTF8Test.scalarValues familyGrapheme.scalars == [0x1F468, 0x200D, 0x1F469, 0x200D, 0x1F467, 0x200D, 0x1F466])
      "advanceGrapheme? returns the full emoji family cluster"
    assert (Radix.UTF8.Cursor.byteOffset familyCursor == familyInput.size - 1)
      "advanceGrapheme? advances past the full emoji family cluster"
  | none => assert false "advanceGrapheme? failed on valid emoji family input"

  let malformedGraphemeInput := UTF8Test.byteArray [0xE1, 0x80, 0x41, 0xCC, 0x81]
  let replacedGraphemes := Radix.UTF8.decodeGraphemesReplacing .maximalSubpart malformedGraphemeInput
  assert (UTF8Test.graphemeScalarValues replacedGraphemes ==
    [[UTF8Test.replacementValue], [0x41, 0x0301]])
    "replacement-aware grapheme decode preserves following combining cluster"
  match Radix.UTF8.Cursor.currentGraphemeReplacing .maximalSubpart (Radix.UTF8.Cursor.init malformedGraphemeInput) with
  | some grapheme =>
    assert (UTF8Test.scalarValues grapheme.scalars == [UTF8Test.replacementValue])
      "currentGraphemeReplacing inspects replacement cluster"
  | none => assert false "currentGraphemeReplacing failed on malformed input"

private def runUTF16InteropTests
    (assert : Bool → String → IO Unit)
    (ascii threeByte fourByte : Radix.UTF8.Scalar) : IO Unit := do
  let musicalSymbol ← UTF8Test.scalar 0x1D11E

  assert (Radix.UTF8.encodeScalarToUTF16List ascii == [0x0041])
    "UTF-16 encodes ASCII as one code unit"
  assert (Radix.UTF8.encodeScalarToUTF16List threeByte == [0x20AC])
    "UTF-16 encodes BMP scalar as one code unit"
  assert (Radix.UTF8.encodeScalarToUTF16List fourByte == [0xD83D, 0xDE42])
    "UTF-16 encodes supplementary scalar as surrogate pair"
  assert (Radix.UTF8.encodeScalarToUTF16List musicalSymbol == [0xD834, 0xDD1E])
    "UTF-16 encodes U+1D11E as the expected surrogate pair"

  let utf16Input := Radix.UTF8.encodeScalarsToUTF16 [ascii, threeByte, fourByte]
  assert (UTF8Test.utf16Values utf16Input == [0x0041, 0x20AC, 0xD83D, 0xDE42])
    "UTF-16 array encoding preserves code-unit order"
  assert (Radix.UTF8.decodeUTF16? utf16Input == some [ascii, threeByte, fourByte])
    "UTF-16 strict decode round-trips encoded scalars"
  assert (Radix.UTF8.utf16ScalarCount? utf16Input == some 3)
    "utf16ScalarCount? counts decoded scalars"

  match Radix.UTF8.decodeNextUTF16ListStep? [0xDC00] with
  | some (.error err) =>
    assert (err.kind == .unexpectedLowSurrogate) "UTF-16 reports unexpected low surrogate"
    assert (err.consumed == 1) "UTF-16 unexpected low surrogate consumes one unit"
  | _ => assert false "UTF-16 missing unexpected low surrogate error"

  match Radix.UTF8.decodeNextUTF16ListStep? [0xD800] with
  | some (.error err) =>
    assert (err.kind == .truncatedHighSurrogate) "UTF-16 reports truncated high surrogate"
    assert (err.expectedLength == 2) "UTF-16 truncated high surrogate expects two units"
  | _ => assert false "UTF-16 missing truncated high surrogate error"

  match Radix.UTF8.decodeNextUTF16ListStep? [0xD800, 0x0041] with
  | some (.error err) =>
    assert (err.kind == .invalidLowSurrogate) "UTF-16 reports invalid low surrogate"
    assert (err.consumed == 1) "UTF-16 invalid low surrogate consumes one unit"
  | _ => assert false "UTF-16 missing invalid low surrogate error"

  assert (Radix.UTF8.firstUTF16DecodeErrorList? [0xD800, 0x0041] ==
    some { kind := Radix.UTF8.UTF16DecodeErrorKind.invalidLowSurrogate, expectedLength := 2, consumed := 1 })
    "firstUTF16DecodeErrorList? matches detailed step"

  assert (Radix.UTF8.firstUTF16DecodeErrorList? [0x0041, 0xD800, 0x0041] ==
    some { kind := Radix.UTF8.UTF16DecodeErrorKind.invalidLowSurrogate, expectedLength := 2, consumed := 1 })
    "firstUTF16DecodeErrorList? scans past valid prefixes to report the first later UTF-16 error"
  assert (Radix.UTF8.firstUTF16DecodeError? #[0x0041, 0xDFFF] ==
    some { kind := Radix.UTF8.UTF16DecodeErrorKind.unexpectedLowSurrogate, expectedLength := 1, consumed := 1 })
    "firstUTF16DecodeError? reports later low-surrogate errors in arrays"

  let malformedUTF16 : Array UInt16 := #[0xD800, 0x0041, 0xDFFF, 0xD83D, 0xDE42]
  let replacedUTF16 := Radix.UTF8.decodeUTF16Replacing malformedUTF16
  assert (UTF8Test.scalarValues replacedUTF16 == [UTF8Test.replacementValue, 0x41, UTF8Test.replacementValue, 0x1F642])
    "UTF-16 replacement decode replaces each malformed surrogate use and resyncs"

  match Radix.UTF8.transcodeUTF16ToUTF8? utf16Input with
  | some utf8Bytes =>
    assert (Radix.UTF8.decodeBytes? utf8Bytes == some [ascii, threeByte, fourByte])
      "UTF-16 to UTF-8 transcoding round-trips valid input"
  | none => assert false "strict UTF-16 to UTF-8 transcoding failed on valid input"

  let transcodedReplacing := Radix.UTF8.transcodeUTF16ToUTF8Replacing malformedUTF16
  assert (Radix.UTF8.decodeBytes? transcodedReplacing == some replacedUTF16)
    "UTF-16 replacement transcoding emits well-formed UTF-8 for replacement decode"

  let utf8Input := Radix.UTF8.encodeScalars [ascii, musicalSymbol, fourByte]
  match Radix.UTF8.transcodeUTF8ToUTF16? utf8Input with
  | some utf16Units =>
    assert (UTF8Test.utf16Values utf16Units == [0x0041, 0xD834, 0xDD1E, 0xD83D, 0xDE42])
      "UTF-8 to UTF-16 transcoding preserves surrogate pairs"
  | none => assert false "strict UTF-8 to UTF-16 transcoding failed on valid input"

  let malformedUTF8 := UTF8Test.byteArray [0xE1, 0x80, 0x41]
  let utf16Replacing := Radix.UTF8.transcodeUTF8ToUTF16Replacing .maximalSubpart malformedUTF8
  assert (UTF8Test.utf16Values utf16Replacing == [0xFFFD, 0x0041])
    "UTF-8 replacement transcoding produces UTF-16 replacement code units"

private def runUTF8TextOpTests
    (assert : Bool → String → IO Unit)
    (ascii twoByte threeByte fourByte : Radix.UTF8.Scalar) : IO Unit := do
  let scalarInput := Radix.UTF8.encodeScalars [ascii, twoByte, threeByte, fourByte]
  assert (Radix.UTF8.scalarBoundaryOffsets? scalarInput == some [0, 1, 3, 6, 10])
    "scalarBoundaryOffsets? reports all scalar starts and final end"
  assert (Radix.UTF8.byteOffsetOfScalarIndex? scalarInput 2 == some 3)
    "byteOffsetOfScalarIndex? resolves scalar boundary"
  assert ((Radix.UTF8.scalarAtIndex? scalarInput 1).map (·.val) == some 0x00A2)
    "scalarAtIndex? returns the scalar at the requested index"

  match Radix.UTF8.sliceBytes? scalarInput 1 6 with
  | some sliced =>
    assert (Radix.UTF8.decodeBytes? sliced == some [twoByte, threeByte])
      "sliceBytes? extracts a boundary-safe byte range"
  | none => assert false "sliceBytes? rejected valid scalar boundaries"
  assert (Radix.UTF8.sliceBytes? scalarInput 2 6 == none)
    "sliceBytes? rejects continuation-byte start offsets"
  match Radix.UTF8.sliceScalars? scalarInput 1 3 with
  | some sliced =>
    assert (Radix.UTF8.decodeBytes? sliced == some [twoByte, threeByte])
      "sliceScalars? extracts the requested scalar range"
  | none => assert false "sliceScalars? rejected valid scalar indices"

  let scalarNeedle := Radix.UTF8.encodeScalars [twoByte, threeByte]
  assert (Radix.UTF8.startsWithScalars scalarInput (Radix.UTF8.encodeScalars [ascii, twoByte]))
    "startsWithScalars accepts scalar-aligned prefix"
  assert (Radix.UTF8.endsWithScalars scalarInput (Radix.UTF8.encodeScalars [threeByte, fourByte]))
    "endsWithScalars accepts scalar-aligned suffix"
  assert (Radix.UTF8.findScalars? scalarInput scalarNeedle == some 1)
    "findScalars? returns the byte offset of the first scalar match"
  assert (Radix.UTF8.containsScalars scalarInput scalarNeedle)
    "containsScalars reports scalar-sequence containment"

  let acute ← UTF8Test.scalar 0x0301
  let letterB ← UTF8Test.scalar 0x42
  let graphemeInput := Radix.UTF8.encodeScalars [ascii, acute, letterB, ascii, acute]
  assert (Radix.UTF8.graphemeBoundaryOffsets? graphemeInput == some [0, 3, 4, 7])
    "graphemeBoundaryOffsets? reports grapheme boundaries and final end"
  assert (Radix.UTF8.byteOffsetOfGraphemeIndex? graphemeInput 2 == some 4)
    "byteOffsetOfGraphemeIndex? resolves grapheme boundary"
  match Radix.UTF8.graphemeAtIndex? graphemeInput 0 with
  | some grapheme =>
    assert (UTF8Test.scalarValues grapheme.scalars == [0x41, 0x0301])
      "graphemeAtIndex? returns the grapheme at the requested index"
  | none => assert false "graphemeAtIndex? rejected valid grapheme index"
  match Radix.UTF8.sliceGraphemes? graphemeInput 0 1 with
  | some sliced =>
    match Radix.UTF8.decodeGraphemes? sliced with
    | some graphemes =>
      assert (UTF8Test.graphemeScalarValues graphemes == [[0x41, 0x0301]])
        "sliceGraphemes? extracts the requested grapheme range"
    | none => assert false "sliceGraphemes? returned non-decodable UTF-8"
  | none => assert false "sliceGraphemes? rejected valid grapheme indices"

  let graphemeNeedle := Radix.UTF8.encodeScalars [letterB, ascii, acute]
  assert (Radix.UTF8.startsWithGraphemes graphemeInput (Radix.UTF8.encodeScalars [ascii, acute]))
    "startsWithGraphemes accepts grapheme-aligned prefix"
  assert (Radix.UTF8.endsWithGraphemes graphemeInput (Radix.UTF8.encodeScalars [ascii, acute]))
    "endsWithGraphemes accepts grapheme-aligned suffix"
  assert (Radix.UTF8.findGraphemes? graphemeInput graphemeNeedle == some 3)
    "findGraphemes? returns the byte offset of the first grapheme match"
  assert (Radix.UTF8.containsGraphemes graphemeInput graphemeNeedle)
    "containsGraphemes reports grapheme-sequence containment"

private def runUTF8NormalizationTests
    (assert : Bool → String → IO Unit) : IO Unit := do
  let asciiA ← UTF8Test.scalar 0x41
  let asciiC ← UTF8Test.scalar 0x43
  let acute ← UTF8Test.scalar 0x0301
  let ringAbove ← UTF8Test.scalar 0x030A
  let cedilla ← UTF8Test.scalar 0x0327
  let asciiF ← UTF8Test.scalar 0x66
  let asciiI ← UTF8Test.scalar 0x69
  let asciiSpace ← UTF8Test.scalar 0x20
  let noBreakSpace ← UTF8Test.scalar 0x00A0
  let precomposedAAcute ← UTF8Test.scalar 0x00C1
  let precomposedARing ← UTF8Test.scalar 0x00C5
  let precomposedARingAcute ← UTF8Test.scalar 0x01FA
  let precomposedCCedilla ← UTF8Test.scalar 0x00C7
  let greekCapitalAlphaWithTonos ← UTF8Test.scalar 0x0386
  let greekCapitalIotaWithDialytika ← UTF8Test.scalar 0x03AA
  let greekCapitalAlpha ← UTF8Test.scalar 0x0391
  let greekCapitalIota ← UTF8Test.scalar 0x0399
  let diaeresis ← UTF8Test.scalar 0x0308
  let angstromSign ← UTF8Test.scalar 0x212B
  let ligatureFFI ← UTF8Test.scalar 0xFB03
  let fullwidthA ← UTF8Test.scalar 0xFF21
  let hangulL ← UTF8Test.scalar 0x1100
  let hangulV ← UTF8Test.scalar 0x1161
  let hangulT ← UTF8Test.scalar 0x11A8
  let hangulLV ← UTF8Test.scalar 0xAC00
  let hangulLVT ← UTF8Test.scalar 0xAC01

  assert (UTF8Test.scalarValues (Radix.UTF8.normalizeScalarsNFD [precomposedAAcute]) == [0x41, 0x0301])
    "normalizeScalarsNFD decomposes supported precomposed Latin characters"
  assert (Radix.UTF8.normalizeScalarsNFC [asciiA, acute] == [precomposedAAcute])
    "normalizeScalarsNFC composes supported precomposed Latin characters"
  assert (UTF8Test.scalarValues (Radix.UTF8.normalizeScalarsNFD [asciiC, acute, cedilla]) == [0x43, 0x0327, 0x0301])
    "normalizeScalarsNFD applies canonical ordering within a segment"
  assert (UTF8Test.scalarValues (Radix.UTF8.normalizeScalarsNFC [asciiC, acute, cedilla]) == [0x1E08])
    "normalizeScalarsNFC composes fully after canonical reordering when Unicode composition allows it"

  assert (UTF8Test.scalarValues (Radix.UTF8.normalizeScalarsNFD [hangulLV]) == [0x1100, 0x1161])
    "normalizeScalarsNFD decomposes Hangul LV syllables algorithmically"
  assert (UTF8Test.scalarValues (Radix.UTF8.normalizeScalarsNFD [hangulLVT]) == [0x1100, 0x1161, 0x11A8])
    "normalizeScalarsNFD decomposes Hangul LVT syllables algorithmically"
  assert (Radix.UTF8.normalizeScalarsNFC [hangulL, hangulV] == [hangulLV])
    "normalizeScalarsNFC composes Hangul L+V pairs"
  assert (Radix.UTF8.normalizeScalarsNFC [hangulL, hangulV, hangulT] == [hangulLVT])
    "normalizeScalarsNFC composes Hangul LV+T triples"
  assert (Radix.UTF8.normalizeScalarsNFKD [noBreakSpace, ligatureFFI, angstromSign, fullwidthA] ==
      [asciiSpace, asciiF, asciiF, asciiI, asciiA, ringAbove, asciiA])
    "normalizeScalarsNFKD decomposes supported compatibility characters"
  assert (Radix.UTF8.normalizeScalarsNFKC [noBreakSpace, ligatureFFI, angstromSign, fullwidthA] ==
      [asciiSpace, asciiF, asciiF, asciiI, precomposedARing, asciiA])
    "normalizeScalarsNFKC recomposes the supported compatibility subset"
  assert (UTF8Test.scalarValues (Radix.UTF8.normalizeScalarsNFD [precomposedARingAcute]) == [0x41, 0x030A, 0x0301])
    "normalizeScalarsNFD fully decomposes Latin letters outside the previous subset"
  assert (Radix.UTF8.normalizeScalarsNFD [greekCapitalAlphaWithTonos] == [greekCapitalAlpha, acute])
    "normalizeScalarsNFD fully decomposes Greek capital alpha with tonos"
  assert (Radix.UTF8.normalizeScalarsNFD [greekCapitalIotaWithDialytika] == [greekCapitalIota, diaeresis])
    "normalizeScalarsNFD fully decomposes Greek capital iota with dialytika"

  let precomposedBytes := Radix.UTF8.encodeScalars [precomposedAAcute, precomposedCCedilla]
  let decomposedBytes := Radix.UTF8.encodeScalars [asciiA, acute, asciiC, cedilla]
  let compatibilityBytes := Radix.UTF8.encodeScalars [noBreakSpace, ligatureFFI, angstromSign, fullwidthA]
  match Radix.UTF8.normalizeBytesNFD? precomposedBytes with
  | some normalized =>
    assert (Radix.UTF8.decodeBytes? normalized == some [asciiA, acute, asciiC, cedilla])
      "normalizeBytesNFD? decodes to the expected canonical decomposition"
  | none => assert false "normalizeBytesNFD? rejected valid UTF-8 input"
  match Radix.UTF8.normalizeBytesNFC? decomposedBytes with
  | some normalized =>
    assert (Radix.UTF8.decodeBytes? normalized == some [precomposedAAcute, precomposedCCedilla])
      "normalizeBytesNFC? decodes to the expected canonical composition"
  | none => assert false "normalizeBytesNFC? rejected valid UTF-8 input"
  assert (Radix.UTF8.isNormalizedBytesNFD? decomposedBytes == some true)
    "isNormalizedBytesNFD? accepts canonically decomposed UTF-8"
  assert (Radix.UTF8.isNormalizedBytesNFD? precomposedBytes == some false)
    "isNormalizedBytesNFD? rejects canonically composed UTF-8"
  assert (Radix.UTF8.isNormalizedBytesNFC? precomposedBytes == some true)
    "isNormalizedBytesNFC? accepts canonically composed UTF-8"
  assert (Radix.UTF8.canonicallyEquivalentBytes? precomposedBytes decomposedBytes)
    "canonicallyEquivalentBytes? matches precomposed and decomposed forms"
  match Radix.UTF8.normalizeBytesNFKD? compatibilityBytes with
  | some normalized =>
    assert (Radix.UTF8.decodeBytes? normalized == some [asciiSpace, asciiF, asciiF, asciiI, asciiA, ringAbove, asciiA])
      "normalizeBytesNFKD? decodes to the expected compatibility decomposition"
  | none => assert false "normalizeBytesNFKD? rejected valid UTF-8 input"
  match Radix.UTF8.normalizeBytesNFKC? compatibilityBytes with
  | some normalized =>
    assert (Radix.UTF8.decodeBytes? normalized == some [asciiSpace, asciiF, asciiF, asciiI, precomposedARing, asciiA])
      "normalizeBytesNFKC? decodes to the expected compatibility composition"
  | none => assert false "normalizeBytesNFKC? rejected valid UTF-8 input"
  assert (Radix.UTF8.normalizeBytes? .nfkd compatibilityBytes ==
      some (Radix.UTF8.encodeScalars [asciiSpace, asciiF, asciiF, asciiI, asciiA, ringAbove, asciiA]))
    "normalizeBytes? dispatches NFKD to the compatibility-normalization implementation"
  assert (Radix.UTF8.normalizeBytes? .nfkc compatibilityBytes ==
      some (Radix.UTF8.encodeScalars [asciiSpace, asciiF, asciiF, asciiI, precomposedARing, asciiA]))
    "normalizeBytes? dispatches NFKC to the compatibility-normalization implementation"
  assert (Radix.UTF8.isNormalizedBytesNFKD? compatibilityBytes == some false)
    "isNormalizedBytesNFKD? rejects non-normalized compatibility forms"
  assert (Radix.UTF8.isNormalizedBytesNFKC? (Radix.UTF8.encodeScalars [asciiSpace, asciiF, asciiF, asciiI, precomposedARing, asciiA]) == some true)
    "isNormalizedBytesNFKC? accepts compatibility-composed UTF-8"

private def runUTF8CaseMappingTests
    (assert : Bool → String → IO Unit) : IO Unit := do
  let asciiA ← UTF8Test.scalar 0x41
  let asciiC ← UTF8Test.scalar 0x43
  let asciiLowerA ← UTF8Test.scalar 0x61
  let asciiLowerC ← UTF8Test.scalar 0x63
  let asciiLowerF ← UTF8Test.scalar 0x66
  let asciiLowerI ← UTF8Test.scalar 0x69
  let asciiLowerK ← UTF8Test.scalar 0x6B
  let asciiLowerS ← UTF8Test.scalar 0x73
  let acute ← UTF8Test.scalar 0x0301
  let dotAbove ← UTF8Test.scalar 0x0307
  let ringAbove ← UTF8Test.scalar 0x030A
  let cedilla ← UTF8Test.scalar 0x0327
  let upperAAcute ← UTF8Test.scalar 0x00C1
  let upperARing ← UTF8Test.scalar 0x00C5
  let lowerAAcute ← UTF8Test.scalar 0x00E1
  let upperCCedilla ← UTF8Test.scalar 0x00C7
  let lowerCCedilla ← UTF8Test.scalar 0x00E7
  let angstromSign ← UTF8Test.scalar 0x212B
  let kelvinSign ← UTF8Test.scalar 0x212A
  let ligatureFFI ← UTF8Test.scalar 0xFB03
  let fullwidthA ← UTF8Test.scalar 0xFF21
  let sharpS ← UTF8Test.scalar 0x00DF
  let capitalSharpS ← UTF8Test.scalar 0x1E9E
  let capitalAWithRingAndAcute ← UTF8Test.scalar 0x01FA
  let dottedCapitalI ← UTF8Test.scalar 0x0130
  let longS ← UTF8Test.scalar 0x017F
  let diaeresis ← UTF8Test.scalar 0x0308
  let greekCapitalAlphaWithTonos ← UTF8Test.scalar 0x0386
  let greekCapitalIotaWithDialytika ← UTF8Test.scalar 0x03AA
  let greekAlpha ← UTF8Test.scalar 0x03B1
  let greekIota ← UTF8Test.scalar 0x03B9
  let greekCapitalSigma ← UTF8Test.scalar 0x03A3
  let greekSigma ← UTF8Test.scalar 0x03C3
  let greekFinalSigma ← UTF8Test.scalar 0x03C2
  let arabicIndicOne ← UTF8Test.scalar 0x0661
  let smile ← UTF8Test.scalar 0x1F642

  assert (Radix.UTF8.toLowerSimple asciiA == asciiLowerA)
    "toLowerSimple lowercases ASCII"
  assert (Radix.UTF8.toUpperSimple asciiLowerA == asciiA)
    "toUpperSimple uppercases ASCII"
  assert (Radix.UTF8.toLowerSimple upperAAcute == lowerAAcute)
    "toLowerSimple applies Unicode simple lowercase mappings to precomposed Latin letters"
  assert (Radix.UTF8.toUpperSimple lowerCCedilla == upperCCedilla)
    "toUpperSimple applies Unicode simple uppercase mappings to precomposed Latin letters"
  assert (Radix.UTF8.caseFoldSimple upperAAcute == lowerAAcute)
    "caseFoldSimple applies Unicode simple case folding to precomposed Latin letters"
  assert (Radix.UTF8.toLowerSimple greekCapitalSigma == greekSigma)
    "toLowerSimple lowercases Greek sigma via Unicode simple mappings"
  assert (Radix.UTF8.toUpperSimple greekSigma == greekCapitalSigma)
    "toUpperSimple uppercases Greek sigma via Unicode simple mappings"
  assert (Radix.UTF8.caseFoldSimple capitalSharpS == sharpS)
    "caseFoldSimple folds capital sharp s with the official simple case-fold mapping"
  assert (Radix.UTF8.caseFoldSimple greekFinalSigma == greekSigma)
    "caseFoldSimple normalizes Greek final sigma to sigma"
  assert (Radix.UTF8.Spec.Scalar.isUppercase greekCapitalSigma)
    "isUppercase recognizes Unicode uppercase letters"
  assert (Radix.UTF8.Spec.Scalar.isLowercase greekSigma)
    "isLowercase recognizes Unicode lowercase letters"
  assert (Radix.UTF8.Spec.Scalar.isAlpha greekCapitalSigma && Radix.UTF8.Spec.Scalar.isAlpha greekSigma)
    "isAlpha recognizes Unicode letters beyond ASCII"
  assert (Radix.UTF8.Spec.Scalar.isDigit arabicIndicOne)
    "isDigit recognizes Unicode decimal digits beyond ASCII"
  assert (Radix.UTF8.Spec.Scalar.isPrintable smile)
    "isPrintable recognizes non-ASCII Unicode scalars in printable categories"
  assert (Radix.UTF8.toLowerSimple smile == smile)
    "toLowerSimple leaves unsupported scalars unchanged"

  let mixedBytes := Radix.UTF8.encodeScalars [asciiA, upperAAcute, upperCCedilla, smile]
  match Radix.UTF8.lowercaseBytesSimple? mixedBytes with
  | some lowerBytes =>
    assert (Radix.UTF8.decodeBytes? lowerBytes == some [asciiLowerA, lowerAAcute, lowerCCedilla, smile])
      "lowercaseBytesSimple? lowercases supported UTF-8 scalars"
  | none => assert false "lowercaseBytesSimple? rejected valid UTF-8 input"
  match Radix.UTF8.uppercaseBytesSimple? (Radix.UTF8.encodeScalars [asciiLowerC, lowerAAcute, lowerCCedilla]) with
  | some upperBytes =>
    assert (Radix.UTF8.decodeBytes? upperBytes == some [asciiC, upperAAcute, upperCCedilla])
      "uppercaseBytesSimple? uppercases supported UTF-8 scalars"
  | none => assert false "uppercaseBytesSimple? rejected valid UTF-8 input"

  let composedUpper := Radix.UTF8.encodeScalars [upperAAcute, upperCCedilla]
  let decomposedLower := Radix.UTF8.encodeScalars [asciiLowerA, acute, asciiLowerC, cedilla]
  match Radix.UTF8.caseFoldBytesSimple? composedUpper with
  | some folded =>
    assert (Radix.UTF8.decodeBytes? folded == some [asciiLowerA, acute, asciiLowerC, cedilla])
      "caseFoldBytesSimple? lowers and canonically decomposes supported UTF-8 input"
  | none => assert false "caseFoldBytesSimple? rejected valid UTF-8 input"
  assert (Radix.UTF8.equalsCaseFoldSimpleBytes? composedUpper decomposedLower)
    "equalsCaseFoldSimpleBytes? matches precomposed uppercase and decomposed lowercase forms"
  assert (!Radix.UTF8.equalsCaseFoldSimpleBytes? composedUpper (Radix.UTF8.encodeScalars [asciiLowerA, acute]))
    "equalsCaseFoldSimpleBytes? rejects unequal scalar sequences"

  let compatibilityUpper := Radix.UTF8.encodeScalars [fullwidthA, ligatureFFI, kelvinSign, angstromSign]
  let compatibilityLower := Radix.UTF8.encodeScalars [asciiLowerA, asciiLowerF, asciiLowerF, asciiLowerI, asciiLowerK, asciiLowerA, ringAbove]
  match Radix.UTF8.caseFoldBytesCompatibility? compatibilityUpper with
  | some folded =>
    assert (Radix.UTF8.decodeBytes? folded == some [asciiLowerA, asciiLowerF, asciiLowerF, asciiLowerI, asciiLowerK, asciiLowerA, ringAbove])
      "caseFoldBytesCompatibility? compatibility-decomposes and case-folds practical compatibility forms"
  | none => assert false "caseFoldBytesCompatibility? rejected valid UTF-8 input"
  assert (Radix.UTF8.caseFoldScalarsCompatibility [fullwidthA, ligatureFFI, kelvinSign, angstromSign] ==
      [asciiLowerA, asciiLowerF, asciiLowerF, asciiLowerI, asciiLowerK, asciiLowerA, ringAbove])
    "caseFoldScalarsCompatibility normalizes compatibility forms before case folding"
  assert (Radix.UTF8.equalsCaseFoldCompatibilityBytes? compatibilityUpper compatibilityLower)
    "equalsCaseFoldCompatibilityBytes? matches compatibility forms against lowercase decomposed text"
  assert (Radix.UTF8.equalsCaseFoldCompatibilityBytes? (Radix.UTF8.encodeScalars [kelvinSign]) (Radix.UTF8.encodeScalars [asciiLowerK]))
    "equalsCaseFoldCompatibilityBytes? matches Kelvin sign and ASCII k"
  assert (Radix.UTF8.equalsCaseFoldCompatibilityBytes? (Radix.UTF8.encodeScalars [angstromSign]) (Radix.UTF8.encodeScalars [upperARing]))
    "equalsCaseFoldCompatibilityBytes? matches Angstrom sign and Latin A-ring"
  assert (Radix.UTF8.caseFoldScalarsCompatibility [sharpS] == [asciiLowerS, asciiLowerS])
    "caseFoldScalarsCompatibility expands sharp s to ss"
  assert (Radix.UTF8.caseFoldScalarsCompatibility [capitalSharpS] == [asciiLowerS, asciiLowerS])
    "caseFoldScalarsCompatibility expands capital sharp s to ss"
  assert (Radix.UTF8.caseFoldScalarsCompatibility [dottedCapitalI] == [asciiLowerI, dotAbove])
    "caseFoldScalarsCompatibility preserves dotted i semantics"
  assert (Radix.UTF8.caseFoldScalarsCompatibility [longS] == [asciiLowerS])
    "caseFoldScalarsCompatibility folds long s to s"
  assert (Radix.UTF8.caseFoldScalarsCompatibility [greekCapitalSigma] == [greekSigma])
    "caseFoldScalarsCompatibility lowercases Greek capital sigma"
  assert (Radix.UTF8.caseFoldScalarsCompatibility [greekFinalSigma] == [greekSigma])
    "caseFoldScalarsCompatibility normalizes final sigma to sigma"
  assert (Radix.UTF8.caseFoldScalarsSimple [capitalSharpS] == [sharpS])
    "caseFoldScalarsSimple uses Unicode simple folding for capital sharp s"
  assert (Radix.UTF8.caseFoldScalarsSimple [greekFinalSigma] == [greekSigma])
    "caseFoldScalarsSimple normalizes final sigma to sigma"
  assert (Radix.UTF8.caseFoldScalarsSimple [greekCapitalAlphaWithTonos] == [greekAlpha, acute])
    "caseFoldScalarsSimple preserves canonical equivalence for Greek alpha with tonos"
  assert (Radix.UTF8.caseFoldScalarsSimple [greekCapitalIotaWithDialytika] == [greekIota, diaeresis])
    "caseFoldScalarsSimple preserves canonical equivalence for Greek iota with dialytika"
  assert (UTF8Test.scalarValues (Radix.UTF8.caseFoldScalarsSimple [capitalAWithRingAndAcute]) == [0x61, 0x030A, 0x0301])
    "caseFoldScalarsSimple preserves canonical equivalence for Latin A with ring and acute"
  assert (Radix.UTF8.equalsCaseFoldCompatibilityBytes? (Radix.UTF8.encodeScalars [capitalSharpS]) (Radix.UTF8.encodeScalars [asciiLowerS, asciiLowerS]))
    "equalsCaseFoldCompatibilityBytes? matches capital sharp s and ss"
  assert (Radix.UTF8.equalsCaseFoldCompatibilityBytes? (Radix.UTF8.encodeScalars [dottedCapitalI]) (Radix.UTF8.encodeScalars [asciiLowerI, dotAbove]))
    "equalsCaseFoldCompatibilityBytes? matches dotted capital I and i plus dot"
  assert (Radix.UTF8.equalsCaseFoldCompatibilityBytes? (Radix.UTF8.encodeScalars [greekCapitalSigma]) (Radix.UTF8.encodeScalars [greekFinalSigma]))
    "equalsCaseFoldCompatibilityBytes? matches sigma variants"
  assert (Radix.UTF8.equalsCaseFoldSimpleBytes? (Radix.UTF8.encodeScalars [greekCapitalAlphaWithTonos]) (Radix.UTF8.encodeScalars [greekAlpha, acute]))
    "equalsCaseFoldSimpleBytes? matches Greek alpha with tonos across canonical forms"
  assert (Radix.UTF8.equalsCaseFoldSimpleBytes? (Radix.UTF8.encodeScalars [greekCapitalIotaWithDialytika]) (Radix.UTF8.encodeScalars [greekIota, diaeresis]))
    "equalsCaseFoldSimpleBytes? matches Greek iota with dialytika across canonical forms"
  assert (Radix.UTF8.equalsCaseFoldSimpleBytes? (Radix.UTF8.encodeScalars [capitalAWithRingAndAcute]) (Radix.UTF8.encodeScalars [asciiLowerA, ringAbove, acute]))
    "equalsCaseFoldSimpleBytes? matches Latin A with ring and acute across canonical forms"

private def runUTF8StreamingAndInteropTail
    (assert : Bool → String → IO Unit)
    (ascii twoByte threeByte fourByte : Radix.UTF8.Scalar) : IO Unit := do
  let strictChunk1 := UTF8Test.byteArray [0xF0, 0x9F]
  let strictChunk2 := UTF8Test.byteArray [0x99, 0x82, 0x41]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init strictChunk1 with
  | Except.ok chunk1 =>
    assert (chunk1.scalars == []) "streaming strict first chunk defers incomplete scalar"
    assert (chunk1.decoder.pendingByteCount == 2) "streaming strict first chunk stores pending bytes"
    match Radix.UTF8.StreamDecoder.feed? chunk1.decoder strictChunk2 with
    | Except.ok chunk2 =>
      assert (UTF8Test.scalarValues chunk2.scalars == [0x1F642, 0x41])
        "streaming strict second chunk decodes pending scalar and ASCII tail"
      assert (!chunk2.decoder.hasPending) "streaming strict leaves no pending bytes after completion"
      assert (Radix.UTF8.StreamDecoder.finish? chunk2.decoder == Except.ok [])
        "streaming strict finish on empty pending succeeds"
    | Except.error err =>
      assert false s!"streaming strict second chunk unexpectedly failed: {reprStr err}"
  | Except.error err =>
    assert false s!"streaming strict first chunk unexpectedly failed: {reprStr err}"

  match Radix.UTF8.decodeChunks? [strictChunk1, strictChunk2] with
  | Except.ok scalars =>
    assert (UTF8Test.scalarValues scalars == [0x1F642, 0x41])
      "decodeChunks? matches strict streaming result"
  | Except.error err =>
    assert false s!"decodeChunks? unexpectedly failed: {reprStr err}"

  let invalidChunk1 := UTF8Test.byteArray [0xC2]
  let invalidChunk2 := UTF8Test.byteArray [0x41, 0x42]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init invalidChunk1 with
  | Except.ok chunk1 =>
    assert (chunk1.scalars == []) "invalid streaming prefix yields no scalar before continuation arrives"
    assert (chunk1.decoder.pendingByteCount == 1) "invalid streaming prefix stores one pending byte"
    match Radix.UTF8.StreamDecoder.feed? chunk1.decoder invalidChunk2 with
    | Except.ok chunk2 =>
      assert false s!"invalid continuation unexpectedly decoded: {reprStr chunk2}"
    | Except.error err =>
      assert (err.scalars == []) "invalid continuation emits no scalar before error"
      assert (err.offset == 0) "invalid continuation is reported at buffered offset zero"
      assert (err.error.kind == Radix.UTF8.Spec.DecodeErrorKind.invalidContinuationByte)
        "invalid continuation reports detailed error kind"
  | Except.error err =>
    assert false s!"invalid streaming prefix unexpectedly failed early: {reprStr err}"

  let truncatedStrictChunk := UTF8Test.byteArray [0xE1, 0x80]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init truncatedStrictChunk with
  | Except.ok chunk =>
    assert (chunk.decoder.pendingByteCount == 2) "strict truncated chunk remains pending before finish"
    match Radix.UTF8.StreamDecoder.finish? chunk.decoder with
    | Except.ok scalars =>
      assert false s!"strict finish unexpectedly accepted truncated input: {UTF8Test.scalarValues scalars}"
    | Except.error err =>
      assert (err.scalars == []) "strict finish truncated error emits no scalar"
      assert (err.offset == 0) "strict finish truncated error starts at pending offset zero"
      assert (err.error.kind == Radix.UTF8.Spec.DecodeErrorKind.truncatedSequence)
        "strict finish reports truncated sequence"
      assert (err.error.consumed == 2) "strict finish keeps truncated maximal subpart width"
  | Except.error err =>
    assert false s!"strict truncated chunk unexpectedly failed before finish: {reprStr err}"

  let replacementChunk1 := UTF8Test.byteArray [0xE1]
  let replacementChunk2 := UTF8Test.byteArray [0x80, 0x41]
  let perByte1 := Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .perByte replacementChunk1
  assert (perByte1.scalars == []) "per-byte replacement defers incomplete prefix"
  assert (perByte1.decoder.pendingByteCount == 1) "per-byte replacement stores incomplete prefix"
  let perByte2 := Radix.UTF8.StreamDecoder.feedReplacing perByte1.decoder .perByte replacementChunk2
  assert (UTF8Test.scalarValues perByte2.scalars == [UTF8Test.replacementValue, UTF8Test.replacementValue, 0x41])
    "per-byte replacement reports each invalid byte after chunk join"
  assert (!perByte2.decoder.hasPending) "per-byte replacement clears pending after malformed completion"

  let maximal1 := Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .maximalSubpart replacementChunk1
  assert (maximal1.scalars == []) "maximal-subpart replacement defers incomplete prefix"
  assert (maximal1.decoder.pendingByteCount == 1) "maximal-subpart replacement stores incomplete prefix"
  let maximal2 := Radix.UTF8.StreamDecoder.feedReplacing maximal1.decoder .maximalSubpart replacementChunk2
  assert (UTF8Test.scalarValues maximal2.scalars == [UTF8Test.replacementValue, 0x41])
    "maximal-subpart replacement collapses buffered invalid prefix into one marker"
  assert (!maximal2.decoder.hasPending) "maximal-subpart replacement clears pending after malformed completion"

  let finishPerByte :=
    Radix.UTF8.StreamDecoder.finishReplacing
      (Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .perByte truncatedStrictChunk).decoder
      .perByte
  assert (UTF8Test.scalarValues finishPerByte == [UTF8Test.replacementValue, UTF8Test.replacementValue])
    "per-byte finish replaces each pending truncated byte"

  let finishMaximal :=
    Radix.UTF8.StreamDecoder.finishReplacing
      (Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .maximalSubpart truncatedStrictChunk).decoder
      .maximalSubpart
  assert (UTF8Test.scalarValues finishMaximal == [UTF8Test.replacementValue])
    "maximal-subpart finish replaces pending truncated prefix once"

  assert (UTF8Test.scalarValues (Radix.UTF8.decodeChunksReplacing .maximalSubpart
    [UTF8Test.byteArray [0xE2], UTF8Test.byteArray [0x82], UTF8Test.byteArray [0xAC]]) == [0x20AC])
    "decodeChunksReplacing reconstructs valid scalar across three chunks"
  assert (UTF8Test.scalarValues (Radix.UTF8.decodeChunksReplacing .maximalSubpart
    [replacementChunk1, replacementChunk2]) == [UTF8Test.replacementValue, 0x41])
    "decodeChunksReplacing maximal-subpart matches manual streaming result"

  UTF8Test.runUTF8CursorTests assert ascii twoByte threeByte fourByte
  UTF8Test.runUTF8GraphemeTests assert ascii
  UTF8Test.runOfficialGraphemeBreakTests assert
  UTF8Test.runUTF16InteropTests assert ascii threeByte fourByte
  UTF8Test.runUTF8NormalizationTests assert
  UTF8Test.runOfficialNormalizationTests assert
  UTF8Test.runUTF8CaseMappingTests assert
  UTF8Test.runOfficialUnicodeDataTests assert
  UTF8Test.runOfficialCaseFoldingTests assert
  UTF8Test.runUTF8TextOpTests assert ascii twoByte threeByte fourByte

end UTF8Test

def runUTF8Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UTF8 tests..."

  let ascii ← UTF8Test.scalar 0x41
  let twoByte ← UTF8Test.scalar 0x00A2
  let threeByte ← UTF8Test.scalar 0x20AC
  let fourByte ← UTF8Test.scalar 0x1F642
  let maxScalar ← UTF8Test.scalar 0x10FFFF

  assert (Radix.UTF8.encodedLength ascii == 1) "ASCII length"
  assert (Radix.UTF8.encodedLength twoByte == 2) "2-byte length"
  assert (Radix.UTF8.encodedLength threeByte == 3) "3-byte length"
  assert (Radix.UTF8.encodedLength fourByte == 4) "4-byte length"
  assert (Radix.UTF8.encodedLength maxScalar == 4) "max scalar length"

  let encoded := Radix.UTF8.encodeScalars [ascii, twoByte, threeByte, fourByte]
  assert (Radix.UTF8.isWellFormed encoded) "encoded scalars well formed"
  match Radix.UTF8.decodeBytes? encoded with
  | some scalars =>
    assert (scalars.map (·.val) == [0x41, 0x00A2, 0x20AC, 0x1F642]) "decode encoded scalars"
  | none => assert false "decode encoded scalars failed"

  match Radix.UTF8.decodeNextBytes? (Radix.UTF8.encodeScalar fourByte) with
  | some (decoded, consumed) =>
    assert (decoded.val == 0x1F642) "decodeNext returns scalar"
    assert (consumed == 4) "decodeNext consumed four bytes"
  | none => assert false "decodeNext four-byte scalar failed"

  let boundaryScalars := [ascii, (← UTF8Test.scalar 0x7F), (← UTF8Test.scalar 0x80), (← UTF8Test.scalar 0x7FF), (← UTF8Test.scalar 0x800), (← UTF8Test.scalar 0xD7FF), (← UTF8Test.scalar 0xE000), (← UTF8Test.scalar 0xFFFF), (← UTF8Test.scalar 0x10000), maxScalar]
  let boundaryEncoded := Radix.UTF8.encodeScalars boundaryScalars
  match Radix.UTF8.decodeBytes? boundaryEncoded with
  | some scalars =>
    assert (scalars.map (·.val) == boundaryScalars.map (·.val)) "boundary scalar round-trip"
  | none => assert false "boundary scalar round-trip failed"

  assert (Radix.UTF8.scalarCount? boundaryEncoded == some boundaryScalars.length) "scalar count round-trip"

  let malformed1 := ByteArray.mk #[0xC0, 0xAF]
  let malformed2 := ByteArray.mk #[0xED, 0xA0, 0x80]
  let malformed3 := ByteArray.mk #[0xF0, 0x9F, 0x99]
  assert (!Radix.UTF8.isWellFormed malformed1) "reject overlong"
  assert (!Radix.UTF8.isWellFormed malformed2) "reject surrogate"
  assert (!Radix.UTF8.isWellFormed malformed3) "reject truncated four-byte sequence"
  assert (Radix.UTF8.ofNat? 0xD800 == none) "reject surrogate constructor"

  let assertDetailedError :=
    fun (bytes : List UInt8)
        (kind : Radix.UTF8.Spec.DecodeErrorKind)
        (expectedLength consumed : Nat)
        (label : String) => do
      match Radix.UTF8.decodeNextListStep? bytes with
      | some (Radix.UTF8.Spec.DecodeStep.error err) =>
        assert (err.kind == kind) s!"{label}: error kind"
        assert (err.expectedLength == expectedLength) s!"{label}: expected length"
        assert (err.consumed == consumed) s!"{label}: maximal subpart length"
        assert (Radix.UTF8.maximalSubpartLength bytes == consumed) s!"{label}: maximalSubpartLength"
        assert (Radix.UTF8.firstDecodeErrorList? bytes == some err) s!"{label}: firstDecodeErrorList?"
      | some (Radix.UTF8.Spec.DecodeStep.scalar _ actualConsumed) =>
        assert false s!"{label}: unexpectedly decoded scalar with width {actualConsumed}"
      | none =>
        assert false s!"{label}: missing decode step"

  assertDetailedError [0x80]
    Radix.UTF8.Spec.DecodeErrorKind.unexpectedContinuationByte 1 1
    "detailed error: unexpected continuation"
  assertDetailedError [0xC0, 0xAF]
    Radix.UTF8.Spec.DecodeErrorKind.overlongSequence 2 1
    "detailed error: overlong lead"
  assertDetailedError [0xC2, 0x41, 0x42]
    Radix.UTF8.Spec.DecodeErrorKind.invalidContinuationByte 2 1
    "detailed error: invalid continuation"
  assertDetailedError [0xE1, 0x80]
    Radix.UTF8.Spec.DecodeErrorKind.truncatedSequence 3 2
    "detailed error: truncated three-byte sequence"
  assertDetailedError [0xED, 0xA0, 0x80]
    Radix.UTF8.Spec.DecodeErrorKind.surrogateSequence 3 1
    "detailed error: surrogate sequence"
  assertDetailedError [0xF4, 0x91, 0x92, 0x93]
    Radix.UTF8.Spec.DecodeErrorKind.outOfRangeSequence 4 1
    "detailed error: out-of-range sequence"

  -- ── Spec-level scalar predicates ──
  assert (Radix.UTF8.Spec.Scalar.isAscii ascii) "ASCII scalar isAscii"
  assert (!Radix.UTF8.Spec.Scalar.isAscii fourByte) "four-byte scalar not isAscii"
  assert (Radix.UTF8.Spec.Scalar.isBMP threeByte) "3-byte scalar isBMP"
  assert (!Radix.UTF8.Spec.Scalar.isBMP fourByte) "four-byte scalar not isBMP"
  assert (Radix.UTF8.Spec.Scalar.isSupplementary fourByte) "four-byte scalar isSupplementary"
  assert (!Radix.UTF8.Spec.Scalar.isSupplementary ascii) "ASCII not isSupplementary"
  assert (Radix.UTF8.Spec.Scalar.plane ascii == 0) "ASCII on plane 0"
  assert (Radix.UTF8.Spec.Scalar.plane fourByte == 1) "emoji on plane 1"

  -- ── Ops-level helpers ──
  let encodedList := Radix.UTF8.encodeAllToList [ascii, twoByte]
  assert (encodedList.length > 0) "encodeAllToList produces bytes"
  let decodedList := Radix.UTF8.decodeList? encodedList
  match decodedList with
  | some scalars => assert (scalars.length == 2) "decodeList? round-trip count"
  | none => assert false "decodeList? round-trip failed"
  assert (Radix.UTF8.isWellFormedList encodedList) "encodeAllToList is well-formed"
  let byteCounts := Radix.UTF8.totalByteLength [ascii, twoByte, threeByte, fourByte]
  assert (byteCounts == 10) "totalByteLength 1+2+3+4=10"
  let nats := Radix.UTF8.scalarsToNats [ascii, twoByte]
  assert (nats == [0x41, 0x00A2]) "scalarsToNats"

  -- ── BOM tests ──
  let bomBytes := Radix.UTF8.Spec.bom
  assert (bomBytes == [0xEF, 0xBB, 0xBF]) "BOM bytes"
  assert (Radix.UTF8.Spec.hasBOM [0xEF, 0xBB, 0xBF, 0x41]) "hasBOM true"
  assert (!Radix.UTF8.Spec.hasBOM [0x41, 0x42]) "hasBOM false"
  assert (Radix.UTF8.Spec.stripBOM [0xEF, 0xBB, 0xBF, 0x41] == [0x41]) "stripBOM"
  assert (Radix.UTF8.Spec.stripBOM [0x41] == [0x41]) "stripBOM no BOM"

  -- ── Byte classification ──
  let classes := Radix.UTF8.classifyBytes (ByteArray.mk #[0x41, 0xC2, 0xA2, 0x80])
  assert (classes.length == 4) "classifyBytes length"

  -- RFC 3629 examples and boundary syntax.
  let rfcExample1 := UTF8Test.byteArray [0x41, 0xE2, 0x89, 0xA2, 0xCE, 0x91, 0x2E]
  match Radix.UTF8.decodeBytes? rfcExample1 with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0x41, 0x2262, 0x0391, 0x2E])
      "RFC 3629 example 1 decodes"
  | none => assert false "RFC 3629 example 1 rejected"

  let rfcExampleKorean := UTF8Test.byteArray [0xED, 0x95, 0x9C, 0xEA, 0xB5, 0xAD, 0xEC, 0x96, 0xB4]
  match Radix.UTF8.decodeBytes? rfcExampleKorean with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0xD55C, 0xAD6D, 0xC5B4])
      "RFC 3629 Korean example decodes"
  | none => assert false "RFC 3629 Korean example rejected"

  let rfcExampleJapanese := UTF8Test.byteArray [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E]
  match Radix.UTF8.decodeBytes? rfcExampleJapanese with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0x65E5, 0x672C, 0x8A9E])
      "RFC 3629 Japanese example decodes"
  | none => assert false "RFC 3629 Japanese example rejected"

  let rfcExampleBOM := UTF8Test.byteArray [0xEF, 0xBB, 0xBF, 0xF0, 0xA3, 0x8E, 0xB4]
  assert (Radix.UTF8.hasByteOrderMark rfcExampleBOM) "RFC 3629 BOM detected"
  match Radix.UTF8.decodeBytes? (Radix.UTF8.stripByteOrderMark rfcExampleBOM) with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0x233B4])
      "RFC 3629 BOM stripping preserves payload"
  | none => assert false "RFC 3629 BOM payload rejected"

  let rfcValidBoundaries : List (List UInt8) :=
    [ [0x00]
    , [0x7F]
    , [0xC2, 0x80]
    , [0xDF, 0xBF]
    , [0xE0, 0xA0, 0x80]
    , [0xED, 0x9F, 0xBF]
    , [0xEE, 0x80, 0x80]
    , [0xEF, 0xBF, 0xBF]
    , [0xF0, 0x90, 0x80, 0x80]
    , [0xF4, 0x8F, 0xBF, 0xBF]
    ]
  for bytes in rfcValidBoundaries do
    assert (Radix.UTF8.Spec.validateUTF8 bytes) s!"RFC boundary accepted: {bytes}"
    assert (Radix.UTF8.isWellFormedList bytes) s!"Ops accepts RFC boundary: {bytes}"

  let rfcInvalidBoundaries : List (List UInt8) :=
    [ [0x80]
    , [0xBF]
    , [0xC0, 0x80]
    , [0xC1, 0xBF]
    , [0xE0, 0x80, 0x80]
    , [0xE0, 0x9F, 0xBF]
    , [0xED, 0xA0, 0x80]
    , [0xED, 0xBF, 0xBF]
    , [0xF0, 0x80, 0x80, 0x80]
    , [0xF0, 0x8F, 0xBF, 0xBF]
    , [0xF4, 0x90, 0x80, 0x80]
    , [0xF5, 0x80, 0x80, 0x80]
    , [0xFE]
    , [0xFF]
    ]
  for bytes in rfcInvalidBoundaries do
    assert (!Radix.UTF8.Spec.validateUTF8 bytes) s!"RFC boundary rejected: {bytes}"
    assert (!Radix.UTF8.isWellFormedList bytes) s!"Ops rejects RFC boundary: {bytes}"

  -- Markus Kuhn UTF-8 stress cases: replacement and re-synchronization.
  let unexpectedContinuation := UTF8Test.byteArray [0x80, 0x22]
  assert (!Radix.UTF8.isWellFormed unexpectedContinuation) "unexpected continuation rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing unexpectedContinuation) ==
    [UTF8Test.replacementValue, 0x22]) "unexpected continuation resyncs at quote"

  let lonelyStart := UTF8Test.byteArray [0xE0, 0x22]
  assert (!Radix.UTF8.isWellFormed lonelyStart) "lonely start byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing lonelyStart) ==
    [UTF8Test.replacementValue, 0x22]) "lonely start byte resyncs at quote"

  let impossibleBytes := UTF8Test.byteArray [0xFE, 0xFF, 0x22]
  assert (!Radix.UTF8.isWellFormed impossibleBytes) "impossible bytes rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing impossibleBytes) ==
    [UTF8Test.replacementValue, UTF8Test.replacementValue, 0x22])
    "impossible bytes produce one replacement per byte"

  let overlongSlash2 := UTF8Test.byteArray [0xC0, 0xAF, 0x22]
  assert (!Radix.UTF8.isWellFormed overlongSlash2) "overlong slash 2-byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing overlongSlash2) ==
    [UTF8Test.replacementValue, UTF8Test.replacementValue, 0x22])
    "overlong slash 2-byte resyncs after invalid bytes"

  let overlongSlash3 := UTF8Test.byteArray [0xE0, 0x80, 0xAF, 0x22]
  assert (!Radix.UTF8.isWellFormed overlongSlash3) "overlong slash 3-byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing overlongSlash3) ==
    [UTF8Test.replacementValue, UTF8Test.replacementValue, UTF8Test.replacementValue, 0x22])
    "overlong slash 3-byte resyncs after invalid bytes"

  let overlongSlash4 := UTF8Test.byteArray [0xF0, 0x80, 0x80, 0xAF, 0x22]
  assert (!Radix.UTF8.isWellFormed overlongSlash4) "overlong slash 4-byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing overlongSlash4) ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x22
    ]) "overlong slash 4-byte resyncs after invalid bytes"

  let surrogatePairBytes := UTF8Test.byteArray [0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80, 0x22]
  assert (!Radix.UTF8.isWellFormed surrogatePairBytes) "surrogate pair encoding rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing surrogatePairBytes) ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x22
    ]) "surrogate pair encoding replaces each invalid byte and resyncs"

  -- Unicode 17 Chapter 3 official conformance vectors.
  let officialReplacementVectors : List (List UInt8 × List Nat × String) :=
    [ ( [0xC0, 0xAF, 0xE0, 0x80, 0xBF, 0xF0, 0x81, 0x82, 0x41]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        ]
      , "Unicode 17 Table 3-8 non-shortest forms"
      )
    , ( [0xED, 0xA0, 0x80, 0xED, 0xBF, 0xBF, 0xED, 0xAF, 0x41]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        ]
      , "Unicode 17 Table 3-9 surrogate sequences"
      )
    , ( [0xF4, 0x91, 0x92, 0x93, 0xFF, 0x41, 0x80, 0xBF, 0x42]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x42
        ]
      , "Unicode 17 Table 3-10 other ill-formed sequences"
      )
    , ( [0xE1, 0x80, 0xE2, 0xF0, 0x91, 0x92, 0xF1, 0xBF, 0x41]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        ]
      , "Unicode 17 Table 3-11 truncated sequences"
      )
    ]
  for vector in officialReplacementVectors do
    let (bytes, expected, label) := vector
    assert (UTF8Test.strictReplacementValues bytes == expected) s!"{label}: maximal-subpart replacement"

  let truncatedUnicodeTable := [0xE1, 0x80, 0xE2, 0xF0, 0x91, 0x92, 0xF1, 0xBF, 0x41]
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeListReplacing truncatedUnicodeTable) ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x41
    ]) "legacy replacement keeps one-marker-per-byte semantics"
  assert (UTF8Test.strictReplacementValues truncatedUnicodeTable ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x41
    ]) "strict replacement collapses truncated prefixes to maximal subparts"

  assert (UTF8Test.strictReplacementValues [0xC2, 0x41, 0x42] ==
    [UTF8Test.replacementValue, 0x41, 0x42])
    "Unicode D93b example does not consume valid successor bytes"
  assert (UTF8Test.strictReplacementValues [0x41, 0xC2, 0xC3, 0xB1, 0x42] ==
    [0x41, UTF8Test.replacementValue, 0x00F1, 0x42])
    "Unicode D86 partition preserves following minimal well-formed subsequence"
  assert (UTF8Test.strictReplacementValues [0xE1, 0x80, 0x41] ==
    [UTF8Test.replacementValue, 0x41])
    "strict replacement consumes truncated maximal subpart only"

  -- Exhaustive coverage over all Unicode scalar values.
  let mut exhaustiveCount := 0
  let mut oneByteCount := 0
  let mut twoByteCount := 0
  let mut threeByteCount := 0
  let mut fourByteCount := 0
  let mut scalarNat := 0
  while scalarNat ≤ 0x10FFFF do
    match Radix.UTF8.ofNat? scalarNat with
    | some scalarValue =>
      let encodedList := Radix.UTF8.encodeToList scalarValue
      assert (Radix.UTF8.encodedLength scalarValue == encodedList.length)
        s!"exhaustive encodedLength matches byte count at scalar {scalarNat}"
      assert (Radix.UTF8.maximalSubpartLength encodedList == encodedList.length)
        s!"exhaustive maximalSubpartLength matches valid scalar width at scalar {scalarNat}"
      match Radix.UTF8.decodeList? encodedList with
      | some decoded =>
        assert (decoded == [scalarValue]) s!"exhaustive UTF-8 round-trip failed at scalar {scalarNat}"
      | none =>
        assert false s!"exhaustive decode rejected scalar {scalarNat}"
      exhaustiveCount := exhaustiveCount + 1
      match encodedList.length with
      | 1 => oneByteCount := oneByteCount + 1
      | 2 => twoByteCount := twoByteCount + 1
      | 3 => threeByteCount := threeByteCount + 1
      | 4 => fourByteCount := fourByteCount + 1
      | _ => assert false s!"unexpected UTF-8 width {encodedList.length} at scalar {scalarNat}"
    | none =>
      assert (0xD800 ≤ scalarNat && scalarNat ≤ 0xDFFF)
        s!"only surrogates should be rejected by Scalar.ofNat?: {scalarNat}"

    if scalarNat == 0x10FFFF then
      scalarNat := scalarNat + 1
    else if scalarNat == 0xD7FF then
      scalarNat := 0xE000
    else
      scalarNat := scalarNat + 1

  assert (exhaustiveCount == 1112064) "exhaustive scalar count matches Unicode scalar space"
  assert (oneByteCount == 128) "ASCII scalar count matches Unicode scalar space"
  assert (twoByteCount == 1920) "two-byte scalar count matches Unicode scalar space"
  assert (threeByteCount == 61440) "three-byte scalar count matches Unicode scalar space"
  assert (fourByteCount == 1048576) "four-byte scalar count matches Unicode scalar space"

  UTF8Test.runUTF8StreamingAndInteropTail assert ascii twoByte threeByte fourByte

  c.get
