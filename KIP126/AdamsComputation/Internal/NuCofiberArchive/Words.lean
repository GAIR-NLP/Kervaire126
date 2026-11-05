module

public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Generators
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Generators
public import KIP126.AdamsComputation.Internal.ArchiveData.Generators
import all KIP126.AdamsComputation.Internal.ArchiveData.Generators
import all Init.Data.List.SplitOn.Basic

/-! Cν module-word syntax, generator coefficients and degrees. The final
number is a Cν module-generator address; preceding numbers are S⁰
generator/exponent pairs. -/

set_option backward.privateInPublic true

@[expose] section
namespace KIP126.Computation.NuCofiberArchive
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/- Top-cell coefficients: zero on cell 0 and cellCoeff on cell 4. -/
private def topCellCoefficient? (i : ℕ) : Option String := do
  let generator ← generator? i
  match generator.cell with
  | 0 => some ""
  | 4 => some generator.cellCoeff
  | _ => none

/- Ordered sphere factors acting on one Cν module generator. -/
private structure ModuleWord where
  spherePowers : List (ℕ × ℕ)
  moduleGenerator : ℕ
  deriving Repr, DecidableEq

private def parseWordNumbers : List ℕ → Option ModuleWord
  | [] => none
  | [moduleGenerator] => some ⟨[], moduleGenerator⟩
  | i :: exponent :: rest => do
      let word ← parseWordNumbers rest
      pure ⟨(i, exponent) :: word.spherePowers, word.moduleGenerator⟩

private def spherePowersDegree : List (ℕ × ℕ) → Option (ℕ × ℕ)
  | [] => some (0, 0)
  | (i, exponent) :: rest =>
      if hi : i < CachedStandard.archiveGeneratorCount then
        match exponent with
        | 0 => none
        | _ + 1 => do
            let degree ← spherePowersDegree rest
            let record := CachedStandard.archiveGeneratorRecord ⟨i, hi⟩
            pure (exponent * record.2.1 + degree.1,
              exponent * record.2.2 + degree.2)
      else none

private def wordDegree (word : ModuleWord) : Option (ℕ × ℕ) := do
  if word.moduleGenerator < generatorCount then
    let moduleGenerator ← generator? word.moduleGenerator
    let sphereDegree ← spherePowersDegree word.spherePowers
    pure (sphereDegree.1 + moduleGenerator.s, sphereDegree.2 + moduleGenerator.t)
  else none

/- Read only ASCII decimal digits. All recursion below is over lists so that
the archive's Boolean degree checks reduce directly in the kernel. -/
private def decimalDigit? (c : Char) : Option ℕ :=
  let n := c.toNat
  match Nat.ble 48 n && Nat.ble n 57 with
  | true => some (n - 48)
  | false => none

private def parseDecimalRest : List Char → ℕ → Option ℕ
  | [], value => some value
  | c :: chars, value => do
      let digit ← decimalDigit? c
      parseDecimalRest chars (10 * value + digit)

private def parseDecimal? : List Char → Option ℕ
  | [] => none
  | c :: chars => do
      let digit ← decimalDigit? c
      parseDecimalRest chars digit

private def parseNumeralFields : List (List Char) → Option (List ℕ)
  | [] => some []
  | chars :: fields => do
      let value ← parseDecimal? chars
      let values ← parseNumeralFields fields
      pure (value :: values)

private def parseNumerals (code : String) : Option (List ℕ) :=
  parseNumeralFields (code.toList.splitOn ',')

/- Invalid tokens, an even or empty number list, zero exponents, and either
kind of out-of-range generator address all fail before a word is returned. -/
private def parseWord (code : String) : Option ModuleWord := do
  let numbers ← parseNumerals code
  let word ← parseWordNumbers numbers
  let _ ← wordDegree word
  pure word

/- Compute the degree once when checking the full archive; parseWord also
performs this validation when the caller needs the word itself. -/
private def labelDegree (code : String) : Option (ℕ × ℕ) := do
  let numbers ← parseNumerals code
  let word ← parseWordNumbers numbers
  wordDegree word

private def degreeMatches (s t : ℕ) (code : String) : Bool :=
  labelDegree code == some (s, t)

end KIP126.Computation.NuCofiberArchive
