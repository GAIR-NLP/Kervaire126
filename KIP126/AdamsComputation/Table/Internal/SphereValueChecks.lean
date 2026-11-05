module

public import KIP126.AdamsComputation.Table.ValueData
import all KIP126.AdamsComputation.Table.ValueSyntax
public import KIP126.AdamsComputation.Standard

/-! Sphere-source word certificates for the displayed expression bindings. -/

set_option backward.privateInPublic true

@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def monomialWord : ∀ {s t : ℕ},
    SourceMonomial Standard.archive.generators s t → List ℕ
  | _, _, .one => []
  | _, _, .generator i => [i.val]
  | _, _, .mul a b => monomialWord a ++ monomialWord b

private noncomputable def expressionWord : Expression → List ℕ
  | .one => []
  | .named a => [(Standard.archive.atomIndex a).val]
  | .generator id _ _ => [id]
  | .mul a b => expressionWord a ++ expressionWord b

private def admissible : Expression → Prop
  | .one => True
  | .named _ => True
  | .generator id s t => if hi : id < Standard.archive.generators.count then
      Standard.archive.generators.degree ⟨id,hi⟩ = (s,t) else False
  | .mul a b => admissible a ∧ admissible b

private noncomputable def admissibleDecidable : (e : Expression) → Decidable (admissible e)
  | .one => isTrue trivial
  | .named _ => isTrue trivial
  | .generator id s t => by
    dsimp only [admissible]
    split_ifs <;> infer_instance
  | .mul a b => by
    letI := admissibleDecidable a
    letI := admissibleDecidable b
    dsimp only [admissible]
    infer_instance
private noncomputable instance (e : Expression) : Decidable (admissible e) := admissibleDecidable e

private noncomputable def checkedWord (s t i : ℕ) : Option (List ℕ) :=
  if hi : i < Standard.archive.basisCount s t then
    some (monomialWord (Standard.archive.basisMonomial s t ⟨i,hi⟩))
  else none

private def rowValid (v : BasisValue) : Prop :=
  admissible v.expression ∧ (expressionDegree v.expression).2 ≤ 261 ∧
    checkedWord (expressionDegree v.expression).1 (expressionDegree v.expression).2 v.index =
      some (expressionWord v.expression)
private noncomputable instance (v : BasisValue) : Decidable (rowValid v) := by
  dsimp only [rowValid]
  infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem basisValues_checked :
    basisValues.all (fun v => decide (rowValid v)) = true := by
  decide

end
end KIP126.Computation.Table
