module

import KIP126.AdamsComputation.Basis
import all KIP126.AdamsComputation.Internal.ArchiveData.Generators
import all KIP126.AdamsComputation.Internal.ArchiveData.Dimensions

/-! Typed syntax and degree verification for the fixed S⁰ archive,
using its generator catalogue and dimension data. -/

@[expose] section
namespace KIP126.Computation.StandardArchive
open CategoryTheory KIP126.Computation
set_option backward.privateInPublic true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private noncomputable def generators : GeneratorCatalogue where
  count := CachedStandard.archiveGeneratorCount
  record := CachedStandard.archiveGeneratorRecord

private noncomputable abbrev basisCount : ℕ → ℕ → ℕ := CachedStandard.archiveBasisCount

private def regradeMonomial {G : GeneratorCatalogue} {s t s' t' : ℕ}
    (hs : s=s') (ht : t=t') (x : SourceMonomial G s t) : SourceMonomial G s' t' :=
  hs ▸ ht ▸ x

private inductive BasisRows (G : GeneratorCatalogue) (t : ℕ) : ℕ → Type
  | nil {s : ℕ} : BasisRows G t s
  | cons {s : ℕ} (head : List (SourceMonomial G s t))
      (tail : BasisRows G t (s+1)) : BasisRows G t s

private def BasisRows.counts {G : GeneratorCatalogue} {t s : ℕ} :
    BasisRows G t s → List ℕ
  | .nil => []
  | .cons head tail => head.length :: tail.counts

private def BasisRows.get {G : GeneratorCatalogue} {t s : ℕ} :
    (R : BasisRows G t s) → (i : ℕ) → List (SourceMonomial G (s+i) t)
  | .nil, _ => []
  | .cons head _, 0 => head
  | .cons _ tail, i+1 =>
    (tail.get i).map (regradeMonomial (by omega) rfl)

private theorem BasisRows.get_length {G : GeneratorCatalogue} {t s : ℕ}
    (R : BasisRows G t s) (i : ℕ) :
    (R.get i).length = ((R.counts[i]?).getD 0) := by
  induction R generalizing i with
  | nil => rfl
  | @cons s head tail ih =>
    cases i with
    | zero => rfl
    | succ i =>
      dsimp only [BasisRows.get, BasisRows.counts]
      simpa only [List.length_map, List.getElem?_cons_succ] using ih i

private def BasisRows.regrade {G : GeneratorCatalogue} {t t' s : ℕ}
    (h : t=t') (R : BasisRows G t s) : BasisRows G t' s := h ▸ R

private theorem BasisRows.regrade_counts {G : GeneratorCatalogue} {t t' s : ℕ}
    (h : t=t') (R : BasisRows G t s) : (R.regrade h).counts = R.counts := by
  cases h
  rfl

private inductive BasisTable (G : GeneratorCatalogue) : ℕ → Type
  | nil {t : ℕ} : BasisTable G t
  | cons {t : ℕ} (head : BasisRows G t 0) (tail : BasisTable G (t+1)) : BasisTable G t

private def BasisTable.counts {G : GeneratorCatalogue} {t : ℕ} :
    BasisTable G t → List (List ℕ)
  | .nil => []
  | .cons head tail => head.counts :: tail.counts

private def BasisTable.get {G : GeneratorCatalogue} {t : ℕ} :
    (T : BasisTable G t) → (i : ℕ) → BasisRows G (t+i) 0
  | .nil, _ => .nil
  | .cons head _, 0 => head
  | .cons _ tail, i+1 => (tail.get i).regrade (by omega)

private theorem BasisTable.get_counts {G : GeneratorCatalogue} {t : ℕ}
    (T : BasisTable G t) (i : ℕ) :
    (T.get i).counts = ((T.counts[i]?).getD []) := by
  induction T generalizing i with
  | nil => rfl
  | @cons t head tail ih =>
    cases i with
    | zero => rfl
    | succ i =>
      dsimp only [BasisTable.get, BasisTable.counts]
      simpa only [BasisRows.regrade_counts, List.getElem?_cons_succ] using ih i

private def BasisTable.monomials {G : GeneratorCatalogue} (T : BasisTable G 0)
    (s t : ℕ) : List (SourceMonomial G s t) :=
  ((T.get t).get s).map (regradeMonomial (Nat.zero_add s) (Nat.zero_add t))

private theorem BasisTable.monomials_length {G : GeneratorCatalogue} (T : BasisTable G 0)
    (s t : ℕ) :
    (T.monomials s t).length = (((T.counts[t]?).getD [])[s]?).getD 0 := by
  dsimp only [BasisTable.monomials]
  rw [List.length_map, BasisRows.get_length, BasisTable.get_counts]


end KIP126.Computation.StandardArchive
