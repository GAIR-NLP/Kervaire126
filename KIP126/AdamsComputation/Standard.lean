module

public import KIP126.AdamsComputation.Basis

public import KIP126.AdamsSynthetic.Completed.Background
public import KIP126.Literature
import KIP126.Literature.E2Exactness.NuAction
import all KIP126.Literature.E2Exactness.ClassicalSuspension
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Batteries.Data.String.Lemmas
import Mathlib.Tactic.LinearCombination
import all Init.Data.List.SplitOn.Basic
import all KIP126.AdamsComputation.Internal.RelationCertificate
public import KIP126.AdamsComputation.Internal.ArchiveData
import all KIP126.AdamsComputation.Internal.ArchiveData
public import KIP126.AdamsComputation.Internal.SphereArchive
import all KIP126.AdamsComputation.Internal.SphereArchive
public import KIP126.AdamsComputation.Internal.SphereArchive.Basic
import all KIP126.AdamsComputation.Internal.SphereArchive.Basic
import all KIP126.AdamsComputation.Internal.SphereArchive.Generators
public import KIP126.AdamsComputation.Internal.NativeAlgebra
import all KIP126.AdamsComputation.Internal.NativeAlgebra
import all KIP126.AdamsComputation.Internal.FixedRelations
import all KIP126.AdamsComputation.Internal.GeneratorCertificates
import all KIP126.AdamsComputation.Internal.TInvariant
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

/-! The fixed sphere algebra combines the finite coordinate data, native
quotient operations and sphere realization. Its E₂ construction is independent
of later-page spectral-sequence conclusions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true

@[expose] section
namespace KIP126.Computation.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed

section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

set_option backward.privateInPublic true in
/-- The complete sphere generator catalogue, with names and bidegrees. -/
public noncomputable def generators : GeneratorCatalogue := KIP126.Computation.StandardArchive.generators

public noncomputable def atomIndex (a : Atom) : Fin generators.count :=
  match a with
  | .h0 => ⟨0, by decide⟩
  | .h1 => ⟨1, by decide⟩
  | .h6 => ⟨69, by decide⟩
  | .h2 => ⟨2, by decide⟩
  | .h4 => ⟨7, by decide⟩
  | .h5 => ⟨18, by decide⟩
  | .h3 => ⟨3, by decide⟩
  | .h7 => ⟨324, by decide⟩
  | .g => ⟨13, by decide⟩
  | .e0 => ⟨9, by decide⟩
  | .delta_h_1_mul_g => ⟨51, by decide⟩
  | .delta_h_6_mul_g => ⟨251, by decide⟩
  | .M_mul_d_0 => ⟨79, by decide⟩
  | .b4 => ⟨80, by decide⟩
  | .b => ⟨82, by decide⟩
  | .x_91_11 => ⟨188, by decide⟩
  | .x_94_8 => ⟨190, by decide⟩
  | .x_109_12 => ⟨275, by decide⟩
  | .x_121_7 => ⟨323, by decide⟩
  | .x_125_5 => ⟨340, by decide⟩
  | .x_126_4 => ⟨341, by decide⟩
  | .x_123_8 => ⟨352, by decide⟩
  | .x_123_9 => ⟨366, by decide⟩
  | .x_124_8 => ⟨367, by decide⟩
  | .x_126_6 => ⟨368, by decide⟩
  | .x_125_8 => ⟨375, by decide⟩
  | .x_123_11 => ⟨386, by decide⟩
  | .x_123_11_2 => ⟨387, by decide⟩
  | .x_125_9_2 => ⟨391, by decide⟩
  | .x_126_8 => ⟨392, by decide⟩
  | .x_126_8_2 => ⟨393, by decide⟩
  | .x_126_8_4 => ⟨395, by decide⟩
  | .x_123_13_2 => ⟨418, by decide⟩
  | .x_122_15_2 => ⟨424, by decide⟩
  | .x_121_17 => ⟨436, by decide⟩
  | .x_122_16 => ⟨437, by decide⟩

public theorem atom_record (a : Atom) :
    ((atomIndex a).val, generators.record (atomIndex a)) = a.record := by
  cases a <;> rfl

end
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
set_option backward.privateInPublic true in
public noncomputable def basisCount : ℕ → ℕ → ℕ := CachedStandard.archiveBasisCount

set_option backward.privateInPublic true in
public noncomputable def basisMonomial (s t : ℕ) (i : Fin (basisCount s t)) :
    SourceMonomial generators s t := KIP126.Computation.StandardArchive.basisMonomialImplementation s t i

/-- The one fixed archive, retaining all generators and every bounded monomial. -/
public noncomputable def archive : SphereArchive where
  generators := generators
  atomIndex := atomIndex
  atom_record := atom_record
  basisCount := basisCount
  basisMonomial := basisMonomial

/- The untruncated quotient by 231848 defining relations, with weighted
homogeneous components, multiplication and unit. Generator weights come
from the complete catalogue. -/




noncomputable section NativeSourceAlgebraConstruction
set_option backward.privateInPublic true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/- These aliases refer to the same fixed algebra data. -/
private abbrev nativePoly := CachedStandard.nativePoly
private abbrev nativePolynomialOfPowers := CachedStandard.nativePolynomialOfPowers
private abbrev nativeMonomialOfString := CachedStandard.nativeMonomialOfString
private abbrev nativeRelationPolynomial := CachedStandard.nativeRelationPolynomial
private abbrev nativeIdeal := CachedStandard.nativeIdeal
private abbrev nativeAlgebra := CachedStandard.nativeAlgebra
private abbrev nativeProjection := CachedStandard.nativeProjection
private abbrev nativePart := CachedStandard.nativePart
private abbrev nativeComponent := CachedStandard.nativeComponent
private abbrev nativeProduct := CachedStandard.nativeProduct
private abbrev nativeUnit := CachedStandard.nativeUnit
private abbrev archiveSourceFirstRelations := CachedStandard.archiveSourceFirstRelations
private abbrev archiveSourceRelationChunks := CachedStandard.archiveSourceRelationChunks
private abbrev archiveSourceRelations := CachedStandard.archiveSourceRelations

private def sourceComponentConstruction (s t : ℕ) : ModuleCat.{0} (ZMod 2) :=
  nativeComponent generators.count generators.degree archiveSourceRelations s t

private def sourceProductConstruction (s t s' t' : ℕ) :
    sourceComponentConstruction s t →ₗ[ZMod 2] sourceComponentConstruction s' t' →ₗ[ZMod 2]
      sourceComponentConstruction (s+s') (t+t') :=
  nativeProduct generators.count generators.degree archiveSourceRelations s t s' t'

private def sourceUnitConstruction : sourceComponentConstruction 0 0 :=
  nativeUnit generators.count generators.degree archiveSourceRelations

private theorem sourceComponentConstruction_carrier (s t : ℕ) :
    (sourceComponentConstruction s t : Type) =
      ↥(nativePart generators.count generators.degree archiveSourceRelations s t) := rfl

private theorem sourceProductConstruction_val (s t s' t' : ℕ)
    (x : sourceComponentConstruction s t) (y : sourceComponentConstruction s' t') :
    (sourceProductConstruction s t s' t' x y).val=x.val*y.val := rfl

private theorem sourceUnitConstruction_val :
    sourceUnitConstruction.val=(1 : nativeAlgebra generators.count archiveSourceRelations) := rfl

private def sourceAtomConstruction (a : Atom) :
    sourceComponentConstruction a.degree.1 a.degree.2 := by
  let i := atomIndex a
  have hi : generators.degree i=a.degree :=
    congrArg (fun r : ℕ × String × ℕ × ℕ=>r.2.2) (atom_record a)
  refine ⟨nativeProjection generators.count archiveSourceRelations (MvPolynomial.X i),?_⟩
  apply Submodule.mem_map.mpr
  refine ⟨MvPolynomial.X i,?_,rfl⟩
  have h := MvPolynomial.isWeightedHomogeneous_X (ZMod 2) generators.degree i
  rw [hi] at h
  exact h

private theorem sourceAtomConstruction_val (a : Atom) :
    (sourceAtomConstruction a).val = nativeProjection generators.count archiveSourceRelations
      (MvPolynomial.X (atomIndex a)) := rfl

end NativeSourceAlgebraConstruction

set_option backward.privateInPublic true in
public noncomputable def sourceComponent : ℕ → ℕ → ModuleCat.{0} (ZMod 2) :=
  sourceComponentConstruction
set_option backward.privateInPublic true in
public noncomputable def sourceProduct (s t s' t' : ℕ) :
    sourceComponent s t →ₗ[ZMod 2] sourceComponent s' t' →ₗ[ZMod 2]
      sourceComponent (s+s') (t+t') :=
  @id (sourceComponent s t →ₗ[ZMod 2] sourceComponent s' t' →ₗ[ZMod 2]
    sourceComponent (s+s') (t+t')) (sourceProductConstruction s t s' t')
set_option backward.privateInPublic true in
public noncomputable def sourceUnit : sourceComponent 0 0 := sourceUnitConstruction
set_option backward.privateInPublic true in
public noncomputable def sourceAtom (a : Atom) : sourceComponent a.degree.1 a.degree.2 :=
  sourceAtomConstruction a
public noncomputable def sourceData : ProgramData.{0} where
  component := sourceComponent
  product := sourceProduct
  unit := sourceUnit
  atom := sourceAtom
/- Recover each source generator at its exact fixed CSV singleton address.
The source coordinates and their basis-value compatibility belong to the
same source algebra, with the designated atoms retained. -/
section SourceGeneratorConstruction
set_option backward.privateInPublic true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
private abbrev singletonBasisIndex := CachedStandard.singletonBasisIndex

private theorem singletonBasisIndex_valid : ∀ i : Fin archive.generators.count,
    (archive.generators.degree i).2 ≤ 261 ∧
    singletonBasisIndex i < archive.basisCount
      (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  CachedStandard.singletonBasisIndex_valid

open CategoryTheory
private noncomputable def sourceAtomGenerator (a : Atom) :
    sourceData.component (archive.generators.degree (archive.atomIndex a)).1
      (archive.generators.degree (archive.atomIndex a)).2 :=
  (eqToHom (congrArg (fun d : ℕ × ℕ => sourceData.component d.1 d.2)
    (archive.atom_degree a).symm)) (sourceData.atom a)

private noncomputable def preferSourceAtom (a : Atom) (i : Fin archive.generators.count)
    (otherwise : sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  if h : i = archive.atomIndex a then h.symm ▸ sourceAtomGenerator a else otherwise

private noncomputable def sourceGeneratorAtoms
    (otherwise : ∀ i : Fin archive.generators.count,
      sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2)
    (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  preferSourceAtom .h0 i (preferSourceAtom .h1 i (preferSourceAtom .h6 i (preferSourceAtom .h2 i (preferSourceAtom .h4 i (preferSourceAtom .h5 i (preferSourceAtom .h3 i (preferSourceAtom .h7 i (preferSourceAtom .g i (preferSourceAtom .e0 i (preferSourceAtom .delta_h_1_mul_g i (preferSourceAtom .delta_h_6_mul_g i (preferSourceAtom .M_mul_d_0 i (preferSourceAtom .b4 i (preferSourceAtom .b i (preferSourceAtom .x_91_11 i (preferSourceAtom .x_94_8 i (preferSourceAtom .x_109_12 i (preferSourceAtom .x_121_7 i (preferSourceAtom .x_125_5 i (preferSourceAtom .x_126_4 i (preferSourceAtom .x_123_8 i (preferSourceAtom .x_123_9 i (preferSourceAtom .x_124_8 i (preferSourceAtom .x_126_6 i (preferSourceAtom .x_125_8 i (preferSourceAtom .x_123_11 i (preferSourceAtom .x_123_11_2 i (preferSourceAtom .x_125_9_2 i (preferSourceAtom .x_126_8 i (preferSourceAtom .x_126_8_2 i (preferSourceAtom .x_126_8_4 i (preferSourceAtom .x_123_13_2 i (preferSourceAtom .x_122_15_2 i (preferSourceAtom .x_121_17 i (preferSourceAtom .x_122_16 i (otherwise i))))))))))))))))))))))))))))))))))))

private theorem sourceGeneratorAtoms_agrees
    (otherwise : ∀ i : Fin archive.generators.count,
      sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2)
    (a : Atom) :
    (eqToHom (congrArg (fun d : ℕ × ℕ => sourceData.component d.1 d.2)
      (archive.atom_degree a)))
      (sourceGeneratorAtoms otherwise (archive.atomIndex a)) = sourceData.atom a := by
  cases a <;> rfl

private abbrev SourceCoordinates := ∀ (s t : ℕ), t ≤ 261 →
  sourceData.component s t ≃ₗ[ℤ] (Fin (archive.basisCount s t) →₀ ZMod 2)

private noncomputable def coordinateGeneratorFor (coordinates : SourceCoordinates)
    (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  (coordinates (archive.generators.degree i).1 (archive.generators.degree i).2
    (singletonBasisIndex_valid i).1).symm
      (Finsupp.single ⟨singletonBasisIndex i, (singletonBasisIndex_valid i).2⟩ 1)

private noncomputable def sourceGeneratorFor (coordinates : SourceCoordinates)
    (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  sourceGeneratorAtoms (coordinateGeneratorFor coordinates) i

private structure SourceCoordinateData where
  coordinates : SourceCoordinates
  basis_values : ∀ (s t : ℕ) (ht : t ≤ 261) (i : Fin (archive.basisCount s t)),
    (coordinates s t ht).symm (Finsupp.single i 1) =
      (archive.basisMonomial s t i).value sourceData (sourceGeneratorFor coordinates)

private noncomputable def sourceCoordinateConstruction : SourceCoordinateData where
  coordinates := by sorry
  basis_values := by sorry

public noncomputable def sourceCoordinates (s t : ℕ) (ht : t ≤ 261) :
    sourceData.component s t ≃ₗ[ℤ] (Fin (archive.basisCount s t) →₀ ZMod 2) :=
  sourceCoordinateConstruction.coordinates s t ht

private noncomputable def coordinateGenerator (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  coordinateGeneratorFor sourceCoordinates i

private noncomputable def sourceGeneratorImplementation (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  sourceGeneratorAtoms coordinateGenerator i


end SourceGeneratorConstruction

set_option backward.privateInPublic true in
public noncomputable def sourceGenerator (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  sourceGeneratorImplementation i
public theorem sourceAtom_agrees (a : Atom) :
    (eqToHom (congrArg (fun d : ℕ × ℕ => sourceData.component d.1 d.2)
      (archive.atom_degree a))) (sourceGenerator (archive.atomIndex a)) = sourceData.atom a := by
  dsimp only [sourceGenerator, sourceGeneratorImplementation]
  exact sourceGeneratorAtoms_agrees coordinateGenerator a
public theorem sourceBasis_values (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (sourceCoordinates s t ht).symm (Finsupp.single i 1) =
      (archive.basisMonomial s t i).value sourceData sourceGenerator := by
  exact sourceCoordinateConstruction.basis_values s t ht i

private noncomputable def sourceBasis : SourceBasisSpecification sourceData archive where
  generator := sourceGenerator
  atom_agrees := sourceAtom_agrees
  coordinates := sourceCoordinates
  basis_values := sourceBasis_values

private structure SphereComparisonData where
  comparison : ∀ (s t : ℕ), t ≤ 261 →
    sourceData.component s t ≃ₗ[ℤ] background.classical.sphere.Page 2 (s,t)
  comparison_product : ∀ (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : sourceData.component s t) (y : sourceData.component s' t'),
    comparison (s+s') (t+t') ht (sourceData.product s t s' t' x y) =
      background.sphereAlgebra.product (s,t) (s',t')
        (comparison s t (Nat.le_trans (Nat.le_add_right t t') ht) x)
        (comparison s' t' (Nat.le_trans (Nat.le_add_left t' t) ht) y)

private noncomputable def sphereComparisonConstruction : SphereComparisonData where
  comparison := by sorry
  comparison_product := by sorry

set_option backward.privateInPublic true in
/-- Comparison with the actual project sphere; its bounded range is explicit. -/
public noncomputable def comparison (s t : ℕ) (ht : t ≤ 261) :
    sourceData.component s t ≃ₗ[ℤ] background.classical.sphere.Page 2 (s,t) := by
  exact sphereComparisonConstruction.comparison s t ht
public theorem comparison_product (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : sourceData.component s t) (y : sourceData.component s' t') :
    comparison (s+s') (t+t') ht (sourceData.product s t s' t' x y) =
      background.sphereAlgebra.product (s,t) (s',t')
        (comparison s t (by omega) x) (comparison s' t' (by omega) y) := by
  exact sphereComparisonConstruction.comparison_product s t s' t' ht x y
public theorem comparison_unit : comparison 0 0 (by decide) sourceData.unit =
    background.sphereAlgebra.unit := by
  let e := comparison 0 0 (by decide)
  let u := e.symm background.sphereAlgebra.unit
  have hu : e u = background.sphereAlgebra.unit := e.apply_symm_apply _
  have hs : sourceData.product 0 0 0 0 sourceData.unit u = u := by
    apply Subtype.ext
    change 1 * u.val = u.val
    exact one_mul _
  have h := comparison_product 0 0 0 0 (by decide) sourceData.unit u
  change e (sourceData.product 0 0 0 0 sourceData.unit u) =
    background.sphereAlgebra.product (0,0) (0,0) (e sourceData.unit) (e u) at h
  rw [hs, hu] at h
  exact (eq_of_heq (background.sphereAlgebra.unit_right (0,0) (e sourceData.unit))).symm.trans h.symm

public theorem comparison_h0 : comparison 1 1 (by decide) (sourceData.atom .h0) =
    background.standardClasses.standardHi 0 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH0Source :
      (sourceCoordinates 1 1 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 1)) 1) =
        sourceData.atom .h0 := by
    exact sourceBasis_values 1 1 (by decide) ⟨0, by decide⟩

  have hiCalibrationH0Nonzero : background.standardClasses.standardHi 0 ≠ 0 :=
    background.standardClasses.hi_ne_zero 0 (by decide)

  let q := sourceCoordinates 1 1 (by decide)
  let c := comparison 1 1 (by decide)
  have hs : sourceData.atom .h0 ≠ 0 := by
    intro hz
    have h := hiCalibrationH0Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 1 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 1)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 1) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h0)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h0) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 0) ≠ 0 := by
    intro hz
    exact hiCalibrationH0Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy
public theorem comparison_h1 : comparison 1 2 (by decide) (sourceData.atom .h1) =
    background.standardClasses.standardHi 1 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH1Source :
      (sourceCoordinates 1 2 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 2)) 1) =
        sourceData.atom .h1 := by
    exact sourceBasis_values 1 2 (by decide) ⟨0, by decide⟩

  have hiCalibrationH1Nonzero : background.standardClasses.standardHi 1 ≠ 0 :=
    background.standardClasses.hi_ne_zero 1 (by decide)

  let q := sourceCoordinates 1 2 (by decide)
  let c := comparison 1 2 (by decide)
  have hs : sourceData.atom .h1 ≠ 0 := by
    intro hz
    have h := hiCalibrationH1Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 2 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 2)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 2) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h1)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h1) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 1) ≠ 0 := by
    intro hz
    exact hiCalibrationH1Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy
public theorem comparison_h2 : comparison 1 4 (by decide) (sourceData.atom .h2) =
    background.standardClasses.standardHi 2 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH2Source :
      (sourceCoordinates 1 4 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 4)) 1) =
        sourceData.atom .h2 := by
    exact sourceBasis_values 1 4 (by decide) ⟨0, by decide⟩

  have hiCalibrationH2Nonzero : background.standardClasses.standardHi 2 ≠ 0 :=
    background.standardClasses.hi_ne_zero 2 (by decide)

  let q := sourceCoordinates 1 4 (by decide)
  let c := comparison 1 4 (by decide)
  have hs : sourceData.atom .h2 ≠ 0 := by
    intro hz
    have h := hiCalibrationH2Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 4 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 4)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 4) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h2)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h2) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 2) ≠ 0 := by
    intro hz
    exact hiCalibrationH2Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy
public theorem comparison_h4 : comparison 1 16 (by decide) (sourceData.atom .h4) =
    background.standardClasses.standardHi 4 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH4Source :
      (sourceCoordinates 1 16 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 16)) 1) =
        sourceData.atom .h4 := by
    exact sourceBasis_values 1 16 (by decide) ⟨0, by decide⟩

  have hiCalibrationH4Nonzero : background.standardClasses.standardHi 4 ≠ 0 :=
    background.standardClasses.hi_ne_zero 4 (by decide)

  let q := sourceCoordinates 1 16 (by decide)
  let c := comparison 1 16 (by decide)
  have hs : sourceData.atom .h4 ≠ 0 := by
    intro hz
    have h := hiCalibrationH4Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 16 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 16)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 16) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h4)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h4) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 4) ≠ 0 := by
    intro hz
    exact hiCalibrationH4Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy
public theorem comparison_h5 : comparison 1 32 (by decide) (sourceData.atom .h5) =
    background.standardClasses.standardHi 5 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH5Source :
      (sourceCoordinates 1 32 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 32)) 1) =
        sourceData.atom .h5 := by
    exact sourceBasis_values 1 32 (by decide) ⟨0, by decide⟩

  have hiCalibrationH5Nonzero : background.standardClasses.standardHi 5 ≠ 0 :=
    background.standardClasses.hi_ne_zero 5 (by decide)

  let q := sourceCoordinates 1 32 (by decide)
  let c := comparison 1 32 (by decide)
  have hs : sourceData.atom .h5 ≠ 0 := by
    intro hz
    have h := hiCalibrationH5Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 32 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 32)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 32) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h5)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h5) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 5) ≠ 0 := by
    intro hz
    exact hiCalibrationH5Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy
public theorem comparison_h6 : comparison 1 64 (by decide) (sourceData.atom .h6) =
    background.standardClasses.standardH6 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH6Source :
      (sourceCoordinates 1 64 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 64)) 1) =
        sourceData.atom .h6 := by
    exact sourceBasis_values 1 64 (by decide) ⟨0, by decide⟩

  have hiCalibrationH6Nonzero : background.standardClasses.standardHi 6 ≠ 0 :=
    background.standardClasses.hi_ne_zero 6 (by decide)

  let q := sourceCoordinates 1 64 (by decide)
  let c := comparison 1 64 (by decide)
  have hs : sourceData.atom .h6 ≠ 0 := by
    intro hz
    have h := hiCalibrationH6Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 64 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 64)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 64) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h6)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h6) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 6) ≠ 0 := by
    intro hz
    exact hiCalibrationH6Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy

public theorem comparison_h3 : comparison 1 8 (by decide) (sourceData.atom .h3) =
    background.standardClasses.standardHi 3 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH3Source :
      (sourceCoordinates 1 8 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 8)) 1) =
        sourceData.atom .h3 := by
    exact sourceBasis_values 1 8 (by decide) ⟨0, by decide⟩

  have hiCalibrationH3Nonzero : background.standardClasses.standardHi 3 ≠ 0 :=
    background.standardClasses.hi_ne_zero 3 (by decide)

  let q := sourceCoordinates 1 8 (by decide)
  let c := comparison 1 8 (by decide)
  have hs : sourceData.atom .h3 ≠ 0 := by
    intro hz
    have h := hiCalibrationH3Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 8 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 8)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 8) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h3)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h3) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 3) ≠ 0 := by
    intro hz
    exact hiCalibrationH3Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy
public theorem comparison_h7 : comparison 1 128 (by decide) (sourceData.atom .h7) =
    background.standardClasses.standardHi 7 := by
  have hiCalibrationF2Cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
    have hlt := ZMod.val_lt x
    have h : x.val = 0 ∨ x.val = 1 := by omega
    rcases h with h | h
    · left
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h

  have hiCalibrationOneCoordinate (f : Fin 1 →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single 0 1 := by
    rcases hiCalibrationF2Cases (f 0) with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa only [Finsupp.single_eq_same] using h

  have hiCalibrationUnique (x y : Fin 1 →₀ ZMod 2)
      (hx : x ≠ 0) (hy : y ≠ 0) : x = y := by
    rcases hiCalibrationOneCoordinate x with h | h
    · exact (hx h).elim
    rcases hiCalibrationOneCoordinate y with h' | h'
    · exact (hy h').elim
    exact h.trans h'.symm

  have hiCalibrationH7Source :
      (sourceCoordinates 1 128 (by decide)).symm
        (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 128)) 1) =
        sourceData.atom .h7 := by
    exact sourceBasis_values 1 128 (by decide) ⟨0, by decide⟩

  have hiCalibrationH7Nonzero : background.standardClasses.standardHi 7 ≠ 0 :=
    background.standardClasses.hi_ne_zero 7 (by decide)

  let q := sourceCoordinates 1 128 (by decide)
  let c := comparison 1 128 (by decide)
  have hs : sourceData.atom .h7 ≠ 0 := by
    intro hz
    have h := hiCalibrationH7Source
    rw [hz] at h
    have hz' := congrArg (sourceCoordinates 1 128 (by decide)) h
    have hz'' : (Finsupp.single (⟨0, by decide⟩ : Fin (archive.basisCount 1 128)) (1 : ZMod 2)) = 0 := by
      exact (q.apply_symm_apply _).symm.trans (hz'.trans (map_zero q))
    have hf := congrArg (fun f : Fin (archive.basisCount 1 128) →₀ ZMod 2 => f ⟨0, by decide⟩) hz''
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hf)
  let e := c.symm.trans q
  have hcx : e (c (sourceData.atom .h7)) ≠ 0 := by
    intro hz
    have hzero : c (sourceData.atom .h7) = 0 := e.injective (hz.trans (map_zero e).symm)
    exact hs (c.injective (hzero.trans (map_zero c).symm))
  have hhy : e (background.standardClasses.standardHi 7) ≠ 0 := by
    intro hz
    exact hiCalibrationH7Nonzero (e.injective (hz.trans (map_zero e).symm))
  apply e.injective
  exact hiCalibrationUnique _ _ hcx hhy
/-- Archived generator in the native source algebra. -/
public noncomputable def sourceHi (i : ℕ) (hiBound : i ≤ 7 := by omega) :
    sourceData.component 1 (2 ^ i) :=
  (eqToHom (congrArg (fun d : ℕ × ℕ => sourceData.component d.1 d.2)
    (Atom.ofHi_degree ⟨i, by omega⟩))) (sourceData.atom (Atom.ofHi ⟨i, by omega⟩))

/-- All eight data generators agree with the finite fixed Adams classes. -/
public theorem comparison_hi (i : ℕ) (hiBound : i ≤ 7) :
    comparison 1 (2 ^ i) (by interval_cases i <;> decide) (sourceHi i hiBound) =
      background.standardClasses.standardHi i hiBound := by
  interval_cases i
  · exact comparison_h0
  · exact comparison_h1
  · exact comparison_h2
  · exact comparison_h3
  · exact comparison_h4
  · exact comparison_h5
  · exact comparison_h6
  · exact comparison_h7

private noncomputable def presentation : SpherePresentation background sourceData where
  comparison := comparison
  comparison_product := comparison_product
  comparison_unit := comparison_unit
  h0 := comparison_h0
  h1 := comparison_h1
  h2 := comparison_h2
  h4 := comparison_h4
  h5 := comparison_h5
  h6 := comparison_h6
public noncomputable def atom (a : Atom) :
    background.classical.sphere.Page 2 (a.degree.1,a.degree.2) :=
  comparison a.degree.1 a.degree.2 (by cases a <;> decide) (sourceData.atom a)

public noncomputable abbrev h0 : background.classical.sphere.Page 2 (1,1) := background.standardClasses.standardHi 0
public noncomputable abbrev h1 : background.classical.sphere.Page 2 (1,2) := background.standardClasses.standardHi 1
public noncomputable abbrev h2 : background.classical.sphere.Page 2 (1,4) := background.standardClasses.standardHi 2
public noncomputable abbrev h4 : background.classical.sphere.Page 2 (1,16) := background.standardClasses.standardHi 4
public noncomputable abbrev h5 : background.classical.sphere.Page 2 (1,32) := background.standardClasses.standardHi 5
public noncomputable abbrev h6 := background.standardClasses.standardH6
public noncomputable abbrev h6Square := background.standardClasses.standardH6Square

public noncomputable def product {p q r : Bidegree}
    (x : background.classical.sphere.Page 2 p) (y : background.classical.sphere.Page 2 q)
    (h : p + q = r := by decide) : background.classical.sphere.Page 2 r :=
  (eqToHom (congrArg (background.classical.sphere.Page 2) h))
    (background.sphereAlgebra.product p q x y)

public noncomputable def h0Square : background.classical.sphere.Page 2 (2,2) :=
  product h0 h0
public noncomputable def h0Six : background.classical.sphere.Page 2 (6,6) :=
  product (product (r := (4,4)) h0Square h0Square) h0Square
public noncomputable def h5Square : background.classical.sphere.Page 2 (2,64) :=
  product h5 h5
public noncomputable def W : background.classical.sphere.Page 2 (8,134) :=
  atom .x_126_8_4 + atom .x_126_8
public noncomputable def U : background.classical.sphere.Page 2 (10,134) :=
  product h0Square (atom .x_124_8)
public noncomputable def T : background.classical.sphere.Page 2 (14,139) :=
  product h1 (product (r := (13,137)) h4 (atom .x_109_12))
public noncomputable def V : background.classical.sphere.Page 2 (9,132) :=
  atom .x_123_9 + product (r := (9,132)) h0 (atom .x_123_8)
public noncomputable def Y : background.classical.sphere.Page 2 (11,136) :=
  product h0Square (atom .x_125_9_2)
public noncomputable def X : background.classical.sphere.Page 2 (8,130) :=
  product h1 (atom .x_121_7)
public noncomputable def P : background.classical.sphere.Page 2 (11,133) :=
  product h6 (atom .M_mul_d_0)
public noncomputable def Q : background.classical.sphere.Page 2 (12,134) :=
  product h5 (atom .x_91_11)
public noncomputable def correction : background.classical.sphere.Page 2 (13,137) :=
  product (atom .e0) (atom .delta_h_6_mul_g)
public noncomputable def highClass : background.classical.sphere.Page 2 (25,150) :=
  product (product (r := (16,96)) (product (r := (8,48)) (atom .g) (atom .g))
    (product (r := (8,48)) (atom .g) (atom .g))) (atom .delta_h_1_mul_g)
public noncomputable def d2Target : background.classical.sphere.Page 2 (10,134) :=
  product (r := (10,134)) h1 V + U
public noncomputable def d3Candidate : background.classical.sphere.Page 2 (9,134) :=
  product h5 (atom .x_94_8)
public noncomputable def d3OtherCandidate : background.classical.sphere.Page 2 (9,134) :=
  d3Candidate + product (r := (9,134)) h6 (atom .b)

public theorem atom_h0 : atom .h0 = h0  := presentation.h0
public theorem atom_h1 : atom .h1 = h1  := presentation.h1
public theorem atom_h2 : atom .h2 = h2  := presentation.h2
public theorem atom_h4 : atom .h4 = h4  := presentation.h4
public theorem atom_h5 : atom .h5 = h5  := presentation.h5
public theorem atom_h6 : atom .h6 = h6  := presentation.h6

/-- The complete actual-page coordinates, including spanning and independence. -/
public noncomputable def coordinates (s t : ℕ) (ht : t ≤ 261) :
    background.classical.sphere.Page 2 (s,t) ≃ₗ[ℤ] (Fin (archive.basisCount s t) →₀ ZMod 2) :=
  (comparison s t ht).symm.trans (sourceCoordinates s t ht)

public noncomputable def comparisonF2 (s t : ℕ) (ht : t ≤ 261) :
    letI := background.sphereAlgebra.scalar (s,t)
    sourceData.component s t ≃ₗ[ZMod 2] background.classical.sphere.Page 2 (s,t) :=
  by
  letI := background.sphereAlgebra.scalar (s,t)
  exact { (comparison s t ht).toAddEquiv with
    map_smul' := fun a x => ZMod.map_smul (comparison s t ht).toAddMonoidHom a x }

public theorem coordinates_basis (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (coordinates s t ht).symm (Finsupp.single i 1) =
      comparison s t ht ((archive.basisMonomial s t i).value sourceData sourceGenerator) :=
  presentation.coordinates_basis sourceBasis s t ht i

public theorem comparison_symm_coordinates_basis (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (comparison s t ht).symm ((coordinates s t ht).symm (Finsupp.single i 1)) =
      (archive.basisMonomial s t i).value sourceData sourceGenerator :=
  presentation.comparison_symm_coordinates_basis sourceBasis s t ht i

public theorem h6_square : comparison 2 128 (by decide)
    (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)) =
    h6Square := presentation.h6_square

-- Native-quotient zero relations with ideal-membership certificates.
noncomputable section NamedRelationVanishingConstruction
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem powers_pointwise (n : ℕ) (xs : List ℕ) :
    CachedStandard.nativePolynomialOfPowers n xs = nativePolynomialOfPowers n xs := by
  rfl

private theorem powers_function :
    CachedStandard.nativePolynomialOfPowers = nativePolynomialOfPowers := by
  rfl

private theorem monomial_function :
    CachedStandard.nativeMonomialOfString = nativeMonomialOfString := by
  rfl

private theorem relation_function :
    CachedStandard.nativeRelationPolynomial = nativeRelationPolynomial := by
  rfl

private theorem nativeIdeal_eq_cached (n : ℕ) (codes : List String) :
    nativeIdeal n codes = CachedStandard.nativeIdeal n codes := by
  rfl

private noncomputable def nativeEquiv (n : ℕ) (codes : List String) :
    nativeAlgebra n codes ≃ₐ[ZMod 2] CachedStandard.nativeAlgebra n codes :=
  Ideal.quotientEquivAlgOfEq (ZMod 2) (nativeIdeal_eq_cached n codes)

private theorem nativeEquiv_projection (n : ℕ) (codes : List String) (p : nativePoly n) :
    nativeEquiv n codes (nativeProjection n codes p) =
      CachedStandard.nativeProjection n codes p := by
  rfl

private theorem projection_zero_iff (n : ℕ) (codes : List String) (p : nativePoly n) :
    nativeProjection n codes p = 0 ↔ CachedStandard.nativeProjection n codes p = 0 := by
  constructor
  · intro h
    have hh := congrArg (nativeEquiv n codes) h
    simpa only [nativeEquiv_projection, map_zero] using hh
  · intro h
    apply (nativeEquiv n codes).injective
    simpa only [nativeEquiv_projection, map_zero] using h

private theorem generic_relation_zero (n : ℕ) (codes : List String)
    (code : String) (hcode : code ∈ codes) :
    nativeProjection n codes (nativeRelationPolynomial n code) = 0 := by
  apply (projection_zero_iff n codes _).mpr
  rw [← relation_function]
  exact CachedStandard.namedRelationProjectionZero n codes code hcode

private theorem arbitrary_product_nonzero (n : ℕ) (codes : List String)
    (p q : nativePoly n)
    (h : ∀ a : CachedStandard.nativeAlgebra n codes,
      CachedStandard.nativeProjection n codes p * a ≠
        CachedStandard.nativeProjection n codes q)
    (a : nativeAlgebra n codes) :
    nativeProjection n codes p * a ≠ nativeProjection n codes q := by
  intro ha
  apply h (nativeEquiv n codes a)
  have hh := congrArg (nativeEquiv n codes) ha
  simpa only [map_mul, nativeEquiv_projection] using hh


private theorem nativeEquiv_mem_part (n : ℕ) (degree : Fin n → ℕ×ℕ)
    (codes : List String) (s t : ℕ) (x : nativeAlgebra n codes)
    (hx : x ∈ nativePart n degree codes s t) :
    nativeEquiv n codes x ∈ CachedStandard.nativePart n degree codes s t := by
  obtain ⟨p, hp, hx⟩ := hx
  refine ⟨p, hp, ?_⟩
  change nativeProjection n codes p = x at hx
  change CachedStandard.nativeProjection n codes p = nativeEquiv n codes x
  simpa only [nativeEquiv_projection] using congrArg (nativeEquiv n codes) hx

private noncomputable def nativePartToCached (n : ℕ) (degree : Fin n → ℕ×ℕ)
    (codes : List String) (s t : ℕ) (x : nativePart n degree codes s t) :
    CachedStandard.nativePart n degree codes s t :=
  ⟨nativeEquiv n codes x.val, nativeEquiv_mem_part n degree codes s t x.val x.property⟩


private noncomputable def namedProjectionX (i : Fin generators.count) :
    nativeAlgebra generators.count archiveSourceRelations :=
  nativeProjection generators.count archiveSourceRelations (MvPolynomial.X i)


private theorem nativeEquiv_namedProjectionX (i : Fin generators.count) :
    nativeEquiv generators.count archiveSourceRelations (namedProjectionX i) =
      CachedStandard.namedProjectionX i := by rfl


private theorem namedRelation_splitOnAux_char (s : String) (c : Char) (b i : String.Pos.Raw)
    (acc : List String) :
    s.splitOnAux (String.singleton c) b i 0 acc = s.splitAux (· == c) b i acc :=
  CachedStandard.namedRelation_splitOnAux_char s c b i acc

private theorem namedRelation_splitOn_char (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList :=
  CachedStandard.namedRelation_splitOn_char s c

private theorem namedRelation_charlist_middle_member (s code : String) (a c b : List Char)
    (hs : s=String.ofList (a++'\n'::(c++'\n'::b)))
    (hc : String.ofList c=code) (hn : '\n'∉c) : code∈s.splitOn "\n" :=
  CachedStandard.namedRelation_charlist_middle_member s code a c b hs hc hn

private theorem namedRelationProjectionZero (n : ℕ) (codes : List String)
    (code : String) (hcode : code ∈ codes) :
    nativeProjection n codes (nativeRelationPolynomial n code) = 0 :=
  generic_relation_zero n codes code hcode

private theorem namedRelationH5Member : "18,1,82,1" ∈ archiveSourceRelations :=
  CachedStandard.namedRelationH5Member

private theorem namedRelationH02Member : "0,5,391,1" ∈ archiveSourceRelations :=
  CachedStandard.namedRelationH02Member

private theorem namedRelationH03Member : "0,6,375,1" ∈ archiveSourceRelations :=
  CachedStandard.namedRelationH03Member

private theorem namedRelationH1H2Member : "1,1,2,1" ∈ archiveSourceRelations :=
  CachedStandard.namedRelationH1H2Member

private theorem namedRelationH5Zero : (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨18,by decide⟩))^1 * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨82,by decide⟩))^1 = 0 := by
  change (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨18,by decide⟩))^1 * (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨82,by decide⟩))^1 = 0
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedRelationH5Zero

private theorem namedRelationH1H2Zero : (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨1,by decide⟩))^1 * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨2,by decide⟩))^1 = 0 := by
  change (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨1,by decide⟩))^1 * (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨2,by decide⟩))^1 = 0
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedRelationH1H2Zero

private theorem namedRelationH02Zero : (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩))^5 * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨391,by decide⟩))^1 = 0 := by
  change (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩))^5 * (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨391,by decide⟩))^1 = 0
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedRelationH02Zero

private theorem namedRelationH03Zero : (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩))^6 * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨375,by decide⟩))^1 = 0 := by
  change (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩))^6 * (nativeProjection CachedStandard.archiveGeneratorCount CachedStandard.archiveSourceRelations (MvPolynomial.X ⟨375,by decide⟩))^1 = 0
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedRelationH03Zero

private theorem namedSourceH5SquareBZero :
    sourceData.product 2 64 8 70
      (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5))
      (sourceData.atom .b) = 0 := by
  apply Subtype.ext
  change ((nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨18,by decide⟩)) *
    (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨18,by decide⟩))) *
    (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨82,by decide⟩)) = 0
  have hr := namedRelationH5Zero
  simp only [pow_one] at hr
  rw [mul_assoc,hr,mul_zero]

private theorem namedSourceXH2Zero :
    sourceData.product 8 130 1 4
      (sourceData.product 1 2 7 128 (sourceData.atom .h1) (sourceData.atom .x_121_7))
      (sourceData.atom .h2) = 0 := by
  apply Subtype.ext
  change ((nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨1,by decide⟩)) *
    (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨323,by decide⟩))) *
    (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨2,by decide⟩)) = 0
  have hr := namedRelationH1H2Zero
  simp only [pow_one] at hr
  rw [mul_right_comm,hr,zero_mul]

private theorem namedH5SquareBActual :
    background.sphereAlgebra.product (2,64) (8,70) h5Square (atom .b) = 0 := by
  have hsquare := comparison_product 1 32 1 32 (by decide)
    (sourceData.atom .h5) (sourceData.atom .h5)
  change comparison 2 64 _
      (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5)) =
    background.sphereAlgebra.product (1,32) (1,32)
      (comparison 1 32 _ (sourceData.atom .h5)) (comparison 1 32 _ (sourceData.atom .h5)) at hsquare
  rw [comparison_h5] at hsquare
  have h := comparison_product 2 64 8 70 (by decide)
    (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5)) (sourceData.atom .b)
  change comparison 10 134 _ _ = background.sphereAlgebra.product (2,64) (8,70)
    (comparison 2 64 _ (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5)))
    (atom .b) at h
  rw [hsquare,namedSourceH5SquareBZero,map_zero] at h
  exact h.symm

private theorem namedXH2Actual :
    background.sphereAlgebra.product (8,130) (1,4) X h2 = 0 := by
  have hx := comparison_product 1 2 7 128 (by decide)
    (sourceData.atom .h1) (sourceData.atom .x_121_7)
  change comparison 8 130 _ _ = background.sphereAlgebra.product (1,2) (7,128)
    (comparison 1 2 _ (sourceData.atom .h1)) (atom .x_121_7) at hx
  rw [comparison_h1] at hx
  have h := comparison_product 8 130 1 4 (by decide)
    (sourceData.product 1 2 7 128 (sourceData.atom .h1) (sourceData.atom .x_121_7))
    (sourceData.atom .h2)
  change comparison 9 134 _ _ = background.sphereAlgebra.product (8,130) (1,4)
    (comparison 8 130 _ (sourceData.product 1 2 7 128
      (sourceData.atom .h1) (sourceData.atom .x_121_7)))
    (comparison 1 4 _ (sourceData.atom .h2)) at h
  rw [hx,comparison_h2,namedSourceXH2Zero,map_zero] at h
  exact h.symm

private theorem namedSourceH02Zero :
    sourceData.product 5 5 9 134 (sourceData.product 4 4 1 1 (sourceData.product 3 3 1 1 (sourceData.product 2 2 1 1 (sourceData.product 1 1 1 1 (sourceData.atom .h0) (sourceData.atom .h0)) (sourceData.atom .h0)) (sourceData.atom .h0)) (sourceData.atom .h0)) (sourceData.atom .x_125_9_2) = 0 := by
  apply Subtype.ext
  change ((nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩))) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨391,by decide⟩)) = 0
  simpa only [pow_succ,pow_zero,one_mul,pow_one] using namedRelationH02Zero

private theorem namedSourceH03Zero :
    sourceData.product 6 6 8 133 (sourceData.product 5 5 1 1 (sourceData.product 4 4 1 1 (sourceData.product 3 3 1 1 (sourceData.product 2 2 1 1 (sourceData.product 1 1 1 1 (sourceData.atom .h0) (sourceData.atom .h0)) (sourceData.atom .h0)) (sourceData.atom .h0)) (sourceData.atom .h0)) (sourceData.atom .h0)) (sourceData.atom .x_125_8) = 0 := by
  apply Subtype.ext
  change ((nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩)) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨0,by decide⟩))) * (nativeProjection generators.count archiveSourceRelations (MvPolynomial.X ⟨375,by decide⟩)) = 0
  simpa only [pow_succ,pow_zero,one_mul,pow_one] using namedRelationH03Zero


private theorem namedRelationH0H1Member : "0,1,1,1" ∈ archiveSourceRelations :=
  CachedStandard.namedRelationH0H1Member

private theorem namedCorrectionMember25 : "1,1,9,1;0,1,10,1" ∈ archiveSourceRelations :=
  CachedStandard.namedCorrectionMember25

private theorem namedCorrectionMember10177 : "10,1,251,1;4,1,312,1;2,1,18,1,188,1" ∈ archiveSourceRelations :=
  CachedStandard.namedCorrectionMember10177

private theorem namedCorrectionMember10178 : "4,1,312,1;2,1,18,1,188,1;1,2,387,1" ∈ archiveSourceRelations :=
  CachedStandard.namedCorrectionMember10178

private theorem namedCorrectionRelation0 : (namedProjectionX ⟨0,by decide⟩) * (namedProjectionX ⟨1,by decide⟩) = 0 := by
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedCorrectionRelation0

private theorem namedCorrectionRelation25 : (namedProjectionX ⟨1,by decide⟩) * (namedProjectionX ⟨9,by decide⟩) + (namedProjectionX ⟨0,by decide⟩) * (namedProjectionX ⟨10,by decide⟩) = 0 := by
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedCorrectionRelation25

private theorem namedCorrectionRelation10177 : (namedProjectionX ⟨10,by decide⟩) * (namedProjectionX ⟨251,by decide⟩) + (namedProjectionX ⟨4,by decide⟩) * (namedProjectionX ⟨312,by decide⟩) + (namedProjectionX ⟨2,by decide⟩) * (namedProjectionX ⟨18,by decide⟩) * (namedProjectionX ⟨188,by decide⟩) = 0 := by
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedCorrectionRelation10177

private theorem namedCorrectionRelation10178 : (namedProjectionX ⟨4,by decide⟩) * (namedProjectionX ⟨312,by decide⟩) + (namedProjectionX ⟨2,by decide⟩) * (namedProjectionX ⟨18,by decide⟩) * (namedProjectionX ⟨188,by decide⟩) + (namedProjectionX ⟨1,by decide⟩)^2 * (namedProjectionX ⟨387,by decide⟩) = 0 := by
  apply (nativeEquiv _ _).injective
  simpa only [map_mul, map_pow, map_add, map_zero, nativeEquiv_projection,
    nativeEquiv_namedProjectionX] using CachedStandard.namedCorrectionRelation10178

private theorem namedCorrectionRingCertificate {R : Type*} [CommRing R]
    (x0 x1 x2 x4 x9 x10 x18 x188 x251 x312 x387 : R)
    (h0 : x0*x1=0) (h25 : x1*x9+x0*x10=0)
    (h10177 : x10*x251+x4*x312+x2*x18*x188=0)
    (h10178 : x4*x312+x2*x18*x188+x1^2*x387=0) :
    x1*(x9*x251)=0 :=
  CachedStandard.namedCorrectionRingCertificate x0 x1 x2 x4 x9 x10 x18 x188 x251 x312 x387 h0 h25 h10177 h10178

private theorem namedSourceH1CorrectionZero :
    sourceData.product 1 2 13 137 (sourceData.atom .h1)
      (sourceData.product 4 21 9 116 (sourceData.atom .e0) (sourceData.atom .delta_h_6_mul_g)) = 0 := by
  apply Subtype.ext
  change (namedProjectionX ⟨1,by decide⟩) * ((namedProjectionX ⟨9,by decide⟩) * (namedProjectionX ⟨251,by decide⟩)) = 0
  exact namedCorrectionRingCertificate (namedProjectionX ⟨0,by decide⟩) (namedProjectionX ⟨1,by decide⟩) (namedProjectionX ⟨2,by decide⟩) (namedProjectionX ⟨4,by decide⟩) (namedProjectionX ⟨9,by decide⟩) (namedProjectionX ⟨10,by decide⟩) (namedProjectionX ⟨18,by decide⟩) (namedProjectionX ⟨188,by decide⟩) (namedProjectionX ⟨251,by decide⟩) (namedProjectionX ⟨312,by decide⟩) (namedProjectionX ⟨387,by decide⟩)
    namedCorrectionRelation0 namedCorrectionRelation25 namedCorrectionRelation10177 namedCorrectionRelation10178

private theorem namedH1CorrectionActual :
    background.sphereAlgebra.product (1,2) (13,137) h1 correction = 0 := by
  have hc := comparison_product 4 21 9 116 (by decide)
    (sourceData.atom .e0) (sourceData.atom .delta_h_6_mul_g)
  change comparison 13 137 _ _ = background.sphereAlgebra.product (4,21) (9,116)
    (atom .e0) (atom .delta_h_6_mul_g) at hc
  have h := comparison_product 1 2 13 137 (by decide) (sourceData.atom .h1)
    (sourceData.product 4 21 9 116 (sourceData.atom .e0) (sourceData.atom .delta_h_6_mul_g))
  rw [comparison_h1,hc,namedSourceH1CorrectionZero,map_zero] at h
  exact h.symm

end NamedRelationVanishingConstruction

public theorem h5Square_b_zero : product (r := (10,134)) h5Square (atom .b) = 0 := by
  exact namedH5SquareBActual


section TNondivisibilityConstruction
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000




@[expose]
section
section FixedSourceComparison
open CategoryTheory KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
private def coefficientSourceT : sourceData.component 14 139 :=
  sourceData.product 1 2 13 137 (sourceData.atom .h1)
    (sourceData.product 1 16 12 121 (sourceData.atom .h4) (sourceData.atom .x_109_12))

private theorem coefficientSourceT_comparison :
    comparison 14 139 (by decide) coefficientSourceT = T := by
  have inner := comparison_product 1 16 12 121 (by decide)
    (sourceData.atom .h4) (sourceData.atom .x_109_12)
  have outer := comparison_product 1 2 13 137 (by decide) (sourceData.atom .h1)
    (sourceData.product 1 16 12 121 (sourceData.atom .h4) (sourceData.atom .x_109_12))
  change comparison 14 139 _ coefficientSourceT = _ at outer
  rw [inner] at outer
  rw [comparison_h1,comparison_h4] at outer
  exact outer

private theorem coefficientSourceT_val : coefficientSourceT.val =
    nativeProjection generators.count archiveSourceRelations
      (MvPolynomial.X ⟨1,by decide⟩ *
        (MvPolynomial.X ⟨7,by decide⟩ * MvPolynomial.X ⟨275,by decide⟩)) := by
  rw [map_mul,map_mul]
  rfl

private theorem coefficient_h0_pullback
    (a : background.classical.sphere.Page 2 (13,138))
    (ha : product (r := (14,139)) h0 a = T) :
    sourceData.product 1 1 13 138 (sourceData.atom .h0)
      ((comparison 13 138 (by decide)).symm a) = coefficientSourceT := by
  apply (comparison 14 139 (by decide)).injective
  have h := comparison_product 1 1 13 138 (by decide) (sourceData.atom .h0)
    ((comparison 13 138 (by decide)).symm a)
  rw [comparison_h0,LinearEquiv.apply_symm_apply] at h
  exact h.trans (ha.trans coefficientSourceT_comparison.symm)

private theorem coefficient_h2_pullback
    (a : background.classical.sphere.Page 2 (13,135))
    (ha : product (r := (14,139)) h2 a = T) :
    sourceData.product 1 4 13 135 (sourceData.atom .h2)
      ((comparison 13 135 (by decide)).symm a) = coefficientSourceT := by
  apply (comparison 14 139 (by decide)).injective
  have h := comparison_product 1 4 13 135 (by decide) (sourceData.atom .h2)
    ((comparison 13 135 (by decide)).symm a)
  rw [comparison_h2,LinearEquiv.apply_symm_apply] at h
  exact h.trans (ha.trans coefficientSourceT_comparison.symm)

end
end FixedSourceComparison

end

section FixedSourceComparison
open CategoryTheory KIP126.AdamsSynthetic.Completed MvPolynomial
open KIP126.Computation.RelationCertificate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
private abbrev coefficientN := 2914
private def coefficientRowGood (cs : List Char) : Prop :=
  KIP126.Computation.CachedStandard.coefficientRowGood cs
private theorem coefficient_source_X_not_target
    (cert : ∀ code∈archiveSourceRelations, coefficientRowGood code.toList)
    (i : Fin coefficientN) (hi : i.val=0 ∨ i.val=2)
    (a : nativeAlgebra coefficientN archiveSourceRelations) :
    (nativeProjection coefficientN archiveSourceRelations (MvPolynomial.X i))*a ≠
    (nativeProjection coefficientN archiveSourceRelations (MvPolynomial.X ⟨1,by decide⟩ *
      (MvPolynomial.X ⟨7,by decide⟩ * MvPolynomial.X ⟨275,by decide⟩))) := by
  apply arbitrary_product_nonzero
  exact KIP126.Computation.CachedStandard.coefficient_source_X_not_target cert i hi

private theorem coefficient_t_not_h0_multiple
    (cert : ∀ code∈archiveSourceRelations, coefficientRowGood code.toList) :
    ¬ ∃ a : background.classical.sphere.Page 2 (13,138), product (r:=(14,139)) h0 a=T := by
  rintro ⟨a,ha⟩
  have hp := coefficient_h0_pullback a ha
  have hv := congrArg Subtype.val hp
  rw [coefficientSourceT_val] at hv
  exact coefficient_source_X_not_target cert ⟨0,by decide⟩ (Or.inl rfl)
    ((comparison 13 138 (by decide)).symm a).val hv

private theorem coefficient_t_not_h2_multiple
    (cert : ∀ code∈archiveSourceRelations, coefficientRowGood code.toList) :
    ¬ ∃ a : background.classical.sphere.Page 2 (13,135), product (r:=(14,139)) h2 a=T := by
  rintro ⟨a,ha⟩
  have hp := coefficient_h2_pullback a ha
  have hv := congrArg Subtype.val hp
  rw [coefficientSourceT_val] at hv
  exact coefficient_source_X_not_target cert ⟨2,by decide⟩ (Or.inr rfl)
    ((comparison 13 135 (by decide)).symm a).val hv
end
end FixedSourceComparison

private theorem coefficientArchiveChecked :
    ∀ code∈archiveSourceRelations, coefficientRowGood code.toList := by
  exact KIP126.Computation.CachedStandard.coefficientArchiveChecked

end TNondivisibilityConstruction

public theorem t_not_h0_multiple : ¬ ∃ a : background.classical.sphere.Page 2 (13,138),
    product (r := (14,139)) h0 a = T := by
  exact coefficient_t_not_h0_multiple coefficientArchiveChecked

public theorem t_not_h2_multiple : ¬ ∃ a : background.classical.sphere.Page 2 (13,135),
    product (r := (14,139)) h2 a = T := by
  exact coefficient_t_not_h2_multiple coefficientArchiveChecked

public theorem x_h2_zero : product (r := (9,134)) X h2 = 0 := by
  exact namedXH2Actual

private theorem yNotH2Generator0 :
    KIP126.Computation.StandardArchive.archiveGenerator0.value sourceData sourceGenerator = sourceData.atom .h0 := by
  exact sourceAtom_agrees .h0
private theorem yNotH2Generator391 :
    KIP126.Computation.StandardArchive.archiveGenerator391.value sourceData sourceGenerator = sourceData.atom .x_125_9_2 := by
  exact sourceAtom_agrees .x_125_9_2

private theorem yNotH2SourceBinding
    (i : Fin (archive.basisCount 11 136)) (hi : i.val = 3) :
    (archive.basisMonomial 11 136 i).value sourceData sourceGenerator =
      sourceData.product 2 2 9 134
        (sourceData.product 1 1 1 1 (sourceData.atom .h0) (sourceData.atom .h0))
        (sourceData.atom .x_125_9_2) := by
  have hir : i = ⟨3, by decide⟩ := Fin.ext hi
  subst i
  change sourceData.product 1 1 10 135 (KIP126.Computation.StandardArchive.archiveGenerator0.value sourceData sourceGenerator)
    (sourceData.product 1 1 9 134 (KIP126.Computation.StandardArchive.archiveGenerator0.value sourceData sourceGenerator)
      (KIP126.Computation.StandardArchive.archiveGenerator391.value sourceData sourceGenerator)) = _
  rw [yNotH2Generator0,yNotH2Generator391]
  apply Subtype.ext
  change _ * (_ * _) = (_ * _) * _
  exact (mul_assoc _ _ _).symm

private theorem yNotH2ActualBinding :
    (coordinates 11 136 (by decide)).symm
      (Finsupp.single (⟨3, by decide⟩ : Fin (archive.basisCount 11 136)) 1) = Y := by
  have h := coordinates_basis 11 136 (by decide) ⟨3, by decide⟩
  rw [yNotH2SourceBinding _ rfl] at h
  have hsquare := comparison_product 1 1 1 1 (by decide)
    (sourceData.atom .h0) (sourceData.atom .h0)
  rw [comparison_h0] at hsquare
  have hm := comparison_product 2 2 9 134 (by decide)
    (sourceData.product 1 1 1 1 (sourceData.atom .h0) (sourceData.atom .h0))
    (sourceData.atom .x_125_9_2)
  rw [hsquare] at hm
  exact h.trans hm

private theorem yNotH2Nonzero : Y ≠ 0 := by
  intro h
  let e := coordinates 11 136 (by decide)
  let i : Fin (archive.basisCount 11 136) := ⟨3, by decide⟩
  have hb : e.symm (Finsupp.single i 1) = Y := yNotH2ActualBinding
  have hv : Finsupp.single i (1 : ZMod 2) = 0 :=
    (e.apply_symm_apply _).symm.trans ((congrArg e (hb.trans h)).trans e.map_zero)
  have hi := (congrArg (fun f => f i) hv).trans (show (0 : Fin (archive.basisCount 11 136) →₀ ZMod 2) i = 0 from rfl)
  have h10 : (1 : ZMod 2) = 0 := (show (Finsupp.single i (1 : ZMod 2)) i = 1 from Finsupp.single_eq_same).symm.trans hi
  exact one_ne_zero h10

public theorem y_not_h2_multiple : ¬ ∃ a : background.classical.sphere.Page 2 (10,132),
    product (r := (11,136)) h2 a = Y := by
  rintro ⟨a,ha⟩
  have hn : archive.basisCount 10 132 = 0 := rfl
  haveI : Subsingleton (Fin (archive.basisCount 10 132) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  have hz : a = 0 := (coordinates 10 132 (by decide)).injective (Subsingleton.elim _ _)
  rw [hz] at ha
  have hp : product (r := (11,136)) h2 (0 : background.classical.sphere.Page 2 (10,132)) = 0 := by
    change background.sphereAlgebra.product (1,4) (10,132) h2 0 = 0
    exact map_zero (background.sphereAlgebra.product (1,4) (10,132) h2)
  exact yNotH2Nonzero (ha.symm.trans hp)

public theorem h1_correction_zero : product (r := (14,139)) h1 correction = 0 := by
  exact namedH1CorrectionActual

public theorem e2_stem125_low : ∀ s : ℕ, s ≤ 4 →
    Subsingleton (background.classical.sphere.Page 2 (s,(s : ℤ)+125)) := by
  intro s hs
  have ht : s + 125 ≤ 261 := by omega
  have hn : archive.basisCount s (s + 125) = 0 := by
    interval_cases s <;> rfl
  haveI : Subsingleton (Fin (archive.basisCount s (s + 125)) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  have h := (coordinates s (s + 125) ht).injective.subsingleton
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

private theorem two_power_sum_eq_128 (i j : ℕ) (hij : i ≤ j)
    (hsum : (2 : ℕ)^i + 2^j = 128) : i = 6 ∧ j = 6 := by
  have upper : (2 : ℕ)^j ≤ 128 := le_trans (Nat.le_add_left _ _) (le_of_eq hsum)
  have hj : j ≤ 7 := by
    by_contra hn
    have h8 : 8 ≤ j := by omega
    have hp : (2 : ℕ)^8 ≤ 2^j := Nat.pow_le_pow_right (by decide) h8
    have h256 : 256 ≤ (2 : ℕ)^j := hp
    omega
  have hi : i ≤ 7 := hij.trans hj
  interval_cases i <;> interval_cases j <;> norm_num at *

/-- The actual sphere E₂ group in bidegree `(1,64)` has one nonzero
element, namely the designated standard `h₆`. -/
public theorem h6_exhaustive (x : background.classical.sphere.Page 2 (1,64)) :
    x = 0 ∨ x = h6 := by
  have hn : archive.basisCount 1 64 = 1 := rfl
  let e := coordinates 1 64 (by decide)
  let j : Fin (archive.basisCount 1 64) := ⟨0, by omega⟩
  have unique (i : Fin (archive.basisCount 1 64)) : i = j := by
    apply Fin.ext
    have hi := i.isLt
    dsimp [j]
    omega
  have oneCoordinate (f : Fin (archive.basisCount 1 64) →₀ ZMod 2) :
      f = 0 ∨ f = Finsupp.single j 1 := by
    have hlt := ZMod.val_lt (f j)
    have h : (f j).val = 0 ∨ (f j).val = 1 := by omega
    rcases h with h | h
    · left
      apply Finsupp.ext
      intro i
      have hi : i = j := unique i
      subst i
      apply ZMod.val_injective 2
      simpa using h
    · right
      apply Finsupp.ext
      intro i
      have hi : i = j := unique i
      subst i
      rw [Finsupp.single_eq_same]
      apply ZMod.val_injective 2
      simpa only [ZMod.val_one] using h
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  have hex : e x ≠ 0 := fun hz => hx (e.injective (hz.trans (map_zero e).symm))
  have heh : e h6 ≠ 0 := by
    intro hz
    exact background.standardClasses.hi_ne_zero 6 (by decide)
      (e.injective (hz.trans (map_zero e).symm))
  rcases oneCoordinate (e x) with h | h
  · exact (hex h).elim
  rcases oneCoordinate (e h6) with h' | h'
  · exact (heh h').elim
  exact e.injective (h.trans h'.symm)

public theorem square_exhaustive (x : background.classical.sphere.Page 2 (2,128)) :
    x = 0 ∨ x = h6Square := by
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  obtain ⟨i,j,hiBound,hjBound,hij,hdegree,hx⟩ :=
    KIP126.Literature.Standard.two_line_exhaustive 128 x hx (by decide)
  have hsum : (2 : ℕ)^i + 2^j = 128 := by
    have ht := congrArg Prod.snd hdegree
    simp only [hiDegree, Prod.snd_add] at ht
    exact_mod_cast ht
  obtain ⟨rfl,rfl⟩ := two_power_sum_eq_128 i j hij hsum
  exact hx.trans (background.standardClasses.standardHiSquare_eq_product 6 hdegree).symm

public theorem square_nonzero : h6Square ≠ 0 := by
  let e := coordinates 2 128 (by decide)
  have hn : archive.basisCount 2 128 = 1 := rfl
  let i : Fin (archive.basisCount 2 128) := ⟨0, by rw [hn]; decide⟩
  let v : Fin (archive.basisCount 2 128) →₀ ZMod 2 := Finsupp.single i 1
  have hv : v ≠ 0 := by
    intro h
    have hi := congrArg (fun f => f i) h
    have h10 : (1 : ZMod 2) = 0 := by simpa only [v, Finsupp.single_eq_same,
      Finsupp.zero_apply] using hi
    exact one_ne_zero h10
  let x := e.symm v
  have hx : x ≠ 0 := by
    intro h
    apply hv
    have he := congrArg e h
    simpa only [x, LinearEquiv.apply_symm_apply, map_zero] using he
  rcases square_exhaustive x with h | h
  · exact (hx h).elim
  · intro hz
    exact hx (h.trans hz)

/- The sphere E₂ group in bidegree (8,130) is one dimensional with basis X,
giving the uniqueness premise for the ν-operation comparison. -/
section CofiberCoefficientConstruction
open CategoryTheory.Limits KIP126.AdamsSynthetic
open KIP126.Literature.Standard KIP126.Literature.Standard.E2Exactness
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
private def cofiberCoefficientSource :=
  sourceData.product 1 2 7 128 (sourceData.atom .h1) (sourceData.atom .x_121_7)
private theorem cofiberCoefficientComparison :
    comparison 8 130 (by decide) cofiberCoefficientSource = X := by
  have h := comparison_product 1 2 7 128 (by decide)
    (sourceData.atom .h1) (sourceData.atom .x_121_7)
  change comparison 8 130 _ _ = background.sphereAlgebra.product (1,2) (7,128)
    (comparison 1 2 _ (sourceData.atom .h1)) (atom .x_121_7) at h
  rw [comparison_h1] at h
  exact h
private theorem cofiberCoefficientBasis :
    (coordinates 8 130 (by decide)).symm
      (Finsupp.single (⟨0,by decide⟩ : Fin (archive.basisCount 8 130)) 1) = X := by
  have h := coordinates_basis 8 130 (by decide) ⟨0,by decide⟩
  have hb : (archive.basisMonomial 8 130 ⟨0,by decide⟩).value sourceData sourceGenerator =
      cofiberCoefficientSource := by
    change sourceData.product 1 2 7 128
      (KIP126.Computation.StandardArchive.archiveGenerator1.value sourceData sourceGenerator)
      (KIP126.Computation.StandardArchive.archiveGenerator323.value sourceData sourceGenerator) = _
    have h1 : KIP126.Computation.StandardArchive.archiveGenerator1.value sourceData sourceGenerator =
        sourceData.atom .h1 := sourceAtom_agrees .h1
    have h323 : KIP126.Computation.StandardArchive.archiveGenerator323.value sourceData sourceGenerator =
        sourceData.atom .x_121_7 := sourceAtom_agrees .x_121_7
    rw [h1,h323]
    rfl
  rw [hb] at h
  exact h.trans cofiberCoefficientComparison

private theorem cofiberCoefficientExhaustive (x : background.classical.sphere.Page 2 (8,130)) :
    x = 0 ∨ x = X := by
  let e := coordinates 8 130 (by decide)
  let i : Fin (archive.basisCount 8 130) := ⟨0,by decide⟩
  have unique (j : Fin (archive.basisCount 8 130)) : j = i := by
    apply Fin.ext
    have hj := j.isLt
    change j.val < 1 at hj
    dsimp [i]
    omega
  have hlt := ZMod.val_lt (e x i)
  have hv : (e x i).val = 0 ∨ (e x i).val = 1 := by omega
  rcases hv with hv | hv
  · left
    apply e.injective
    rw [map_zero]
    apply Finsupp.ext
    intro j
    rw [unique j]
    apply ZMod.val_injective 2
    exact hv
  · right
    have hx : e x = Finsupp.single i 1 := by
      apply Finsupp.ext
      intro j
      rw [unique j,Finsupp.single_eq_same]
      apply ZMod.val_injective 2
      exact hv
    have he := congrArg e.symm hx
    exact (e.symm_apply_apply x).symm.trans (he.trans cofiberCoefficientBasis)

private theorem cofiberH2CoefficientZero :
    background.sphereAlgebra.product (1,4) (8,130) h2 X = 0 := by
  have h := comparison_product 1 4 8 130 (by decide)
    (sourceData.atom .h2) cofiberCoefficientSource
  rw [comparison_h2,cofiberCoefficientComparison] at h
  have hcomm : sourceData.product 1 4 8 130 (sourceData.atom .h2) cofiberCoefficientSource =
      sourceData.product 8 130 1 4 cofiberCoefficientSource (sourceData.atom .h2) := by
    apply Subtype.ext
    exact mul_comm _ _
  rw [hcomm] at h
  have h' := comparison_product 8 130 1 4 (by decide)
    cofiberCoefficientSource (sourceData.atom .h2)
  rw [cofiberCoefficientComparison,comparison_h2] at h'
  exact h.symm.trans (h'.trans x_h2_zero)
private theorem cofiberNuSphereActionZero
    (z : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :
    sphereAction (KIP126.Literature.normalizedNu background nuCofiber_nu_exponent) z = 0 := by
  let E := KIP126.Literature.sphereFirstQuotient background 8 130
  apply (KIP126.Literature.sphereFirstQuotient background 9 134).injective
  rw [map_zero]
  have H := first_quotient_action 1 4 8 130
    (KIP126.Literature.normalizedNu background nuCofiber_nu_exponent) z
  change KIP126.Literature.sphereFirstQuotient background 9 134
      (sphereAction (KIP126.Literature.normalizedNu background nuCofiber_nu_exponent) z) =
    background.sphereAlgebra.product (1,4) (8,130)
      (KIP126.Literature.sphereFirstQuotient background 1 4
        (quotientClass 1 (KIP126.Literature.normalizedNu background nuCofiber_nu_exponent)))
      (E z) at H
  rw [nuCofiber_normalized_label] at H
  rw [H]
  rcases cofiberCoefficientExhaustive (E z) with hz | hz
  · rw [hz]
    exact map_zero _
  · rw [hz]
    exact cofiberH2CoefficientZero

private theorem cofiberNuSourceUnique
    (u v : BiHom 122 130 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))
    (hu : u ≠ 0) (hv : v ≠ 0) : u = v := by
  let E := KIP126.Literature.sphereFirstQuotient background 8 130
  have hun : E u ≠ 0 := fun h => hu (E.injective (h.trans E.map_zero.symm))
  have hvn : E v ≠ 0 := fun h => hv (E.injective (h.trans E.map_zero.symm))
  rcases cofiberCoefficientExhaustive (E u) with h | h
  · exact (hun h).elim
  rcases cofiberCoefficientExhaustive (E v) with h' | h'
  · exact (hvn h').elim
  exact E.injective (h.trans h'.symm)

private theorem cofiberNuConnectingZero
    (a3 : (background.classical.obj (Sphere 3)).Page 2 (8,133)) :
    e2Connecting background.auxiliary.nuRouteTriangle nuCofiber_nu_exponent 8 133 a3 = 0 := by
  have hz := nu_quotient_operation_zero 122 130 cofiberNuSourceUnique cofiberNuSphereActionZero
    ((background.firstQuotient (.shift 3 .sphere) 1 8 133).symm a3)
  unfold e2Connecting
  change (background.firstQuotient .sphere 0 9 134)
    (homotopyRegrade _ _
      (((background.firstQuotient (.shift 3 .sphere) 1 8 133).symm a3) ≫
        XModLambdaN.map positiveNuNormalizedMap 1 ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1)) = 0
  rw [←Category.assoc,hz,zero_comp]
  simp only [homotopyRegrade,map_zero]
end
end CofiberCoefficientConstruction

public noncomputable abbrev nuCofiberSequence :=
  background.classical.obj (HasFunctorialCofiber.cofib background.auxiliary.nuMap)
public noncomputable def bottom (s t : ℤ) :
    background.classical.sphere.Page 2 (s,t) →ₗ[ℤ] nuCofiberSequence.Page 2 (s,t) :=
  (background.classical.pageMap (HasFunctorialCofiber.cofibι background.auxiliary.nuMap) 2 (s,t)).hom
private structure CofiberTopCellData where
  topCell : nuCofiberSequence.Page 2 (8,134)
  top_comparison :
    ∃ (a3 : (background.classical.obj (Sphere 3)).Page 2 (8,133))
      (a2 : (background.classical.obj (Sphere 2)).Page 2 (8,132))
      (a1 : (background.classical.obj (Sphere 1)).Page 2 (8,131)),
      (background.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
        (background.classical.pageMap (HasFunctorialCofiber.cofibδ background.auxiliary.nuMap) 2 (8,134) topCell) a3 ∧
      (background.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
        (background.classical.pageMap
          ((shiftFunctorAdd' Spectrum (2 : ℤ) 1 3 (by decide)).hom.app SphereSpectrum)
          2 (8,133) a3) a2 ∧
      (background.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
        (background.classical.pageMap
          ((shiftFunctorAdd' Spectrum (1 : ℤ) 1 2 (by decide)).hom.app SphereSpectrum)
          2 (8,132) a2) a1 ∧
      (background.classicalSuspension .sphere).DesuspendsClass 8 131 a1 X

private noncomputable def cofiberPageIso {A B : Spectrum} (e : A ≅ B) (s t : ℤ) :
    (background.classical.obj A).Page 2 (s,t) ≃
      (background.classical.obj B).Page 2 (s,t) where
  toFun := background.classical.pageMap e.hom 2 (s,t)
  invFun := background.classical.pageMap e.inv 2 (s,t)
  left_inv a := by
    have h : (background.classical.map e.hom).pageMap 2 (s,t) ≫
        (background.classical.map e.inv).pageMap 2 (s,t) = 𝟙 _ := by
      rw [← SpectralSequenceMorphism.pageMap_comp, ← background.classical.map_comp,
        e.hom_inv_id, background.classical.map_id, SpectralSequenceMorphism.pageMap_id]
    exact congrArg (fun f => f a) h
  right_inv a := by
    have h : (background.classical.map e.inv).pageMap 2 (s,t) ≫
        (background.classical.map e.hom).pageMap 2 (s,t) = 𝟙 _ := by
      rw [← SpectralSequenceMorphism.pageMap_comp, ← background.classical.map_comp,
        e.inv_hom_id, background.classical.map_id, SpectralSequenceMorphism.pageMap_id]
    exact congrArg (fun f => f a) h

/-- Existence of a top-cell lift by E₂ exactness. -/
private theorem cofiberTopCell_exists : Nonempty CofiberTopCellData := by
  obtain ⟨a1,h1⟩ := KIP126.Literature.Standard.E2Exactness.exists_suspendsClass .sphere 8 131 X
  obtain ⟨sa2,h2⟩ := KIP126.Literature.Standard.E2Exactness.exists_suspendsClass (.shift 1 .sphere) 8 132 a1
  let e2 := (shiftFunctorAdd' Spectrum (1 : ℤ) 1 2 (by decide)).app SphereSpectrum
  let a2 := (cofiberPageIso e2 8 132).symm sa2
  have ha2 : background.classical.pageMap e2.hom 2 (8,132) a2 = sa2 :=
    (cofiberPageIso e2 8 132).apply_symm_apply sa2
  obtain ⟨sa3,h3⟩ := KIP126.Literature.Standard.E2Exactness.exists_suspendsClass (.shift 2 .sphere) 8 133 a2
  let e3 := (shiftFunctorAdd' Spectrum (2 : ℤ) 1 3 (by decide)).app SphereSpectrum
  let a3 := (cofiberPageIso e3 8 133).symm sa3
  have ha3 : background.classical.pageMap e3.hom 2 (8,133) a3 = sa3 :=
    (cofiberPageIso e3 8 133).apply_symm_apply sa3
  obtain ⟨a,ha⟩ := (KIP126.Literature.Standard.E2Exactness.e2ExactAtX
    background.auxiliary.nuRouteTriangle
    KIP126.Literature.Standard.nuCofiber_nu_exponent
    KIP126.Literature.Standard.nuCofiber_bottom_exponent
    KIP126.Literature.Standard.nuCofiber_top_exponent 8 133 a3).mp
      (cofiberNuConnectingZero a3)
  refine ⟨{ topCell := a, top_comparison := ⟨a3,a2,a1,ha,?_,?_,h1⟩ }⟩
  · change (background.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
      (background.classical.pageMap e3.hom 2 (8,133) a3) a2
    rw [ha3]
    exact h3
  · change (background.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
      (background.classical.pageMap e2.hom 2 (8,132) a2) a1
    rw [ha2]
    exact h2

private noncomputable def cofiberTopCellConstruction : CofiberTopCellData :=
  Classical.choice cofiberTopCell_exists

set_option backward.privateInPublic true in
public noncomputable def topCell : nuCofiberSequence.Page 2 (8,134) := by
  exact cofiberTopCellConstruction.topCell
/-- The top-cell lift maps to X under the connecting arrow and four sphere
desuspensions. -/
public theorem top_comparison :
  ∃ (a3 : (background.classical.obj (Sphere 3)).Page 2 (8,133))
    (a2 : (background.classical.obj (Sphere 2)).Page 2 (8,132))
    (a1 : (background.classical.obj (Sphere 1)).Page 2 (8,131)),
    (background.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
      (background.classical.pageMap (HasFunctorialCofiber.cofibδ background.auxiliary.nuMap) 2 (8,134) topCell) a3 ∧
    (background.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
      (background.classical.pageMap
        ((shiftFunctorAdd' Spectrum (2 : ℤ) 1 3 (by decide)).hom.app SphereSpectrum)
        2 (8,133) a3) a2 ∧
    (background.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
      (background.classical.pageMap
        ((shiftFunctorAdd' Spectrum (1 : ℤ) 1 2 (by decide)).hom.app SphereSpectrum)
        2 (8,132) a2) a1 ∧
    (background.classicalSuspension .sphere).DesuspendsClass 8 131 a1 X := by
  exact cofiberTopCellConstruction.top_comparison
public noncomputable def cofiberSource : nuCofiberSequence.Page 2 (8,134) :=
  topCell + bottom 8 134 (atom .x_126_8_2) + bottom 8 134 (atom .x_126_8)
/-- The computation labels coincide with the same fixed literature labels. -/
public theorem g_agrees : atom .g = KIP126.Literature.Standard.g := by
  let q := sourceCoordinates 4 24 (by decide)
  let i : Fin (archive.basisCount 4 24) := ⟨0, by decide⟩
  have hb : q.symm (Finsupp.single i 1) = sourceData.atom .g := by
    exact sourceBasis_values 4 24 (by decide) ⟨0, by decide⟩
  have hs : sourceData.atom .g ≠ 0 := by
    intro hz
    have hv : Finsupp.single i (1 : ZMod 2) = 0 :=
      (q.apply_symm_apply _).symm.trans ((congrArg q (hb.trans hz)).trans q.map_zero)
    have hi := (congrArg (fun f => f i) hv).trans
      (show (0 : Fin (archive.basisCount 4 24) →₀ ZMod 2) i = 0 from rfl)
    have h10 : (1 : ZMod 2) = 0 :=
      (show (Finsupp.single i (1 : ZMod 2)) i = 1 from Finsupp.single_eq_same).symm.trans hi
    exact one_ne_zero h10
  have ha : atom .g ≠ 0 := by
    intro hz
    exact hs ((comparison 4 24 (by decide)).injective
      (hz.trans (comparison 4 24 (by decide)).map_zero.symm))
  exact KIP126.Literature.Standard.g_unique (atom .g) ha
public theorem delta_agrees : atom .delta_h_1_mul_g = KIP126.Literature.Standard.deltaH1g := by
  let q := sourceCoordinates 9 54 (by decide)
  let i : Fin (archive.basisCount 9 54) := ⟨0, by decide⟩
  have hb : q.symm (Finsupp.single i 1) = sourceData.atom .delta_h_1_mul_g := by
    exact sourceBasis_values 9 54 (by decide) ⟨0, by decide⟩
  have hs : sourceData.atom .delta_h_1_mul_g ≠ 0 := by
    intro hz
    have hv : Finsupp.single i (1 : ZMod 2) = 0 :=
      (q.apply_symm_apply _).symm.trans ((congrArg q (hb.trans hz)).trans q.map_zero)
    have hi := (congrArg (fun f => f i) hv).trans
      (show (0 : Fin (archive.basisCount 9 54) →₀ ZMod 2) i = 0 from rfl)
    have h10 : (1 : ZMod 2) = 0 :=
      (show (Finsupp.single i (1 : ZMod 2)) i = 1 from Finsupp.single_eq_same).symm.trans hi
    exact one_ne_zero h10
  have ha : atom .delta_h_1_mul_g ≠ 0 := by
    intro hz
    exact hs ((comparison 9 54 (by decide)).injective
      (hz.trans (comparison 9 54 (by decide)).map_zero.symm))
  exact KIP126.Literature.Standard.deltaH1g_unique (atom .delta_h_1_mul_g) ha


end KIP126.Computation.Standard
