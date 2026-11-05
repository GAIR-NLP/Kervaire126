module
import all KIP126.Literature.E2Exactness.Ordinary.ActualE2Naturality
import all KIP126.Literature.E2Exactness.Ordinary.ExactTransport

@[expose] section
namespace KIP126.Literature.Standard.ActualE2LES
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard.FixedTensorE2
open KIP126.Literature.Standard.TensorNormalization
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (U : Triangle Spectrum) (hU : U ∈ distTriang Spectrum)
  (hH : HomologyShortExact coefficients U) (t s : ℤ)

include hU hH

private theorem actualE2Boundary_square :
    tensorCochainBoundary baseTensorTower t U hU hH s ≫
      (actualE2ObjectIso U.obj₁ t (s+1)).hom =
    (actualE2ObjectIso U.obj₃ t s).hom ≫ actualE2Boundary U hU hH t s := by
  simp only [actualE2Boundary, Iso.hom_inv_id_assoc]

private theorem actualE2_range_eq_ker_middle :
    LinearMap.range ((classical.map U.mor₁).toSSDataMorphism.pageMap (s,t) 0).hom =
      LinearMap.ker ((classical.map U.mor₂).toSSDataMorphism.pageMap (s,t) 0).hom :=
  range_eq_ker_of_iso _ _ _ _
    (actualE2ObjectIso U.obj₁ t s) (actualE2ObjectIso U.obj₂ t s)
    (actualE2ObjectIso U.obj₃ t s)
    (actualE2ObjectIso_natural U.mor₁ t s) (actualE2ObjectIso_natural U.mor₂ t s)
    (tensorCochain_range_eq_ker_middle baseTensorTower t U hU hH s)

private theorem actualE2_range_eq_ker_before_boundary :
    LinearMap.range ((classical.map U.mor₂).toSSDataMorphism.pageMap (s,t) 0).hom =
      LinearMap.ker (actualE2Boundary U hU hH t s).hom :=
  range_eq_ker_of_iso _ _ _ _
    (actualE2ObjectIso U.obj₂ t s) (actualE2ObjectIso U.obj₃ t s)
    (actualE2ObjectIso U.obj₁ t (s+1))
    (actualE2ObjectIso_natural U.mor₂ t s) (actualE2Boundary_square U hU hH t s)
    (tensorCochain_range_eq_ker_before_boundary baseTensorTower t U hU hH s)

private theorem actualE2_range_eq_ker_after_boundary :
    LinearMap.range (actualE2Boundary U hU hH t s).hom =
      LinearMap.ker ((classical.map U.mor₁).toSSDataMorphism.pageMap (s+1,t) 0).hom :=
  range_eq_ker_of_iso _ _ _ _
    (actualE2ObjectIso U.obj₃ t s) (actualE2ObjectIso U.obj₁ t (s+1))
    (actualE2ObjectIso U.obj₂ t (s+1))
    (actualE2Boundary_square U hU hH t s) (actualE2ObjectIso_natural U.mor₁ t (s+1))
    (tensorCochain_range_eq_ker_after_boundary baseTensorTower t U hU hH s)

private theorem actualE2_longExactSequence :
    (∀ y : ((classical.obj U.obj₂).ssData (s,t)).page 0,
      (classical.map U.mor₂).toSSDataMorphism.pageMap (s,t) 0 y = 0 ↔
        ∃ x, (classical.map U.mor₁).toSSDataMorphism.pageMap (s,t) 0 x = y) ∧
    (∀ z : ((classical.obj U.obj₃).ssData (s,t)).page 0,
      actualE2Boundary U hU hH t s z = 0 ↔
        ∃ y, (classical.map U.mor₂).toSSDataMorphism.pageMap (s,t) 0 y = z) ∧
    (∀ x : ((classical.obj U.obj₁).ssData (s+1,t)).page 0,
      (classical.map U.mor₁).toSSDataMorphism.pageMap (s+1,t) 0 x = 0 ↔
        ∃ z, actualE2Boundary U hU hH t s z = x) := by
  constructor
  · intro y
    change y ∈ LinearMap.ker _ ↔ y ∈ LinearMap.range _
    rw [actualE2_range_eq_ker_middle U hU hH t s]
  constructor
  · intro z
    change z ∈ LinearMap.ker _ ↔ z ∈ LinearMap.range _
    rw [actualE2_range_eq_ker_before_boundary U hU hH t s]
  · intro x
    change x ∈ LinearMap.ker _ ↔ x ∈ LinearMap.range _
    rw [actualE2_range_eq_ker_after_boundary U hU hH t s]

end
end KIP126.Literature.Standard.ActualE2LES
end
