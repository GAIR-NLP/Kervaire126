module
import all KIP126.Literature.BocksteinOriginalSuccessor
import all KIP126.Literature.BocksteinComparisonInput
import all KIP126.Literature.BocksteinBoundaryInput
public import KIP126.AdamsSynthetic.Completed.Background
import KIP126.AdamsSynthetic.Completed.Filtration
import KIP126.AdamsSynthetic.Completed.Separation
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
public import KIP126.Literature.ModelResults
import all KIP126.Literature.ModelResults
import all KIP126.Literature.Classical
import all KIP126.Literature.ClassicalRange
import all KIP126.Literature.EInfinity
import all KIP126.Literature.Triangles
import all KIP126.Literature.May

public import KIP126.AdamsSynthetic.Completed.SpectrumScope
public import KIP126.Literature.Standard.ClassicalInputs
import all KIP126.Literature.Standard.ClassicalInputs
public import KIP126.Literature.Standard.AdamsComparison
import all KIP126.Literature.Standard.AdamsComparison
public import KIP126.Literature.Standard.NormalizedTriangles
import all KIP126.Literature.Standard.NormalizedTriangles
public import KIP126.Literature.Standard.FiniteLift
import all KIP126.Literature.Standard.FiniteLift
public import KIP126.Literature.Standard.RealizationLifts
import all KIP126.Literature.Standard.RealizationLifts
public import KIP126.Literature.Standard.BurklundXu
import all KIP126.Literature.Standard.BurklundXu
public import KIP126.Literature.Standard.Tensor
import all KIP126.Literature.Standard.Tensor

/-! Moss on the fixed literature background. -/

@[expose] section
set_option autoImplicit false
noncomputable section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)


public def closedTensor :
  ClosedSymmetricTensorTriangulated Spectrum := KIP126.AdamsSynthetic.Completed.closedBackground


public def finiteMappingObject :
  MappingObject (fun X : Spectrum => X = SphereSpectrum) → MappingObject (IsFiniteSpectrum (C := Spectrum)) := fun X => ⟨X.val, by rw [X.property]; exact IsFiniteSpectrum.sphere⟩


public noncomputable def mapping :
  MappingSpectrumSystem closedTensor background.classicalTower (fun X : Spectrum => X = SphereSpectrum) := {
    convergence := fun X Y hX hY =>
      KIP126.AdamsSynthetic.Completed.mappingConvergence X Y
        (by rw [hX]; exact IsFiniteSpectrum.sphere) (by rw [hY]; exact IsFiniteSpectrum.sphere) }


public def mappingComposition :
  MappingComposition mapping := {
    pairing := fun X Y Z => KIP126.AdamsSynthetic.Completed.mapping_pairing
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    parity := fun X Y Z => KIP126.AdamsSynthetic.Completed.mapping_parity
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    abutment_compatible := fun X Y Z => KIP126.AdamsSynthetic.Completed.mapping_abutment_compatible
      (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    page_associative := fun W X Y Z => KIP126.AdamsSynthetic.Completed.mapping_page_associative
      (finiteMappingObject W) (finiteMappingObject X) (finiteMappingObject Y) (finiteMappingObject Z)
    identity := fun X => KIP126.AdamsSynthetic.Completed.mapping_identity (finiteMappingObject X)
    identity_actual := fun X => KIP126.AdamsSynthetic.Completed.mapping_identity_actual (finiteMappingObject X)
    page_left_unital := fun X Y => KIP126.AdamsSynthetic.Completed.mapping_page_left_unital
      (finiteMappingObject X) (finiteMappingObject Y)
    page_right_unital := fun X Y => KIP126.AdamsSynthetic.Completed.mapping_page_right_unital
      (finiteMappingObject X) (finiteMappingObject Y) }


public theorem mappingSphereCompatibility :
  MappingSphereCompatibility mappingComposition background.sphereAlgebra rfl := ⟨KIP126.AdamsSynthetic.Completed.mapping_sphere_product, KIP126.AdamsSynthetic.Completed.mapping_sphere_unit⟩


set_option backward.isDefEq.respectTransparency false in
private def filtrationPieceCast {A : ℤ → ModuleCat.{0} ℤ} (F : Filtration A)
    {p q : ℤ × ℤ} (h : p = q) :
    FiltrationPiece F p.1 p.2 ⟶ FiltrationPiece F q.1 q.2 :=
  eqToHom (congrArg (fun k : ℤ × ℤ => FiltrationPiece F k.1 k.2) h)

set_option backward.isDefEq.respectTransparency false in
private theorem filtrationPieceCast_arrow {A : ℤ → ModuleCat.{0} ℤ} (F : Filtration A)
    {p q : ℤ × ℤ} (h : p = q) (f : FiltrationPiece F p.1 p.2) :
    (F.F q.1 q.2).arrow (filtrationPieceCast F h f) =
      (eqToHom (congrArg (fun k : ℤ × ℤ => A k.2) h)) ((F.F p.1 p.2).arrow f) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem associatedGraded_lift_of_transport {A : ℤ → ModuleCat.{0} ℤ} (F : Filtration A)
    {p q : ℤ × ℤ} (h : p = q) (x : F.associatedGraded q.1 q.2)
    (f : FiltrationPiece F p.1 p.2)
    (hx : F.transportGraded h.symm x = F.toAssociatedGraded p.1 p.2 f) :
    x = F.toAssociatedGraded q.1 q.2 (filtrationPieceCast F h f) := by
  cases h
  simpa only [Filtration.transportGraded_self, filtrationPieceCast, eqToHom_refl,
    ModuleCat.id_apply] using hx

set_option backward.isDefEq.respectTransparency false in
private theorem mappingHomotopyEquiv_cast (X Y : Spectrum) {m n : ℤ} (h : m = n)
    (x : HomotopyGroup m (mappingSpectrum closedTensor X Y)) :
    mappingHomotopyEquiv closedTensor n X Y
      ((eqToHom (congrArg (fun k => AbstractAdamsTower.homotopy
        (mappingSpectrum closedTensor X Y) k) h)) x) =
      eqToHom (congrArg (fun k => X⟦k⟧) h.symm) ≫
        mappingHomotopyEquiv closedTensor m X Y x := by
  cases h
  simp only [eqToHom_refl, ModuleCat.id_apply, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem mappingComposition_detection_compatible_impl : Moss.DetectionCompatible mapping mappingComposition := by
  intro X Y Z r hr i j a b α β hα hβ
  rcases hα with ⟨eα, ⟨zα, hza, hzeα⟩, fα, hfa, hgα⟩
  rcases hβ with ⟨eβ, ⟨zβ, hzb, hzeβ⟩, fβ, hfb, hgβ⟩
  subst eα
  subst eβ
  let P := mappingComposition.pairing X Y Z
  let z := P.cyclePairAtInfinity i j zα zβ
  refine ⟨_, ⟨z, ?_, rfl⟩, ?_⟩
  · have hp := P.finitePagePair_compatible r i j
      (by
        change (background.classical.obj (mappingSpectrum closedTensor X.val Y.val)).r₀ ≤ r
        rw [background.classical.firstPage]
        exact hr)
      (by
        change (background.classical.obj (mappingSpectrum closedTensor Y.val Z.val)).r₀ ≤ r
        rw [background.classical.firstPage]
        exact hr)
      (by
        change (background.classical.obj (mappingSpectrum closedTensor X.val Z.val)).r₀ ≤ r
        rw [background.classical.firstPage]
        exact hr) zα zβ
    change infinityToPage (mapping.hom X Y).underlying.E r i zα = a at hza
    change infinityToPage (mapping.hom Y Z).underlying.E r j zβ = b at hzb
    rw [hza, hzb] at hp
    exact hp.symm
  · let F := (mapping.hom X Z).underlying.F
    have h : (i.1+j.1, Moss.stem i+Moss.stem j) = ((i+j).1, Moss.stem (i+j)) :=
      P.reindex_compatible i j
    let f : FiltrationPiece F (i.1+j.1) (Moss.stem i+Moss.stem j) :=
      P.filteredAbutmentPair i.1 j.1 (Moss.stem i) (Moss.stem j) fα fβ
    refine ⟨filtrationPieceCast F h f, ?_, ?_⟩
    · refine (filtrationPieceCast_arrow F h f).trans ?_
      have hf : (F.F (i.1+j.1) (Moss.stem i+Moss.stem j)).arrow f =
          P.abutmentPair (Moss.stem i) (Moss.stem j) α β :=
        (P.filteredAbutmentPair_compatible i.1 j.1
          (Moss.stem i) (Moss.stem j) fα fβ).trans
          (congrArg₂ (fun u v => P.abutmentPair (Moss.stem i) (Moss.stem j) u v) hfa hfb)
      refine (congrArg (fun x =>
        (eqToHom (congrArg (fun k : ℤ × ℤ => (mapping.hom X Z).underlying.A k.2) h)) x) hf).trans ?_
      apply (mappingHomotopyEquiv closedTensor (Moss.stem (i+j)) X.val Z.val).injective
      have hc := mappingHomotopyEquiv_cast X.val Z.val (congrArg Prod.snd h)
        (P.abutmentPair (Moss.stem i) (Moss.stem j) α β)
      refine hc.trans ?_
      have hcompat := mappingComposition.abutment_compatible X Y Z
        (Moss.stem i) (Moss.stem j) α β
      refine (congrArg (fun c =>
        eqToHom (congrArg (fun k => X.val⟦k⟧) (congrArg Prod.snd h).symm) ≫ c) hcompat).trans ?_
      delta Moss.abutmentComposition Moss.shiftMap Moss.abutmentMap
      simp (config := { congrConsts := false }) only [Equiv.apply_symm_apply, Category.assoc]
    · apply associatedGraded_lift_of_transport F h _ f
      have hp := P.eInfty_compatible i j
        ((((mapping.hom X Y).underlying.E).ssData i).pageπ ⊤ zα)
        ((((mapping.hom Y Z).underlying.E).ssData j).pageπ ⊤ zβ)
      rw [← P.eInftyPair_induced] at hp
      change F.transportGraded h.symm
          (((mapping.convergence X.val Z.val X.property Z.property).identification (i+j)).hom
            (((Moss.sequence mapping X Z).ssData (i+j)).pageπ ⊤ z)) =
          P.associatedGradedPair i.1 j.1 (Moss.stem i) (Moss.stem j)
            (((mapping.convergence X.val Y.val X.property Y.property).identification i).hom
              (((Moss.sequence mapping X Y).ssData i).pageπ ⊤ zα))
            (((mapping.convergence Y.val Z.val Y.property Z.property).identification j).hom
              (((Moss.sequence mapping Y Z).ssData j).pageπ ⊤ zβ)) at hp
      rw [hgα, hgβ] at hp
      exact hp.trans (P.associatedGradedPair_induced i.1 j.1
        (Moss.stem i) (Moss.stem j) fα fβ)


/-- The same common infinite-cycle product and filtered abutment product
supply multiplicative detection; the abutment is the actual stable composite. -/
public theorem mappingComposition_detection_compatible :
  Moss.DetectionCompatible mapping mappingComposition := mappingComposition_detection_compatible_impl


public theorem moss_convergence :
  ∀ W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum),
    Moss.StatementAt mapping mappingComposition W X Y Z := by
  sorry


public theorem moss_at :
  ∀ W X Y Z : MappingObject (fun X : Spectrum => X = SphereSpectrum),
    Moss.StatementAt mapping mappingComposition W X Y Z := moss_convergence

end KIP126.Literature.Standard
end
