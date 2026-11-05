module

public import KIP126.AdamsSynthetic.Completed.Filtration
import all KIP126.AdamsSynthetic.Completed.Background
public import KIP126.AdamsSynthetic.MappingEnrichment
public import KIP126.AdamsSynthetic.Enrichment
import all KIP126.AdamsSynthetic.Enrichment
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.RingHom
public import KIP126.AdamsSynthetic.ESSShift
public import KIP126.AdamsSynthetic.Weight
public import KIP126.AdamsSynthetic.PageExtensions
public import KIP126.AdamsSynthetic.MappingOperations
import KIP126.SpectralSequence.FinitePageCalculus.Proofs

/-! Mapping composition on one fixed Adams background.
The construction data are shared by the page and E∞ operations. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.Kervaire.Route
noncomputable section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

public abbrev FiniteSpectrum := MappingObject (IsFiniteSpectrum (C := Spectrum))


private theorem pageSubsingletonOfAmbient
    (D : SSData (ModuleCat.{0} ℤ)) (r : WithTop ℕ) [Subsingleton D.V] :
    Subsingleton (D.page r) := by
  have hV : IsZero D.V := ModuleCat.isZero_of_subsingleton D.V
  have hZ : IsZero (Subobject.underlying.obj (D.Z r)) :=
    IsZero.of_mono (D.Z r).arrow hV
  letI : Epi (D.pageπ r) := coequalizer.π_epi
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_epi (D.pageπ r) hZ)

private theorem classicalPageNegativeGeneral (M : Spectrum) (r s t : ℤ)
    (hs : s < 0) : Subsingleton ((classical.obj M).Page r (s,t)) := by
  let T := classicalTower.tower M
  have hi (a b : ℕ) (hab : a ≤ b) (h : a = b) : IsIso (T.map hab) := by
    subst b
    rw [T.map_self]
    infer_instance
  let f := T.mapAt (show s ≤ s+1 by omega)
  haveI : IsIso f := hi s.toNat (s+1).toNat (by omega) (by omega)
  have hLayer : IsZero (T.layer s) :=
    Pretriangulated.Triangle.isZero₃_of_isIso₁
      (Pretriangulated.Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f))
      (HasFunctorialCofiber.cofib_distinguished f) (show IsIso f from inferInstance)
  letI : Subsingleton (T.FirstPage (s,t)) := ⟨fun a b => hLayer.eq_of_tgt a b⟩
  let D := (classical.obj M).ssData (s,t)
  letI : Subsingleton D.V :=
    (classicalTower.sequence M).ambient (s,t) |>.toLinearEquiv.injective.subsingleton
  exact pageSubsingletonOfAmbient D _

private theorem boundariesAtZeroStable (M : Spectrum) :
    ((classical.obj M).ssData (0,0)).B ⊤ = ((classical.obj M).ssData (0,0)).B 0 := by
  have h := boundaries_top_eq_of_d_eq_zero (classical.obj M) 2
    (le_of_eq (classical.firstPage M)) (0,0) ?_
  · simpa only [classical.firstPage, sub_self, Int.toNat_zero, Nat.cast_zero] using h
  intro r hr
  have hs : (((0 : ℤ), (0 : ℤ)) - (classical.obj M).diffDeg r).1 < 0 := by
    rw [classical.differentialDegree]
    dsimp
    omega
  letI := classicalPageNegativeGeneral M r
    (((0 : ℤ), (0 : ℤ)) - (classical.obj M).diffDeg r).1
    (((0 : ℤ), (0 : ℤ)) - (classical.obj M).diffDeg r).2 hs
  ext a
  have ha : a = 0 := Subsingleton.elim _ _
  simp only [ha, map_zero]

private theorem zeroInfinityEqDeterminesAllPages (M : Spectrum) (r : ℤ)
    (z z' : InfiniteCycles (classical.obj M) (0,0))
    (h : ((classical.obj M).ssData (0,0)).pageπ ⊤ z =
      ((classical.obj M).ssData (0,0)).pageπ ⊤ z') :
    infinityToPage (classical.obj M) r (0,0) z =
      infinityToPage (classical.obj M) r (0,0) z' := by
  let D := (classical.obj M).ssData (0,0)
  let n : WithTop ℕ := ↑(r-(classical.obj M).r₀).toNat
  have hB : D.B ⊤ = D.B n :=
    le_antisymm ((boundariesAtZeroStable M).le.trans (D.B_mono (show 0 ≤ n from zero_le)))
      (D.B_mono le_top)
  exact FinitePageCalculus.same_boundaries_projection_eq D n ⊤ le_top hB z z' h

set_option backward.privateInPublic true in
private def mappingIdentityWitness
    (X : MappingObject (IsFiniteSpectrum (C := Spectrum))) :
    { U : ConvergingSSUnit (mappingSystem.hom X X).underlying rfl //
      mappingHomotopyZeroEquiv closedBackground X.val X.val U.abutment = 𝟙 X.val } := by
  classical
  apply Classical.choice
  let M := mappingSpectrum closedBackground X.val X.val
  let T := classicalTower.tower M
  let c := mappingConvergence X.val X.val X.property X.property
  let a := (mappingHomotopyZeroEquiv closedBackground X.val X.val).symm (𝟙 X.val)
  have ha : a ∈ T.filtrationSubmodule 0 0 := by
    refine ⟨a ≫ T.zeroIso.inv, ?_⟩
    change (a ≫ T.zeroIso.inv) ≫ T.projection 0 = a
    have hproj : T.projection 0 = T.zeroIso.hom := by
      change T.map (Nat.zero_le 0) ≫ T.zeroIso.hom = T.zeroIso.hom
      rw [T.map_self, Category.id_comp]
    rw [hproj, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmem : a ∈ ModuleCat.subobjectModule _ (T.filtration.F 0 0) := by
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using ha
  change ∃ b, (T.filtration.F 0 0).arrow.hom b = a at hmem
  obtain ⟨b, hb⟩ := hmem
  let e := (c.identification (0,0)).inv (T.filtration.toAssociatedGraded 0 0 b)
  haveI : Epi (((classical.obj M).ssData (0,0)).pageπ ⊤) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    (((classical.obj M).ssData (0,0)).pageπ ⊤)).mp inferInstance e
  let U : ConvergingSSUnit (mappingSystem.hom X X).underlying rfl :=
    { cycle := z
      filtered := b
      compatible := by
        change T.filtration.transportGraded rfl
          ((c.identification (0,0)).hom (((classical.obj M).ssData (0,0)).pageπ ⊤ z)) =
          T.filtration.toAssociatedGraded 0 0 b
        rw [Filtration.transportGraded_self, ModuleCat.id_apply, hz]
        change ((c.identification (0,0)).inv ≫ (c.identification (0,0)).hom) _ = _
        rw [Iso.inv_hom_id]
        rfl }
  refine ⟨⟨U, ?_⟩⟩
  change mappingHomotopyZeroEquiv closedBackground X.val X.val
    ((T.filtration.F 0 0).arrow b) = 𝟙 X.val
  rw [hb]
  exact (mappingHomotopyZeroEquiv closedBackground X.val X.val).apply_symm_apply _

set_option backward.privateInPublic true in
/-- The fixed mapping identity, with one common infinite cycle and the actual identity abutment. -/
public def mapping_identity :
    ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      ConvergingSSUnit (mappingSystem.hom X X).underlying rfl :=
  fun X => (mappingIdentityWitness X).val

/-- The fixed mapping identity abuts to the actual identity morphism. -/
public theorem mapping_identity_actual :
    ∀ X : MappingObject (IsFiniteSpectrum (C := Spectrum)),
      mappingHomotopyZeroEquiv closedBackground X.val X.val
        (mapping_identity X).abutment = 𝟙 X.val :=
  fun X => (mappingIdentityWitness X).property

/-- The mapping pairing, its compatibility with the sphere product and its unit laws
for the mapping identity. -/
private def MappingCompositionData :=
  {composition : MappingComposition mappingSystem // ∀ (p q : ℤ × ℤ)
      (x : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 p)
      (y : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 q),
    (sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 (p + q)
      ((composition.pairing ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).ssPairing.pair 2 p q x y) =
      sphereAlgebra.product p q
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 p x)
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 q y)}

private def mappingCompositionDataConstruction : MappingCompositionData :=
  ⟨{ pairing := by sorry
     parity := by sorry
     abutment_compatible := by sorry
     page_associative := by sorry
     identity := mapping_identity
     identity_actual := mapping_identity_actual
     page_left_unital := by sorry
     page_right_unital := by sorry }, by sorry⟩

/-- The mapping composition retains the specified identity. -/
private def mappingCompositionConstruction : MappingComposition mappingSystem :=
  mappingCompositionDataConstruction.val

public def mapping_pairing : ∀ X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum)),
    ConvergingSSPairing (mappingSystem.hom X Y).underlying (mappingSystem.hom Y Z).underlying (mappingSystem.hom X Z).underlying := mappingCompositionConstruction.pairing

private theorem mapping_sphere_product_compat (p q : ℤ × ℤ)
    (x : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
      ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 p)
    (y : (mappingSystem.hom ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
      ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).underlying.E.Page 2 q) :
    (sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 (p + q)
      ((mapping_pairing ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩
        ⟨SphereSpectrum, IsFiniteSpectrum.sphere⟩).ssPairing.pair 2 p q x y) =
      sphereAlgebra.product p q
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 p x)
        ((sphereMappingAdamsIso closedBackground classical).hom.pageMap 2 q y) :=
  mappingCompositionDataConstruction.property p q x y

public theorem mapping_parity : ∀ X Y Z, (mapping_pairing X Y Z).ssPairing.parity = adamsStemParity := mappingCompositionConstruction.parity

public theorem mapping_abutment_compatible : ∀ (X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (a b : ℤ)
      (x : (mappingSystem.hom X Y).underlying.A a) (y : (mappingSystem.hom Y Z).underlying.A b),
    mappingHomotopyEquiv closedBackground (a + b) X.val Z.val ((mapping_pairing X Y Z).abutmentPair a b x y) =
      (shiftFunctorAdd Spectrum a b).hom.app X.val ≫
        (shiftFunctor Spectrum b).map (mappingHomotopyEquiv closedBackground a X.val Y.val x) ≫
        mappingHomotopyEquiv closedBackground b Y.val Z.val y := mappingCompositionConstruction.abutment_compatible

public theorem mapping_page_associative : ∀ (W X Y Z : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (i j k : ℤ × ℤ)
      (x : (mappingSystem.hom W X).underlying.E.Page r i)
      (y : (mappingSystem.hom X Y).underlying.E.Page r j)
      (z : (mappingSystem.hom Y Z).underlying.E.Page r k),
    HEq ((mapping_pairing W Y Z).ssPairing.pair r (i + j) k
      ((mapping_pairing W X Y).ssPairing.pair r i j x y) z)
      ((mapping_pairing W X Z).ssPairing.pair r i (j + k) x
        ((mapping_pairing X Y Z).ssPairing.pair r j k y z)) := mappingCompositionConstruction.page_associative

public theorem mapping_page_left_unital : ∀ (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (k : ℤ × ℤ)
      (x : (mappingSystem.hom X Y).underlying.E.Page r k),
    HEq ((mapping_pairing X X Y).ssPairing.pair r (0,0) k ((mapping_identity X).page r) x) x := mappingCompositionConstruction.page_left_unital

public theorem mapping_page_right_unital : ∀ (X Y : MappingObject (IsFiniteSpectrum (C := Spectrum))) (r : ℤ) (k : ℤ × ℤ)
      (x : (mappingSystem.hom X Y).underlying.E.Page r k),
    HEq ((mapping_pairing X Y Y).ssPairing.pair r k (0,0) x ((mapping_identity Y).page r)) x := mappingCompositionConstruction.page_right_unital

private theorem actualIdentityDeterminesPages
    (X : MappingObject (IsFiniteSpectrum (C := Spectrum)))
    (U V : ConvergingSSUnit (mappingSystem.hom X X).underlying rfl)
    (hU : mappingHomotopyZeroEquiv closedBackground X.val X.val U.abutment = 𝟙 X.val)
    (hV : mappingHomotopyZeroEquiv closedBackground X.val X.val V.abutment = 𝟙 X.val)
    (r : ℤ) : U.page r = V.page r := by
  let F := (mappingSystem.hom X X).underlying.F
  have hf : U.filtered = V.filtered := by
    apply (ModuleCat.mono_iff_injective (F.F 0 0).arrow).mp inferInstance
    apply (mappingHomotopyZeroEquiv closedBackground X.val X.val).injective
    exact hU.trans hV.symm
  have hu := U.compatible
  have hv := V.compatible
  simp only [Filtration.transportGraded_self] at hu hv
  have he : U.eInfty = V.eInfty := by
    apply ((mappingSystem.hom X X).underlying.conv.iso (0,0)).toLinearEquiv.injective
    exact hu.trans ((congrArg (F.toAssociatedGraded 0 0) hf).trans hv.symm)
  exact zeroInfinityEqDeterminesAllPages
    (mappingSpectrum closedBackground X.val X.val) r U.cycle V.cycle he


/-- Assemble the common mapping operations and their identity. -/


public def mappingComposition : MappingComposition mappingSystem where
  pairing := mapping_pairing
  parity := mapping_parity
  abutment_compatible := mapping_abutment_compatible
  page_associative := mapping_page_associative
  identity := mapping_identity
  identity_actual := mapping_identity_actual
  page_left_unital := mapping_page_left_unital
  page_right_unital := mapping_page_right_unital

end
end KIP126.AdamsSynthetic.Completed
