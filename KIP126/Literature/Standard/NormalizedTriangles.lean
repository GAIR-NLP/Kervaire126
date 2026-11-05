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

/-! NormalizedTriangles on the fixed literature background. -/

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

/-- External input: Proposition 3.20 on the same selected normalized arrows
and weight shifts, with its original exponent-sum hypothesis. -/
public theorem normalized_triangle_distinguished
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1) :
    KIP126.Literature.NormalizedTriangleCompatible background T he := by
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- A choice of cofiber comparison derived from Proposition 3.20. -/
public def normalized_cofiber
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1) :
    NormalizedCofiberComparison background T he := by
  let F := (background.normalizedMap T.X T.Y T.f).map
  let Q := Triangle.mk F (HasFunctorialCofiber.cofibι F) (HasFunctorialCofiber.cofibδ F)
  let V := KIP126.Literature.normalizedTriangle background T he
  let e : Q ≅ V := isoTriangleOfIso₁₂ Q V
    (HasFunctorialCofiber.cofib_distinguished F) (normalized_triangle_distinguished T he)
    (Iso.refl _) (Iso.refl _)
    (by simp [Q, V, F, KIP126.Literature.normalizedTriangle, Triangle.mk])
  refine { cofiber := Triangle.π₃.mapIso e, inclusion := ?_, boundary := ?_ }
  · have h := e.hom.comm₂
    simpa [e, Q, V, F, Triangle.mk, Category.id_comp] using h
  · change e.inv.hom₃ ≫ Q.mor₃ = V.mor₃
    rw [← e.inv.comm₃]
    have h₁ : e.inv.hom₁ = 𝟙 Q.obj₁ := by
      simp [e, Q, V, KIP126.Literature.normalizedTriangle, Triangle.mk]
    rw [h₁]
    dsimp only [Q, V, KIP126.Literature.normalizedTriangle, Triangle.mk]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

public def normalizedCofiberTriangle (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1) :=
  NormalizedCofiberComparison.triangle background (normalized_cofiber T he)

public abbrev normalizedCofiberTriangle_distinguished (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1) :=
  NormalizedCofiberComparison.distinguished background (normalized_cofiber T he)



public theorem nuCofiber_nu_exponent :
  normalizedExponent background.classicalTower background.auxiliary.nuMap = 1 := by
  classical
  obtain ⟨_, _, b, hb, _⟩ := nu_detection
  have hmem : background.auxiliary.nuMap ∈ ModuleCat.subobjectModule _
      ((background.classicalTower.tower SphereSpectrum).filtration.F 1 3) := by
    change ∃ b, ((background.classicalTower.tower SphereSpectrum).filtration.F 1 3).arrow.hom b = _
    exact ⟨b, hb⟩
  simp only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] at hmem
  obtain ⟨lift, hlift⟩ := hmem
  have hF : MapFiltrationAtLeast background.classicalTower background.auxiliary.nuMap 1 :=
    ⟨lift, hlift⟩
  change (if MapFiltrationAtLeast background.classicalTower background.auxiliary.nuMap 1 then 1 else 0) = 1
  exact if_pos hF

section
set_option backward.isDefEq.respectTransparency false

/- The fixed factorization-filtration theorem gives the required vanishing
on represented HF₂ homology. -/

private theorem nuFactorizationZeroOnHomology {X Y : Spectrum} {n : ℕ}
    {f : X ⟶ Y} (h : AdamsMapFactorization background.coefficients n f) :
    ZeroOnModTwoHomology background.coefficients f := by
  cases h with
  | single f hf => exact hf
  | prepend f g hf hg =>
      intro i x
      change x ≫ (background.coefficients.object ◁ (f ≫ g)) = 0
      rw [whiskerLeft_comp, ← Category.assoc]
      change modTwoHomologyMap background.coefficients f i x ≫ _ = 0
      rw [hf i x, zero_comp]

private theorem nuPositiveFiltrationZeroOnRightHomology {X Y : Spectrum}
    (f : X ⟶ Y) (hf : MapFiltrationAtLeast background.classicalTower f 1)
    (i : ℤ) (x : HomotopyGroup i (X ⊗ background.coefficients.object)) :
    x ≫ (f ▷ background.coefficients.object) = 0 := by
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.symmetric
  have hF : FactorizationFiltration background.coefficients f 1 :=
    (KIP126.AdamsSynthetic.Completed.factorization_filtration_iff f 1).mpr hf
  have hz := nuFactorizationZeroOnHomology (hF 1 (by decide) (by decide))
  apply (cancel_mono (β_ Y background.coefficients.object).hom).mp
  rw [Category.assoc, BraidedCategory.braiding_naturality_left,
    ← Category.assoc]
  change modTwoHomologyMap background.coefficients f i
    (x ≫ (β_ X background.coefficients.object).hom) = _
  rw [hz, zero_comp]

private theorem nuCoefficientUnitNonzero : background.coefficients.unit ≠ 0 := by
  intro h
  have h0 : background.coefficients.pi0Equiv.symm 1 = 0 := by
    dsimp only [ModTwoCoefficients.unit] at h
    have hh := congrArg
      (fun z => (shiftFunctorZero Spectrum ℤ).hom.app SphereSpectrum ≫ z) h
    simpa (config := { congrConsts := false }) only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      comp_zero] using hh
  have h10 : (1 : ZMod 2) = 0 := by
    simpa (config := { congrConsts := false }) only [AddEquiv.apply_symm_apply, map_zero] using
      congrArg background.coefficients.pi0Equiv h0
  exact one_ne_zero h10

private theorem nuCofiberCellExponents :
    normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g = 0 ∧
    normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h = 0 := by
  let B := KIP126.AdamsSynthetic.Completed.closedBackground
  let H := background.coefficients.object
  let F := tensorRight H
  letI := B.tensorShift H
  letI := B.tensorExact H
  let T := F.mapTriangle.obj
    (Triangle.mk background.auxiliary.nuMap
      (HasFunctorialCofiber.cofibι background.auxiliary.nuMap)
      (HasFunctorialCofiber.cofibδ background.auxiliary.nuMap))
  have hT : T ∈ distTriang Spectrum :=
    F.map_distinguished _ (HasFunctorialCofiber.cofib_distinguished _)
  have hF : MapFiltrationAtLeast background.classicalTower background.auxiliary.nuMap 1 := by
    classical
    have h := nuCofiber_nu_exponent
    change (if MapFiltrationAtLeast background.classicalTower background.auxiliary.nuMap 1
      then 1 else 0) = 1 at h
    by_contra hn
    simp (config := { congrConsts := false }) only [if_neg hn] at h
    contradiction
  have hf (i : ℤ) (x : HomotopyGroup i T.obj₁) : x ≫ T.mor₁ = 0 :=
    nuPositiveFiltrationZeroOnRightHomology _ hF i x
  have hbottom : ¬ MapFiltrationAtLeast background.classicalTower
      background.auxiliary.nuRouteTriangle.g 1 := by
    intro hg
    let a : HomotopyGroup 0 T.obj₂ :=
      background.coefficients.pi0Equiv.symm 1 ≫ (λ_ H).inv
    have ha : a ≠ 0 := by
      intro hz
      have h0 : background.coefficients.pi0Equiv.symm 1 = 0 := by
        have hh := congrArg (fun z => z ≫ (λ_ H).hom) hz
        simpa (config := { congrConsts := false }) only [a, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          zero_comp] using hh
      have h10 : (1 : ZMod 2) = 0 := by
        simpa (config := { congrConsts := false }) only [AddEquiv.apply_symm_apply, map_zero] using
          congrArg background.coefficients.pi0Equiv h0
      exact one_ne_zero h10
    have hag : a ≫ T.mor₂ = 0 :=
      nuPositiveFiltrationZeroOnRightHomology _ hg 0 a
    obtain ⟨b, hb⟩ := T.coyoneda_exact₂ hT a hag
    exact ha (hb.trans (hf 0 b))
  have htop : ¬ MapFiltrationAtLeast background.classicalTower
      background.auxiliary.nuRouteTriangle.h 1 := by
    intro hh
    let a₃ : HomotopyGroup 3 T.obj₁ :=
      (shiftFunctor Spectrum (3 : ℤ)).map background.coefficients.unit ≫
        (B.sphereTensorShift 3 H).inv
    have ha₃ : a₃ ≠ 0 := by
      intro hz
      have hu : (shiftFunctor Spectrum (3 : ℤ)).map background.coefficients.unit = 0 := by
        have h := congrArg (fun z => z ≫ (B.sphereTensorShift 3 H).hom) hz
        simpa (config := { congrConsts := false }) only [a₃, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          zero_comp] using h
      apply nuCoefficientUnitNonzero
      apply (shiftFunctor Spectrum (3 : ℤ)).map_injective
      rw [Functor.map_zero]
      exact hu
    let a₄ : HomotopyGroup 4 (T.obj₁⟦(1 : ℤ)⟧) :=
      (shiftFunctorAdd' Spectrum (3 : ℤ) 1 4 (by norm_num)).hom.app SphereSpectrum ≫
        (shiftFunctor Spectrum (1 : ℤ)).map a₃
    have ha₄ : a₄ ≠ 0 := by
      intro hz
      have h : (shiftFunctor Spectrum (1 : ℤ)).map a₃ = 0 := by
        apply (cancel_epi
          ((shiftFunctorAdd' Spectrum (3 : ℤ) 1 4 (by norm_num)).hom.app SphereSpectrum)).mp
        simpa (config := { congrConsts := false }) only [a₄, comp_zero] using hz
      apply ha₃
      apply (shiftFunctor Spectrum (1 : ℤ)).map_injective
      rw [Functor.map_zero]
      exact h
    have haf : a₄ ≫ (shiftFunctor Spectrum (1 : ℤ)).map T.mor₁ = 0 := by
      dsimp only [a₄]
      rw [Category.assoc, ← Functor.map_comp, hf 3 a₃,
        Functor.map_zero, comp_zero]
    obtain ⟨b, hb⟩ := T.coyoneda_exact₁ hT a₄ haf
    have hbh : b ≫ T.mor₃ = 0 := by
      change b ≫ ((background.auxiliary.nuRouteTriangle.h ▷ H) ≫ _) = 0
      rw [← Category.assoc]
      have hz := nuPositiveFiltrationZeroOnRightHomology
        background.auxiliary.nuRouteTriangle.h hh 4 b
      change b ≫ (background.auxiliary.nuRouteTriangle.h ▷ H) = 0 at hz
      rw [hz, zero_comp]
    exact ha₄ (hb.trans hbh)
  classical
  dsimp only [normalizedExponent]
  simp (config := { congrConsts := false }) only [if_neg hbottom, if_neg htop, and_self]

end



public theorem nuCofiber_bottom_exponent :
  normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g = 0 :=
  nuCofiberCellExponents.1

/-- The top cell has filtration exponent zero by the same actual Cν triangle. -/
public theorem nuCofiber_top_exponent :
  normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h = 0 :=
  nuCofiberCellExponents.2


public theorem nuCofiber_normalized_label :
  sphereFirstQuotient background 1 4 (quotientClass 1 (normalizedNu background nuCofiber_nu_exponent)) =
    background.standardClasses.standardHi 2 nu_detection._proof_2 := by
  sorry


public theorem triangle_lift :
  SyntheticTriangleLiftComparison background := by
  sorry

section NuCofiberConstructionScope
namespace NuCofiberConstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed (Spectrum SyntheticSpectrum background)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C := C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C := Syn)]
private theorem triangle_inverse_rotation_transport
    {A B E Z : Syn} (g : B ⟶ E) (h : E ⟶ Z) (d : Z ⟶ B⟦(1:ℤ)⟧)
    (hd : Triangle.mk g h d ∈ distTriang Syn) (j : Z ≅ A⟦(1:ℤ)⟧) :
    ∃ a : A ⟶ B,
      (shiftFunctor Syn (1:ℤ)).map a = -(j.inv ≫ d) ∧
      Triangle.mk a g (h ≫ j.hom) ∈ distTriang Syn := by
  let a := (shiftFunctor Syn (1:ℤ)).preimage (-(j.inv ≫ d))
  have ha : (shiftFunctor Syn (1:ℤ)).map a = -(j.inv ≫ d) :=
    (shiftFunctor Syn (1:ℤ)).map_preimage _
  refine ⟨a,ha,?_⟩
  apply (rotate_distinguished_triangle _).mpr
  apply isomorphic_distinguished _ hd
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) j.symm ?_ ?_ ?_
  · simp
  · simp
  · simp only [Triangle.rotate, Triangle.mk, Iso.refl_hom, CategoryTheory.Functor.map_id,
      Iso.symm_hom,Category.comp_id]
    exact congrArg Neg.neg ha |>.trans (neg_neg _)
private def nuPositiveLandingIso (N : NuFunctorData C Syn) (X : C) :
    N.functor.obj (X⟦(1:ℤ)⟧) ≅
      ((SyntheticCategory.biShift (0,1)).obj (N.functor.obj X))⟦(1:ℤ)⟧ :=
  N.suspensionIso X ≪≫
    (SyntheticCategory.biShift_comp (0,1) (1,0)).symm.app (N.functor.obj X) ≪≫
    (SyntheticCategory.biShift_compat (Syn:=Syn) 1).app _
private theorem boundaryLanding_natural_of_suspension_square
    (N : NuFunctorData C Syn) {X Y : C} (f : X ⟶ Y)
    (hs : N.functor.map ((shiftFunctor C (1:ℤ)).map f) ≫ (N.suspensionIso Y).hom =
      (N.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (N.functor.map f)) :
    (SyntheticCategory.biShift (0,-1)).map (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
      (N.boundaryLandingIso Y).hom =
      (N.boundaryLandingIso X).hom ≫ (shiftFunctor Syn (1:ℤ)).map (N.functor.map f) := by
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  have h₁ := congrArg F.map hs
  have h₂ := (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.naturality (N.functor.map f)
  have h₃ := (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.naturality (N.functor.map f)
  change F.map (N.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
      (F.map (N.suspensionIso Y).hom ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj Y)) =
    (F.map (N.suspensionIso X).hom ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj X) ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj X)) ≫ _
  simp only [Functor.map_comp] at h₁
  change F.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
      (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) =
      (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj X) ≫
        (SyntheticCategory.biShift (1,0)).map (N.functor.map f) at h₂
  change (SyntheticCategory.biShift (1,0)).map (N.functor.map f) ≫ _ = _ at h₃
  calc
    _ = F.map (N.suspensionIso X).hom ≫
        F.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj Y) := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app (N.functor.obj Y) ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app (N.functor.obj Y)) h₁
    _ = _ := by rw [reassoc_of% h₂, h₃]; simp only [Category.assoc]
private theorem lambda_negative_self (coh : BiShiftCoherence Syn) (A : Syn) :
    SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,-1)).obj A) =
      (SyntheticCategory.biShift (0,-1)).map (SyntheticCategory.lam.app A) := by
  have h := coh.lambda_comm (0,-1) A
  simpa only [biShiftAddIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.trans_inv, eqToIso.hom,eqToIso.inv,eqToHom_app,eqToHom_refl,
    Category.comp_id,Category.id_comp,Iso.hom_inv_id_app_assoc] using h
private theorem positive_lambda_shift_coherence
    (coh : BiShiftCoherence Syn) (A : Syn) :
    (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫
      (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) =
    (SyntheticCategory.biShift (0,-1)).map
        ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A) ≫
      SyntheticCategory.lam.app
        ((SyntheticCategory.biShift (1,0)).obj ((SyntheticCategory.biShift (0,1)).obj A)) := by
  have ha := coh.associativity (0,1) (1,0) (0,-1) (1,1) (1,-1) (1,0)
    rfl rfl rfl rfl A
  have hb := coh.associativity (0,1) (0,-1) (1,0) (0,0) (1,-1) (1,0)
    rfl rfl rfl rfl A
  have hu := coh.left_unit (1,0) A
  have hc := coh.lambda_comm (1,0) ((SyntheticCategory.biShift (0,1)).obj A)
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,
    eqToHom_refl,Category.comp_id] at ha hb hu
  simp only [biShiftAddIso,Iso.trans_hom,Iso.trans_inv,
    eqToIso.hom,eqToIso.inv,eqToHom_refl,Category.comp_id,Category.id_comp] at hc
  have hL : lambdaToPositivePow 1 A = SyntheticCategory.biShift_zero.inv.app A ≫
      (SyntheticCategory.biShift_comp (0,1) (0,-1)).inv.app A ≫
      SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) := by
    delta lambdaToPositivePow
    simp only [lambdaPow_one coh,eqToHom_refl,Category.id_comp]
    rfl
  have haux : (SyntheticCategory.biShift_comp (0,1) (1,-1)).hom.app A ≫
      (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) =
    (SyntheticCategory.biShift_comp (0,-1) (1,0)).inv.app
        ((SyntheticCategory.biShift (0,1)).obj A) ≫
      (SyntheticCategory.biShift (1,0)).map
        (SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A)) := by
    apply (cancel_epi ((SyntheticCategory.biShift_comp (0,-1) (1,0)).hom.app
      ((SyntheticCategory.biShift (0,1)).obj A))).1
    calc
      _ = ((SyntheticCategory.biShift (1,0)).map
          ((SyntheticCategory.biShift_comp (0,1) (0,-1)).hom.app A) ≫
          (SyntheticCategory.biShift_comp (0,0) (1,0)).hom.app A) ≫
            (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) := by
        simpa only [Category.assoc] using congrArg
          (fun z => z ≫ (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A)) hb.symm
      _ = _ := by
        have hu' : (SyntheticCategory.biShift_comp (0,0) (1,0)).hom.app A =
            (SyntheticCategory.biShift (1,0)).map (SyntheticCategory.biShift_zero.hom.app A) := hu
        rw [hu',hL]
        simp only [Functor.map_comp,Category.assoc]
        simp only [←Functor.map_comp_assoc,Iso.hom_inv_id_app,
          Iso.hom_inv_id_app_assoc,Category.id_comp,CategoryTheory.Functor.map_id]
  apply (cancel_epi ((SyntheticCategory.biShift (0,-1)).map
    ((SyntheticCategory.biShift_comp (0,1) (1,0)).hom.app A))).1
  calc
    _ = ((SyntheticCategory.biShift_comp (1,0) (0,-1)).hom.app
        ((SyntheticCategory.biShift (0,1)).obj A) ≫
        (SyntheticCategory.biShift_comp (0,1) (1,-1)).hom.app A) ≫
        (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A)) ha
    _ = SyntheticCategory.lam.app
        ((SyntheticCategory.biShift (1,0)).obj ((SyntheticCategory.biShift (0,1)).obj A)) := by
      rw [Category.assoc,haux]
      exact hc.symm
    _ = _ := by
      simp only [←Category.assoc,←Functor.map_comp,Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id,Category.id_comp]
private theorem positive_lambda_landing_square
    (coh : BiShiftCoherence Syn) (N : NuFunctorData C Syn) (X : C) :
    (N.boundaryLandingIso X).hom ≫
      (shiftFunctor Syn (1:ℤ)).map (lambdaToPositivePow 1 (N.functor.obj X)) =
    SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫
      (nuPositiveLandingIso N X).hom := by
  let A := N.functor.obj X
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  let P := (SyntheticCategory.biShift (Syn:=Syn) (0,1)).obj A
  have hp := positive_lambda_shift_coherence coh A
  have hc := (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.naturality
    (lambdaToPositivePow 1 A)
  have hn := SyntheticCategory.lam.naturality
    ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A)
  have hs := SyntheticCategory.lam.naturality (N.suspensionIso X).hom
  change (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) ≫
      (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P =
    (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app A ≫
      (shiftFunctor Syn (1:ℤ)).map (lambdaToPositivePow 1 A) at hc
  change F.map ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A) ≫
      SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,0)).obj P) =
    SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,1)).obj A) ≫
      (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A at hn
  change F.map (N.suspensionIso X).hom ≫
      SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,1)).obj A) =
    SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫ (N.suspensionIso X).hom at hs
  change (F.map (N.suspensionIso X).hom ≫
      (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫
      (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app A) ≫ _ =
    SyntheticCategory.lam.app (N.functor.obj (X⟦(1:ℤ)⟧)) ≫
      ((N.suspensionIso X).hom ≫
        (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P)
  calc
    _ = F.map (N.suspensionIso X).hom ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫
        (SyntheticCategory.biShift (1,0)).map (lambdaToPositivePow 1 A) ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P := by
      simpa only [Category.assoc] using congrArg (fun z =>
        F.map (N.suspensionIso X).hom ≫
        (SyntheticCategory.biShift_comp (1,1) (0,-1)).hom.app A ≫ z) hc.symm
    _ = F.map (N.suspensionIso X).hom ≫
        F.map ((SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A) ≫
        SyntheticCategory.lam.app ((SyntheticCategory.biShift (1,0)).obj P) ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P := by
      simpa only [Category.assoc] using congrArg (fun z => F.map (N.suspensionIso X).hom ≫ z ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P) hp
    _ = _ := by
      rw [reassoc_of% hn]
      simpa only [Category.assoc] using congrArg (fun z => z ≫
        (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app A ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app P) hs
private theorem inverse_rotated_lift_factorization
    (D : AdamsSyntheticBackground C Syn) (coh : BiShiftCoherence Syn)
    [(SyntheticCategory.biShift (Syn:=Syn) (0,-1)).Additive]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1:ℤ)⟧)
    (S : SyntheticTriangleLift D (Triangle.mk f g h).rotate)
    (hs : D.nu.functor.map ((shiftFunctor C (1:ℤ)).map f) ≫ (D.nu.suspensionIso Y).hom =
      (D.nu.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (D.nu.functor.map f)) :
    ∃ a : (SyntheticCategory.biShift (0,1)).obj (D.nu.functor.obj X) ⟶ D.nu.functor.obj Y,
      lambdaToPositivePow 1 (D.nu.functor.obj X) ≫ a = D.nu.functor.map f ∧
      Triangle.mk a (D.nu.functor.map g)
        (D.nu.functor.map h ≫ (nuPositiveLandingIso D.nu X).hom) ∈ distTriang Syn := by
  letI : D.nu.functor.Additive := D.nu.additive
  let F := SyntheticCategory.biShift (Syn:=Syn) (0,-1)
  have hd : Triangle.mk (D.nu.functor.map g) (D.nu.functor.map h)
      (S.connecting ≫ (D.nu.boundaryLandingIso Y).hom) ∈ distTriang Syn := S.distinguished
  obtain ⟨a,ha,htri⟩ := triangle_inverse_rotation_transport _ _ _ hd (nuPositiveLandingIso D.nu X)
  refine ⟨a,?_,htri⟩
  have hδ : S.connecting ≫ SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧)) =
      -(D.nu.functor.map ((shiftFunctor C (1:ℤ)).map f)) := by
    have hh := S.factorization
    change S.connecting ≫ SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧)) =
      D.nu.functor.map (-((shiftFunctor C (1:ℤ)).map f)) at hh
    simpa only [Functor.map_neg] using hh
  have hlam : F.map (S.connecting ≫
      SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧))) =
    SyntheticCategory.lam.app (D.nu.functor.obj (X⟦(1:ℤ)⟧)) ≫ S.connecting := by
    rw [Functor.map_comp,←lambda_negative_self coh]
    exact SyntheticCategory.lam.naturality S.connecting
  apply (shiftFunctor Syn (1:ℤ)).map_injective
  rw [Functor.map_comp]
  apply (cancel_epi (D.nu.boundaryLandingIso X).hom).1
  calc
    _ = SyntheticCategory.lam.app (D.nu.functor.obj (X⟦(1:ℤ)⟧)) ≫
        (nuPositiveLandingIso D.nu X).hom ≫ (shiftFunctor Syn (1:ℤ)).map a := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (shiftFunctor Syn (1:ℤ)).map a)
        (positive_lambda_landing_square coh D.nu X)
    _ = -(SyntheticCategory.lam.app (D.nu.functor.obj (X⟦(1:ℤ)⟧)) ≫
        S.connecting ≫ (D.nu.boundaryLandingIso Y).hom) := by
      rw [ha]
      simp only [Preadditive.comp_neg,Iso.hom_inv_id_assoc]
    _ = -(F.map (S.connecting ≫
        SyntheticCategory.lam.app (D.nu.functor.obj (Y⟦(1:ℤ)⟧))) ≫
        (D.nu.boundaryLandingIso Y).hom) := by
      rw [hlam]
      simp only [Category.assoc]
    _ = F.map (D.nu.functor.map ((shiftFunctor C (1:ℤ)).map f)) ≫
        (D.nu.boundaryLandingIso Y).hom := by
      rw [hδ,Functor.map_neg,Preadditive.neg_comp,neg_neg]
    _ = _ := boundaryLanding_natural_of_suspension_square D.nu f hs
private def oneSourceIso (n : ℕ) (hn : n=1) (A : Syn) :
    (SyntheticCategory.biShift (0,(n:ℤ))).obj A ≅ (SyntheticCategory.biShift (0,1)).obj A := by
  subst n
  exact Iso.refl _
private def negativeZeroIso (k : ℕ) (hk : k=0) (X : Syn) :
    (SyntheticCategory.biShift (0,-(k:ℤ))).obj X ≅ X := by
  subst k
  exact SyntheticCategory.biShift_zero.app X
private theorem negative_lift_zero_factorization {X Y : Syn} (k : ℕ) (hk : k=0)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj X ⟶ Y)
    (g : X ⟶ Y) (h : lambdaToPositivePow k X ≫ f = g) :
    negativeLift k f ≫ (negativeZeroIso k hk Y).hom = g := by
  subst k
  rw [←h]
  dsimp only [negativeLift,negativeZeroIso,lambdaToPositivePow,lambdaPow]
  simp only [eqToHom_refl,Category.id_comp,
    Iso.app_hom,Category.assoc]
  erw [SyntheticCategory.biShift_zero.hom.naturality]
  rfl
private def rawSourceConnecting (nf ng nh : ℕ)
    (he : (nf:ℤ)+(ng:ℤ)+(nh:ℤ)=1) {X X1 Z : Syn}
    (sx : X1 ≅ (SyntheticCategory.biShift (1,1)).obj X)
    (m : (SyntheticCategory.biShift (0,(nh:ℤ))).obj Z ⟶ X1) :
    (SyntheticCategory.biShift (0,-(ng:ℤ))).obj Z ⟶
      ((SyntheticCategory.biShift (0,(nf:ℤ))).obj X)⟦(1:ℤ)⟧ :=
  (SyntheticCategory.biShift (0,-(ng:ℤ))).map (negativeLift nh m) ≫
  (SyntheticCategory.biShift (0,-(ng:ℤ))).map
    ((SyntheticCategory.biShift (0,-(nh:ℤ))).map sx.hom) ≫
  (SyntheticCategory.biShift (0,-(ng:ℤ))).map
    ((SyntheticCategory.biShift_comp (1,1) (0,-(nh:ℤ))).hom.app X) ≫
  (SyntheticCategory.biShift_comp ((1,1)+(0,-(nh:ℤ))) (0,-(ng:ℤ))).hom.app X ≫
  eqToHom (congrArg (fun p => (SyntheticCategory.biShift p).obj X)
    (show ((1,1)+(0,-(nh:ℤ)))+(0,-(ng:ℤ))=(0,(nf:ℤ))+(1,0) from by
      ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> omega)) ≫
  (SyntheticCategory.biShift_comp (0,(nf:ℤ)) (1,0)).inv.app X ≫
  (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _
private theorem raw_connecting_zero_normalization
    (coh : BiShiftCoherence Syn) (nf ng nh : ℕ)
    (hf : nf=1) (hg : ng=0) (hh : nh=0) (he : (nf:ℤ)+(ng:ℤ)+(nh:ℤ)=1)
    {X X1 Z : Syn} (sx : X1 ≅ (SyntheticCategory.biShift (1,1)).obj X)
    (m : (SyntheticCategory.biShift (0,(nh:ℤ))).obj Z ⟶ X1)
    (h : Z ⟶ X1) (hfac : lambdaToPositivePow nh Z ≫ m=h) :
    rawSourceConnecting nf ng nh he sx m ≫
      (shiftFunctor Syn (1:ℤ)).map (oneSourceIso nf hf X).hom =
      (negativeZeroIso ng hg Z).hom ≫ h ≫ sx.hom ≫
        (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app X ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _ := by
  subst nf
  subst ng
  subst nh
  have hzero := negative_lift_zero_factorization 0 rfl m h hfac
  have hu := coh.right_unit (1,1) X
  simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
  change (SyntheticCategory.biShift_comp (1,1) (0,0)).hom.app X =
    SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X) at hu
  dsimp only [rawSourceConnecting,oneSourceIso,negativeZeroIso]
  simp only [eqToHom_refl,Iso.refl_hom,
    CategoryTheory.Functor.map_id,Category.comp_id,Category.id_comp]
  change (SyntheticCategory.biShift (0,0)).map (negativeLift 0 m) ≫
    (SyntheticCategory.biShift (0,0)).map ((SyntheticCategory.biShift (0,0)).map sx.hom) ≫
    (SyntheticCategory.biShift (0,0)).map ((SyntheticCategory.biShift_comp (1,1) (0,0)).hom.app X) ≫
    (SyntheticCategory.biShift_comp (1,1) (0,0)).hom.app X ≫ _ = _
  rw [hu]
  have hs := SyntheticCategory.biShift_zero.hom.naturality sx.hom
  have hz := SyntheticCategory.biShift_zero.hom.naturality (h ≫ sx.hom)
  have hcomp : negativeLift 0 m ≫ (SyntheticCategory.biShift (0,0)).map sx.hom ≫
      SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X) = h ≫ sx.hom := by
    rw [hs,←Category.assoc]
    exact congrArg (fun z=>z≫sx.hom) hzero
  calc
    _ = (SyntheticCategory.biShift (0,0)).map
        (negativeLift 0 m ≫ (SyntheticCategory.biShift (0,0)).map sx.hom ≫
          SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X)) ≫
        SyntheticCategory.biShift_zero.hom.app ((SyntheticCategory.biShift (1,1)).obj X) ≫
        (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app X ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _ := by
      simp only [Functor.map_comp,Category.assoc]
      rfl
    _ = _ := by
      rw [hcomp]
      simpa only [Functor.id_map,Iso.app_hom,Category.assoc] using congrArg (fun z=>z≫
        (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app X ≫
        (SyntheticCategory.biShift_compat (Syn:=Syn) 1).hom.app _) hz

private def lambdaAction (m n : ℤ) (X : SyntheticSpectrum) :
    BiHom m n X → BiHom m (n - 1) X := by
  intro f
  have heq : (m, n) + (0, -1) = (m, n - 1) := by
    ext <;> simp [sub_eq_add_neg]
  refine eqToHom ?_ ≫
    (SyntheticCategory.biShift_comp (m, n) (0, -1)).inv.app S_0_0 ≫
      SyntheticCategory.lam.app (Smn m n) ≫ f
  simp only [Smn]
  rw [heq]
private def LambdaInjectiveAt (m w : ℤ) (X : SyntheticSpectrum) : Prop :=
  Function.Injective (lambdaAction m w X)

private theorem source_connecting_zero_normalization

    (hf : normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f=1)
    (hg : normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g=0)
    (hh : normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h=0)
    (he : (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f:ℤ) +
      normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g +
      normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h=1) :
    normalizedConnecting background background.auxiliary.nuRouteTriangle he ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (oneSourceIso (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f) hf
          (background.nu.functor.obj (background.auxiliary.nuRouteTriangle.X.obj background.auxiliary))).hom =
    (negativeZeroIso (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g) hg
        (background.nu.functor.obj (background.auxiliary.nuRouteTriangle.Z.obj background.auxiliary))).hom ≫
      background.nu.functor.map background.auxiliary.nuRouteTriangle.h ≫
      (nuPositiveLandingIso background.nu (background.auxiliary.nuRouteTriangle.X.obj background.auxiliary)).hom := by
  exact raw_connecting_zero_normalization background.quotients.coherence _ _ _ hf hg hh he
    (background.nu.suspensionIso _) (background.normalizedMap .nuCofiber (.shift 1 (.shift 3 .sphere)) background.auxiliary.nuRouteTriangle.h).map _ (background.normalizedMap .nuCofiber (.shift 1 (.shift 3 .sphere)) background.auxiliary.nuRouteTriangle.h).factorization
private theorem lambda_injective_below_diagonal
    (m wt : ℤ) (hw : wt ≤ m + 1) :
    LambdaInjectiveAt m wt (S_0_0 : SyntheticSpectrum) := by
  letI := background.exactness.shiftAdditive (0,-1)
  letI := (SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-1)).faithful
  let U := (SyntheticCategory.biShift (0,-1)).obj (Smn (Syn := SyntheticSpectrum) m wt)
  let T := XModLambdaN.cofiberTriangle (S_0_0 : SyntheticSpectrum) 1
  let e₀ : U ≅ Smn (Syn := SyntheticSpectrum) m (wt-1) :=
    (SyntheticCategory.biShift_comp (m,wt) (0,-1)).app S_0_0 ≪≫
      eqToIso (by congr 1; simp [sub_eq_add_neg])
  let e₁ : U⟦(1 : ℤ)⟧ ≅ Smn (Syn := SyntheticSpectrum) (m+1) (wt-1) :=
    (shiftFunctor SyntheticSpectrum (1 : ℤ)).mapIso e₀ ≪≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp (m,wt-1) (1,0)).app S_0_0 ≪≫
      eqToIso (by congr 1; simp)
  have hQ : ∀ q : U⟦(1 : ℤ)⟧ ⟶ T.obj₃, q = 0 := by
    intro q
    haveI : Subsingleton (background.classical.sphere.Page 2 (wt-m-2,wt-1)) :=
      KIP126.AdamsSynthetic.Completed.classical_page_negative .sphere
        2 (wt-m-2) (wt-1) (by omega)
    have hz : ∀ a : BiHom (m+1) (wt-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1), a = 0 := by
      intro a
      have hp : wt - 1 - (wt-m-2) = m+1 := by omega
      have hsub : Subsingleton (BiHom (wt-1-(wt-m-2)) (wt-1)
          (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) :=
        (KIP126.Literature.sphereFirstQuotient background (wt-m-2) (wt-1)).injective.subsingleton
      rw [hp] at hsub
      exact @Subsingleton.elim _ hsub a 0
    apply (cancel_epi e₁.inv).mp
    simpa only [comp_zero] using hz (e₁.inv ≫ q)
  intro a b hab
  have hpre : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m wt) ≫ (a-b) = 0 := by
    rw [Preadditive.comp_sub]
    apply sub_eq_zero.mpr
    simpa only [lambdaAction, Category.assoc, cancel_epi] using hab
  have hf : (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ T.mor₁ = 0 := by
    change (SyntheticCategory.biShift (0,-1)).map (a-b) ≫ lambdaPow 1 S_0_0 = 0
    rw [lambdaPow_one background.quotients.coherence]
    rw [SyntheticCategory.lam.naturality]
    exact hpre
  have hfs : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧' ≫
      T.mor₁⟦(1 : ℤ)⟧' = 0 := by
    rw [← Functor.map_comp, hf, Functor.map_zero]
  obtain ⟨q,hq⟩ := T.coyoneda_exact₁
    (HasFunctorialCofiber.cofib_distinguished _) _ hfs
  have hz : ((SyntheticCategory.biShift (0,-1)).map (a-b))⟦(1 : ℤ)⟧' = 0 := by
    rw [hq, hQ q, zero_comp]
  have hz' : (SyntheticCategory.biShift (0,-1)).map (a-b) = 0 := by
    apply (shiftFunctor SyntheticSpectrum (1 : ℤ)).map_injective
    simpa only [Functor.map_zero] using hz
  apply sub_eq_zero.mp
  apply (SyntheticCategory.biShift (0,-1)).map_injective
  simpa only [Functor.map_zero] using hz'
private theorem nu_source_lambda_injective  :
    LambdaInjectiveAt 3 4 (S_0_0 : SyntheticSpectrum) :=
  lambda_injective_below_diagonal 3 4 (by omega)
private theorem positive_lift_unique_nu_degree
    {A B : SyntheticSpectrum}
    (eA : (SyntheticCategory.biShift (0,1)).obj A ≅ Smn (Syn := SyntheticSpectrum) 3 4)
    (eB : B ≅ (S_0_0 : SyntheticSpectrum))
    (f g : (SyntheticCategory.biShift (0,1)).obj A ⟶ B)
    (h : lambdaToPositivePow 1 A ≫ f = lambdaToPositivePow 1 A ≫ g) : f = g := by
  have hlam : SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) ≫ f =
      SyntheticCategory.lam.app ((SyntheticCategory.biShift (0,1)).obj A) ≫ g := by
    dsimp only [lambdaToPositivePow] at h
    rw [lambdaPow_one background.quotients.coherence] at h
    simp only [Category.assoc, cancel_epi] at h
    exact h
  have hlamTransport : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) 3 4) ≫
        (eA.inv ≫ f ≫ eB.hom) =
      SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) 3 4) ≫
        (eA.inv ≫ g ≫ eB.hom) := by
    have hn := SyntheticCategory.lam.naturality eA.inv
    dsimp only [Functor.id_map] at hn
    calc
      _ = (SyntheticCategory.biShift (0,-1)).map eA.inv ≫
          (SyntheticCategory.lam.app _ ≫ f) ≫ eB.hom := by simpa only [Category.assoc] using congrArg (fun z => z ≫ f ≫ eB.hom) hn.symm
      _ = (SyntheticCategory.biShift (0,-1)).map eA.inv ≫
          (SyntheticCategory.lam.app _ ≫ g) ≫ eB.hom := by rw [hlam]
      _ = _ := by simpa only [Category.assoc] using congrArg (fun z => z ≫ g ≫ eB.hom) hn
  have heq : eA.inv ≫ f ≫ eB.hom = eA.inv ≫ g ≫ eB.hom := by
    apply nu_source_lambda_injective
    dsimp only [lambdaAction]
    simpa only [Category.assoc] using congrArg
      (fun z => eqToHom (by rfl) ≫
        (SyntheticCategory.biShift_comp (3,4) (0,-1)).inv.app (S_0_0 : SyntheticSpectrum) ≫ z) hlamTransport
  exact (cancel_mono eB.hom).mp ((cancel_epi eA.inv).mp heq)
private theorem normalized_nu_lift_unique
    (he : normalizedExponent background.classicalTower background.auxiliary.nuMap = 1)
    (S T : NormalizedSyntheticMap background.classicalTower background.nu background.auxiliary.nuMap) : S.map = T.map := by
  let A := background.nu.functor.obj (Sphere (C := Spectrum) 3)
  let B := background.nu.functor.obj SphereSpectrum
  have h : lambdaToPositivePow (normalizedExponent background.classicalTower background.auxiliary.nuMap) A ≫ S.map =
      lambdaToPositivePow (normalizedExponent background.classicalTower background.auxiliary.nuMap) A ≫ T.map :=
    S.factorization.trans T.factorization.symm
  have aux (n : ℕ) (hn : n = 1)
      (f g : (SyntheticCategory.biShift (0,(n : ℤ))).obj A ⟶ B)
      (hh : lambdaToPositivePow n A ≫ f = lambdaToPositivePow n A ≫ g) : f = g := by
    subst n
    exact positive_lift_unique_nu_degree
      ((SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree background) ≪≫
        (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0)
      background.nu.unitIso f g hh
  exact aux _ he S.map T.map h
private theorem source_triangle_of_rotation_and_square

    (hf : normalizedExponent background.classicalTower background.auxiliary.nuMap=1)
    (hg : normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g=0)
    (hh : normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h=0)
    (R : SyntheticTriangleLift background
      (Triangle.mk background.auxiliary.nuMap background.auxiliary.nuRouteTriangle.g
        background.auxiliary.nuRouteTriangle.h).rotate)
    (hs : background.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map background.auxiliary.nuMap) ≫
        (background.nu.suspensionIso SphereSpectrum).hom =
      (background.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (background.nu.functor.map background.auxiliary.nuMap))
    (he : (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f:ℤ) +
      normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g +
      normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h=1) :
    KIP126.Literature.normalizedTriangle background background.auxiliary.nuRouteTriangle he ∈ distTriang SyntheticSpectrum := by
  letI := background.exactness.shiftAdditive (0,-1)
  obtain ⟨a,ha,htri⟩ := inverse_rotated_lift_factorization background background.quotients.coherence
    background.auxiliary.nuMap background.auxiliary.nuRouteTriangle.g background.auxiliary.nuRouteTriangle.h R hs
  let e := oneSourceIso (normalizedExponent background.classicalTower background.auxiliary.nuMap) hf
    (background.nu.functor.obj (Sphere (C:=Spectrum) 3))
  have haf : lambdaToPositivePow (normalizedExponent background.classicalTower background.auxiliary.nuMap)
      (background.nu.functor.obj (Sphere (C:=Spectrum) 3)) ≫ (e.hom ≫ a) = background.nu.functor.map background.auxiliary.nuMap := by
    have aux (n : ℕ) (hn : n=1) : lambdaToPositivePow n (background.nu.functor.obj (Sphere (C:=Spectrum) 3)) ≫
        (oneSourceIso n hn (background.nu.functor.obj (Sphere (C:=Spectrum) 3))).hom ≫ a =
        background.nu.functor.map background.auxiliary.nuMap := by
      subst n
      simpa only [oneSourceIso,Iso.refl_hom,Category.id_comp] using ha
    exact aux _ hf
  let U : NormalizedSyntheticMap background.classicalTower background.nu background.auxiliary.nuMap := ⟨e.hom ≫ a,haf⟩
  have hnu : (background.normalizedMap (.shift 3 .sphere) .sphere background.auxiliary.nuMap).map=e.hom ≫ a := normalized_nu_lift_unique hf (background.normalizedMap (.shift 3 .sphere) .sphere background.auxiliary.nuMap) U
  have hb := negative_lift_zero_factorization _ hg (background.normalizedMap .sphere .nuCofiber background.auxiliary.nuRouteTriangle.g).map _ (background.normalizedMap .sphere .nuCofiber background.auxiliary.nuRouteTriangle.g).factorization
  have ht := source_connecting_zero_normalization hf hg hh he
  apply isomorphic_distinguished _ htri
  refine Triangle.isoMk _ _ e (Iso.refl _)
    (negativeZeroIso (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g) hg
      (background.nu.functor.obj (background.auxiliary.nuRouteTriangle.Z.obj background.auxiliary))) ?_ ?_ ?_
  · change (background.normalizedMap (.shift 3 .sphere) .sphere background.auxiliary.nuMap).map ≫ 𝟙 _ = e.hom ≫ a
    simpa only [Category.comp_id] using hnu
  · change negativeLift (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g) (background.normalizedMap .sphere .nuCofiber background.auxiliary.nuRouteTriangle.g).map ≫ _ =
      𝟙 _ ≫ background.nu.functor.map background.auxiliary.nuRouteTriangle.g
    dsimp only [AuxiliaryData.nuRouteTriangle] at hb ⊢
    simpa only [Category.id_comp] using hb
  · exact ht

section TensorSupport
local instance tensorSymmetric : SymmetricCategory Spectrum :=
  KIP126.AdamsSynthetic.Completed.closedBackground.symmetric
local instance rightTensorShift (X : Spectrum) : (tensorRight X).CommShift ℤ :=
  KIP126.AdamsSynthetic.Completed.closedBackground.tensorShift X
local instance rightTensorExact (X : Spectrum) : (tensorRight X).IsTriangulated :=
  KIP126.AdamsSynthetic.Completed.closedBackground.tensorExact X
local instance leftTensorShift (X : Spectrum) : (tensorLeft X).CommShift ℤ :=
  Functor.CommShift.ofIso (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
local instance leftTensorShiftCompatibility (X : Spectrum) :
    NatTrans.CommShift (BraidedCategory.tensorLeftIsoTensorRight X).symm.hom ℤ :=
  Functor.CommShift.ofIso_compatibility (BraidedCategory.tensorLeftIsoTensorRight X).symm ℤ
local instance leftTensorExact (X : Spectrum) : (tensorLeft X).IsTriangulated :=
  Functor.isTriangulated_of_iso (BraidedCategory.tensorLeftIsoTensorRight X).symm

private theorem shifted_zero_homology {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ZeroOnModTwoHomology background.coefficients f) :
    ZeroOnModTwoHomology background.coefficients ((shiftFunctor Spectrum (1:ℤ)).map f) := by
  let F := tensorLeft background.coefficients.object
  let S := shiftFunctor Spectrum (1:ℤ)
  intro n a
  let e : Sphere (C:=Spectrum) n ≅ S.obj (Sphere (n-1)) :=
    (shiftFunctorAdd' Spectrum (n-1) 1 n (by omega)).app SphereSpectrum
  let b : HomotopyGroup (n-1) (F.obj X) :=
    S.preimage (e.inv ≫ a ≫ (F.commShiftIso (1:ℤ)).hom.app X)
  have hb : S.map b = e.inv ≫ a ≫ (F.commShiftIso (1:ℤ)).hom.app X :=
    S.map_preimage _
  have hz := congrArg S.map (hf (n-1) b)
  change S.map (b ≫ F.map f) = S.map 0 at hz
  rw [Functor.map_comp, hb, Functor.map_zero] at hz
  apply (cancel_mono ((F.commShiftIso (1:ℤ)).hom.app Y)).mp
  apply (cancel_epi e.inv).mp
  change e.inv ≫ ((a ≫ F.map (S.map f)) ≫ (F.commShiftIso (1:ℤ)).hom.app Y) = _
  have hn := (F.commShiftIso (1:ℤ)).hom.naturality f
  change F.map (S.map f) ≫ (F.commShiftIso (1:ℤ)).hom.app Y =
    (F.commShiftIso (1:ℤ)).hom.app X ≫ S.map (F.map f) at hn
  simp only [Category.assoc]
  rw [hn]
  simpa only [Category.assoc, comp_zero, zero_comp] using hz

private theorem positive_filtration_of_homology_zero {X Y : Spectrum}
    (f : X ⟶ Y) (hf : ZeroOnModTwoHomology background.coefficients f) :
    MapFiltrationAtLeast background.classicalTower f 1 := by
  apply (KIP126.AdamsSynthetic.Completed.factorization_filtration_iff f 1).mp
  intro n hn hn1
  have he : n=1 := by omega
  subst n
  exact AdamsMapFactorization.single f hf

private theorem rotated_cofiber_homology_short_exact {X Y : Spectrum}
    (f : X ⟶ Y) (hf : ZeroOnModTwoHomology background.coefficients f) :
    HomologyShortExact background.coefficients
      (Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f)).rotate := by
  let F := tensorLeft background.coefficients.object
  let T := F.mapTriangle.obj (Triangle.mk f (HasFunctorialCofiber.cofibι f)
    (HasFunctorialCofiber.cofibδ f))
  have hT : T ∈ distTriang Spectrum :=
    F.map_distinguished _ (HasFunctorialCofiber.cofib_distinguished f)
  intro n
  refine ⟨?_,?_,?_⟩
  · intro a b hab
    have hzero : (a-b) ≫ T.mor₂ = 0 := by
      rw [Preadditive.sub_comp]
      exact sub_eq_zero.mpr hab
    obtain ⟨c,hc⟩ := T.coyoneda_exact₂ hT (a-b) hzero
    apply sub_eq_zero.mp
    exact hc.trans (hf n c)
  · intro a
    change a ≫ (background.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) = 0 ↔
      ∃ b, b ≫ (background.coefficients.object ◁ HasFunctorialCofiber.cofibι f) = a
    constructor
    · intro ha
      have hz : a ≫ T.mor₃ = 0 := by
        change a ≫ ((background.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0
        rw [←Category.assoc,ha,zero_comp]
      obtain ⟨b,hb⟩ := T.coyoneda_exact₃ hT a hz
      exact ⟨b,hb.symm⟩
    · rintro ⟨b,rfl⟩
      have hh := comp_distTriang_mor_zero₂₃ T hT
      have hg : (background.coefficients.object ◁ HasFunctorialCofiber.cofibι f) ≫
          (background.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) = 0 := by
        apply (cancel_mono ((F.commShiftIso (1:ℤ)).hom.app X)).mp
        change (background.coefficients.object ◁ HasFunctorialCofiber.cofibι f) ≫
          ((background.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) ≫ _) = 0 at hh
        simpa only [T, Functor.mapTriangle_obj, Triangle.mk, Category.assoc, zero_comp] using hh
      rw [Category.assoc,hg,comp_zero]
  · intro a
    let e := (F.commShiftIso (1:ℤ)).app X
    have hz : (a ≫ e.hom) ≫ T.mor₁⟦(1:ℤ)⟧' = 0 := by
      have hshift := shifted_zero_homology f hf n a
      change a ≫ F.map ((shiftFunctor Spectrum (1:ℤ)).map f) = 0 at hshift
      have hn := (F.commShiftIso (1:ℤ)).hom.naturality f
      change F.map ((shiftFunctor Spectrum (1:ℤ)).map f) ≫ (F.commShiftIso (1:ℤ)).hom.app Y =
        e.hom ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map f) at hn
      change (a ≫ e.hom) ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map f) = 0
      rw [Category.assoc, ← hn, ← Category.assoc, hshift, zero_comp]
    obtain ⟨b,hb⟩ := T.coyoneda_exact₁ hT (a ≫ e.hom) hz
    refine ⟨b,?_⟩
    apply (cancel_mono e.hom).mp
    change (b ≫ (background.coefficients.object ◁ HasFunctorialCofiber.cofibδ f)) ≫ e.hom = a ≫ e.hom
    change a ≫ e.hom = b ≫ ((background.coefficients.object ◁ HasFunctorialCofiber.cofibδ f) ≫ e.hom) at hb
    simpa only [Category.assoc] using hb.symm

private theorem actual_rotated_cofiber_lift {X Y : Spectrum}
    (f : X ⟶ Y) (hf : ZeroOnModTwoHomology background.coefficients f) :
    ∃ R : SyntheticTriangleLift background
      (Triangle.mk f (HasFunctorialCofiber.cofibι f)
        (HasFunctorialCofiber.cofibδ f)).rotate, R.FullLiftComparison background := by
  have hz : ZeroOnModTwoHomology background.coefficients
      (-(shiftFunctor Spectrum (1:ℤ)).map f) := by
    intro n a
    change a ≫ (tensorLeft background.coefficients.object).map (-(shiftFunctor Spectrum (1:ℤ)).map f) = 0
    have hshift : a ≫ (tensorLeft background.coefficients.object).map ((shiftFunctor Spectrum (1:ℤ)).map f) = 0 :=
      shifted_zero_homology f hf n a
    rw [Functor.map_neg, Preadditive.comp_neg, hshift, neg_zero]
  exact triangle_lift _ (rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished f))
    (positive_filtration_of_homology_zero _ hz)
    (rotated_cofiber_homology_short_exact f hf)


private theorem triangle_of_suspension_square
    (hs : background.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map background.auxiliary.nuMap) ≫
        (background.nu.suspensionIso SphereSpectrum).hom =
      (background.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (background.nu.functor.map background.auxiliary.nuMap)) :
    ∀ he : (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f:ℤ) +
      normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g +
      normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h=1,
      KIP126.Literature.NormalizedTriangleCompatible background background.auxiliary.nuRouteTriangle he := by
  have hF : MapFiltrationAtLeast background.classicalTower background.auxiliary.nuMap 1 := by
    classical
    have he := nuCofiber_nu_exponent
    change (if MapFiltrationAtLeast background.classicalTower background.auxiliary.nuMap 1 then 1 else 0)=1 at he
    by_contra hn
    simp only [if_neg hn] at he
    contradiction
  have hzero : ZeroOnModTwoHomology background.coefficients background.auxiliary.nuMap := by
    have hfac := (KIP126.AdamsSynthetic.Completed.factorization_filtration_iff background.auxiliary.nuMap 1).mpr hF
    exact nuFactorizationZeroOnHomology (hfac 1 (by decide) (by decide))
  obtain ⟨R,_⟩ := actual_rotated_cofiber_lift background.auxiliary.nuMap hzero
  intro he
  exact source_triangle_of_rotation_and_square nuCofiber_nu_exponent
    nuCofiber_bottom_exponent nuCofiber_top_exponent R hs he


-- ν suspension naturality.
private theorem nu_suspension_square_proof :
    background.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map background.auxiliary.nuMap) ≫
        (background.nu.suspensionIso SphereSpectrum).hom =
      (background.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
        (SyntheticCategory.biShift (1,1)).map (background.nu.functor.map background.auxiliary.nuMap) := by
  have tensorRight_fullyFaithful_of_inverse (A Z : Spectrum)
      (e : A ⊗ Z ≅ 𝟙_ Spectrum) : (tensorRight A).Full ∧ (tensorRight A).Faithful := by
    have compIso (P Q : Spectrum) (e : P ⊗ Q ≅ 𝟙_ Spectrum) :
        tensorRight P ⋙ tensorRight Q ≅ 𝟭 Spectrum := by
      refine NatIso.ofComponents (fun X =>
        (α_ X P Q) ≪≫ (tensorLeft X).mapIso e ≪≫ (ρ_ X)) ?_
      intro X Y f
      change (f ▷ P ▷ Q) ≫ ((α_ Y P Q).hom ≫ (Y ◁ e.hom) ≫ (ρ_ Y).hom) =
        ((α_ X P Q).hom ≫ (X ◁ e.hom) ≫ (ρ_ X).hom) ≫ f
      simp only [Category.assoc]
      rw [associator_naturality_left_assoc]
      rw [← whisker_exchange_assoc]
      rw [rightUnitor_naturality]
    let i := compIso A Z e
    let j := compIso Z A ((β_ Z A) ≪≫ e)
    letI : (tensorRight Z).Faithful := Functor.Faithful.of_comp_iso j
    exact ⟨Functor.Full.of_comp_faithful_iso i, Functor.Faithful.of_comp_iso i⟩

  have sphere_tensorRight_fullyFaithful (n : ℤ)
      [(tensorRight (Sphere (C := Spectrum) (-n))).CommShift ℤ] :
      (tensorRight (Sphere (C := Spectrum) n)).Full ∧
        (tensorRight (Sphere (C := Spectrum) n)).Faithful := by
    let e : (Sphere (C := Spectrum) n) ⊗ Sphere (-n) ≅ 𝟙_ Spectrum :=
      ((tensorRight (Sphere (C := Spectrum) (-n))).commShiftIso n).app (𝟙_ Spectrum) ≪≫
        (shiftFunctor Spectrum n).mapIso (λ_ (Sphere (C := Spectrum) (-n))) ≪≫
        (shiftFunctorCompIsoId Spectrum (-n) n (by omega)).app (𝟙_ Spectrum)
    exact tensorRight_fullyFaithful_of_inverse _ _ e

  have scalar_end_cancellation
      (A B Z : Spectrum) [(tensorRight A).Full] [(tensorRight Z).Faithful]
      (e : B ⊗ Z ≅ A) (f : A ⟶ B) (κ : A ⟶ A)
      (hκ : ((f ▷ Z) ≫ e.hom) ≫ κ = (f ▷ Z) ≫ e.hom) :
      κ ≫ f = f := by
    let scalar (c : 𝟙_ Spectrum ⟶ 𝟙_ Spectrum) (X : Spectrum) : X ⟶ X :=
      (λ_ X).inv ≫ (c ▷ X) ≫ (λ_ X).hom
    have scalar_natural (c : 𝟙_ Spectrum ⟶ 𝟙_ Spectrum) {X Y : Spectrum} (g : X ⟶ Y) :
        scalar c X ≫ g = g ≫ scalar c Y := by
      dsimp [scalar]
      simp only [Category.assoc]
      rw [← leftUnitor_naturality, ← whisker_exchange_assoc,
        leftUnitor_inv_naturality_assoc]
    have scalar_tensor (c : 𝟙_ Spectrum ⟶ 𝟙_ Spectrum) (X Y : Spectrum) :
        scalar c (X ⊗ Y) = (scalar c X) ▷ Y := by
      dsimp [scalar]
      simp only [leftUnitor_tensor_inv, leftUnitor_tensor_hom,
        whiskerRight_tensor, comp_whiskerRight, Category.assoc,
        Iso.hom_inv_id_assoc]
    obtain ⟨c, hc⟩ := (tensorRight A).map_surjective
      ((λ_ A).hom ≫ κ ≫ (λ_ A).inv)
    change c ▷ A = (λ_ A).hom ≫ κ ≫ (λ_ A).inv at hc
    have hscalar : scalar c A = κ := by
      dsimp [scalar]
      rw [hc]
      simp
    have hwhisker : (f ▷ Z) ≫ (scalar c B ▷ Z) = f ▷ Z := by
      apply (cancel_mono e.hom).mp
      rw [← scalar_tensor]
      rw [Category.assoc, scalar_natural, hscalar]
      simpa only [Category.assoc] using hκ
    have hright : f ≫ scalar c B = f := by
      apply (tensorRight Z).map_injective
      change (f ≫ scalar c B) ▷ Z = f ▷ Z
      rw [comp_whiskerRight]
      exact hwhisker
    rw [← hscalar, scalar_natural, hright]

  have lambda_powers_injective_of_lower_weights
      (coh : BiShiftCoherence SyntheticSpectrum) (m wt : ℤ) (X : SyntheticSpectrum)
      (h : ∀ wt' : ℤ, wt' ≤ wt → LambdaInjectiveAt m wt' X) :
      ∀ k : ℕ, Function.Injective (fun a : BiHom m wt X => lambdaMultiply k a) := by
    have one (k : ℕ) : Function.Injective (fun a :
        (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn (Syn := SyntheticSpectrum) m wt) ⟶ X =>
        SyntheticCategory.lam.app _ ≫ a) := by
      let e : Smn (Syn := SyntheticSpectrum) m (wt-k) ≅
          (SyntheticCategory.biShift (0,-(k : ℤ))).obj (Smn m wt) :=
        eqToIso (by dsimp only [Smn]; congr 1; simp [sub_eq_add_neg]) ≪≫
          ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).app S_0_0).symm
      intro a b hab
      apply (cancel_epi e.hom).mp
      apply h (wt-k) (by omega)
      dsimp only [lambdaAction]
      have hc : SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m (wt-k)) ≫ (e.hom ≫ a) =
          SyntheticCategory.lam.app (Smn (Syn := SyntheticSpectrum) m (wt-k)) ≫ (e.hom ≫ b) := by
        have hn := SyntheticCategory.lam.naturality e.hom
        dsimp only [Functor.id_map] at hn
        rw [← Category.assoc, ← Category.assoc, ← hn]
        simpa only [Category.assoc] using
          congrArg (fun z => (SyntheticCategory.biShift (0,-1)).map e.hom ≫ z) hab
      exact congrArg (fun z => _ ≫ _ ≫ z) hc
    have powers (k : ℕ) : Function.Injective (fun a : BiHom m wt X =>
        lambdaPow k (Smn m wt) ≫ a) := by
      induction k with
      | zero =>
        intro a b hab
        exact (cancel_epi (SyntheticCategory.biShift_zero.hom.app (Smn m wt))).mp hab
      | succ k ih =>
        intro a b hab
        apply ih
        apply one k
        rw [lambdaPow_add coh k 1 (k+1) rfl, lambdaPow_one coh] at hab
        have hc := (cancel_epi ((lambdaShiftAddIso k 1 (k+1) rfl).inv.app (Smn (Syn := SyntheticSpectrum) m wt))).mp
          (by simpa only [Category.assoc] using hab)
        have hn := SyntheticCategory.lam.naturality (lambdaPow k (Smn (Syn := SyntheticSpectrum) m wt))
        dsimp only [Functor.id_map] at hn
        change (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
          (SyntheticCategory.lam.app (Smn m wt) ≫ a) =
          (SyntheticCategory.biShift (0,-1)).map (lambdaPow k (Smn m wt)) ≫
          (SyntheticCategory.lam.app (Smn m wt) ≫ b) at hc
        rw [← Category.assoc, ← Category.assoc] at hc
        rw [hn] at hc
        simpa only [Category.assoc] using hc
    intro k a b hab
    apply powers k
    delta lambdaMultiply at hab
    have hc := (cancel_epi (eqToHom (by congr 1; simp))).mp hab
    exact (cancel_epi ((SyntheticCategory.biShift_comp (m,wt) (0,-(k : ℤ))).inv.app S_0_0)).mp
      (by simpa only [Category.assoc] using hc)

  have low_realization_zero_iff
       {m wt : ℤ} (hw : wt ≤ m+1)
      (a : BiHom m wt (S_0_0 : SyntheticSpectrum)) : background.recovery.realization.map a = 0 ↔ a = 0 := by
    letI := background.recovery.adjunction.isLeftAdjoint
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts background.recovery.realization
    letI := Functor.additive_of_preservesBinaryBiproducts background.recovery.realization
    constructor
    · intro ha
      obtain ⟨k,hk⟩ := (selected_realization_kernel .sphere m wt a).mp ha
      have hi := lambda_powers_injective_of_lower_weights background.quotients.coherence m wt
        (S_0_0 : SyntheticSpectrum) (fun wt' h => lambda_injective_below_diagonal m wt' (by omega))
      apply hi k
      delta lambdaMultiply at hk ⊢
      simpa only [comp_zero] using hk
    · rintro rfl
      exact background.recovery.realization.map_zero _ _

  have third_arrow_unique_of_no_return
      {A B E : Spectrum} (f : A ⟶ B) (g : B ⟶ E) (h h' : E ⟶ A⟦(1:ℤ)⟧)
      (hT : Triangle.mk f g h ∈ distTriang Spectrum)
      (hT' : Triangle.mk f g h' ∈ distTriang Spectrum)
      (hzero : ∀ z : A⟦(1:ℤ)⟧ ⟶ E, z = 0) : h = h' := by
    obtain ⟨c,hc,hc'⟩ := complete_distinguished_triangle_morphism
      (Triangle.mk f g h) (Triangle.mk f g h') hT hT' (𝟙 A) (𝟙 B) (by
        change f ≫ 𝟙 B = 𝟙 A ≫ f
        exact (Category.comp_id f).trans (Category.id_comp f).symm)
    change E ⟶ E at c
    change g ≫ c = 𝟙 B ≫ g at hc
    change h ≫ (shiftFunctor Spectrum (1:ℤ)).map (𝟙 A) = c ≫ h' at hc'
    have hz : g ≫ (c - 𝟙 E) = 0 := by
      simpa only [Triangle.mk_mor₂, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, sub_eq_zero] using hc
    obtain ⟨z,hz'⟩ := (Triangle.mk f g h).yoneda_exact₃ hT (c-𝟙 E) hz
    have he : c = 𝟙 E := by
      apply sub_eq_zero.mp
      rw [hz', hzero z, comp_zero]
    rw [(shiftFunctor Spectrum (1:ℤ)).map_id A, Category.comp_id, he, Category.id_comp] at hc'
    exact hc'

  have realized_triangle_lift_third
      (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
      (L : SyntheticTriangleLift background T)
      (hzero : ∀ z : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₃, z = 0) :
      letI := background.exactness.realizationShift
      background.recovery.nuRealizationIso.inv.app T.obj₃ ≫
        background.recovery.realization.map (L.connecting ≫ (background.nu.boundaryLandingIso T.obj₁).hom) ≫
        (background.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor Spectrum (1:ℤ)).map (background.recovery.nuRealizationIso.hom.app T.obj₁) = T.mor₃ := by
    letI := background.exactness.realizationShift
    letI := background.exactness.realizationExact
    let F := background.recovery.realization
    let e := background.recovery.nuRealizationIso
    let U := Triangle.mk (background.nu.functor.map T.mor₁) (background.nu.functor.map T.mor₂)
      (L.connecting ≫ (background.nu.boundaryLandingIso T.obj₁).hom)
    let d := e.inv.app T.obj₃ ≫ F.map U.mor₃ ≫
      (F.commShiftIso (1:ℤ)).hom.app U.obj₁ ≫
      (shiftFunctor Spectrum (1:ℤ)).map (e.hom.app T.obj₁)
    have hU : U ∈ distTriang SyntheticSpectrum := L.distinguished
    have hi : F.mapTriangle.obj U ≅ Triangle.mk T.mor₁ T.mor₂ d := by
      refine Triangle.isoMk _ _ (e.app T.obj₁) (e.app T.obj₂) (e.app T.obj₃) ?_ ?_ ?_
      · exact background.recovery.nuRealizationIso.hom.naturality T.mor₁
      · exact background.recovery.nuRealizationIso.hom.naturality T.mor₂
      · change (F.map U.mor₃ ≫ (F.commShiftIso (1:ℤ)).hom.app U.obj₁) ≫
          (shiftFunctor Spectrum (1:ℤ)).map (e.hom.app T.obj₁) = e.hom.app T.obj₃ ≫ d
        dsimp only [d]
        simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    have hd : Triangle.mk T.mor₁ T.mor₂ d ∈ distTriang Spectrum :=
      isomorphic_distinguished _ (F.map_distinguished U hU) _ hi.symm
    change d = T.mor₃
    exact third_arrow_unique_of_no_return T.mor₁ T.mor₂ d T.mor₃ hd hT hzero

  have realized_suspension_normalization_on_third
      (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
      (L : SyntheticTriangleLift background T)
      (hzero : ∀ z : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₃, z = 0) :
      letI := background.exactness.realizationShift
      letI := realization_lambda_iso (background.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))
      T.mor₃ ≫ (background.recovery.nuRealizationIso.inv.app (T.obj₁⟦(1:ℤ)⟧) ≫
        inv (background.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
        background.recovery.realization.map (background.nu.boundaryLandingIso T.obj₁).hom ≫
        (background.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
        (shiftFunctor Spectrum (1:ℤ)).map (background.recovery.nuRealizationIso.hom.app T.obj₁)) = T.mor₃ := by
    letI := background.exactness.realizationShift
    letI := realization_lambda_iso (background.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))
    let F := background.recovery.realization
    let e := background.recovery.nuRealizationIso
    have hf : e.inv.app T.obj₃ ≫ F.map L.connecting =
        T.mor₃ ≫ e.inv.app (T.obj₁⟦(1:ℤ)⟧) ≫
          inv (F.map (SyntheticCategory.lam.app _)) := by
      apply (cancel_mono (F.map (SyntheticCategory.lam.app
        (background.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))))).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← F.map_comp, L.factorization]
      have hn := e.inv.naturality T.mor₃
      exact hn.symm
    have hd := realized_triangle_lift_third T hT L hzero
    change e.inv.app T.obj₃ ≫ F.map (L.connecting ≫ (background.nu.boundaryLandingIso T.obj₁).hom) ≫
      (F.commShiftIso (1:ℤ)).hom.app _ ≫
      (shiftFunctor Spectrum (1:ℤ)).map (e.hom.app T.obj₁) = T.mor₃ at hd
    simp only [F.map_comp, Category.assoc] at hd
    rw [← Category.assoc (e.inv.app T.obj₃) (F.map L.connecting), hf] at hd
    simpa only [Category.assoc] using hd

  have normalization_fixes_shift_of_tensor_zero


      {X Y : Spectrum} (f : X ⟶ Y) (hf : ZeroOnModTwoHomology background.coefficients f)
      (hzero : ∀ z : Y⟦(1:ℤ)⟧ ⟶ X⟦(1:ℤ)⟧, z = 0) :
      letI := background.exactness.realizationShift
      letI := realization_lambda_iso (background.nu.functor.obj (Y⟦(1:ℤ)⟧))
      (shiftFunctor Spectrum (1:ℤ)).map f ≫
        (background.recovery.nuRealizationIso.inv.app (Y⟦(1:ℤ)⟧) ≫
          inv (background.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
          background.recovery.realization.map (background.nu.boundaryLandingIso Y).hom ≫
          (background.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor Spectrum (1:ℤ)).map (background.recovery.nuRealizationIso.hom.app Y)) =
        (shiftFunctor Spectrum (1:ℤ)).map f := by
    letI := background.exactness.realizationShift
    letI := realization_lambda_iso (background.nu.functor.obj (Y⟦(1:ℤ)⟧))
    let T := (Triangle.mk f (HasFunctorialCofiber.cofibι f)
      (HasFunctorialCofiber.cofibδ f)).rotate
    have hT : T ∈ distTriang Spectrum := rot_of_distTriang _
      (HasFunctorialCofiber.cofib_distinguished f)
    obtain ⟨L,hL⟩ := actual_rotated_cofiber_lift f hf
    have ht := realized_suspension_normalization_on_third T hT L hzero
    change (-(shiftFunctor Spectrum (1:ℤ)).map f) ≫ _ = -(shiftFunctor Spectrum (1:ℤ)).map f at ht
    simpa only [T, Triangle.rotate_obj₁, Triangle.mk_obj₂, Preadditive.neg_comp, neg_inj] using ht

  have realized_boundary_square_of_normalization_natural
      {X Y : Spectrum} (f : X ⟶ Y) :
      letI := background.exactness.realizationShift
      let κ (A : Spectrum) : A⟦(1:ℤ)⟧ ⟶ A⟦(1:ℤ)⟧ :=
        letI := realization_lambda_iso (background.nu.functor.obj (A⟦(1:ℤ)⟧))
        background.recovery.nuRealizationIso.inv.app (A⟦(1:ℤ)⟧) ≫
          inv (background.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
          background.recovery.realization.map (background.nu.boundaryLandingIso A).hom ≫
          (background.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
          (shiftFunctor Spectrum (1:ℤ)).map (background.recovery.nuRealizationIso.hom.app A)
      (shiftFunctor Spectrum (1:ℤ)).map f ≫ κ Y = κ X ≫ (shiftFunctor Spectrum (1:ℤ)).map f →
        background.recovery.realization.map ((SyntheticCategory.biShift (0,-1)).map
          (background.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
          (background.nu.boundaryLandingIso Y).hom) =
        background.recovery.realization.map ((background.nu.boundaryLandingIso X).hom ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)) := by
    letI := background.exactness.realizationShift
    dsimp only
    intro hk
    let F := background.recovery.realization
    let e := background.recovery.nuRealizationIso
    let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    let S := shiftFunctor Spectrum (1:ℤ)
    letI (A : Spectrum) := realization_lambda_iso (background.nu.functor.obj (S.obj A))
    let β (A : Spectrum) : S.obj A ≅ F.obj (G.obj (background.nu.functor.obj (S.obj A))) :=
      (e.app (S.obj A)).symm ≪≫ (asIso (F.map (SyntheticCategory.lam.app _))).symm
    let j (A : Spectrum) : F.obj ((shiftFunctor SyntheticSpectrum (1:ℤ)).obj (background.nu.functor.obj A)) ≅ S.obj A :=
      (F.commShiftIso (1:ℤ)).app _ ≪≫ S.mapIso (e.app A)
    have hβ : S.map f ≫ (β Y).hom = (β X).hom ≫
        F.map (G.map (background.nu.functor.map (S.map f))) := by
      apply (cancel_mono (F.map (SyntheticCategory.lam.app
        (background.nu.functor.obj (S.obj Y))))).mp
      dsimp only [β, Iso.trans_hom, Iso.symm_hom, asIso_inv]
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← F.map_comp]
      have hn := SyntheticCategory.lam.naturality (background.nu.functor.map (S.map f))
      change G.map (background.nu.functor.map (S.map f)) ≫ SyntheticCategory.lam.app _ =
        SyntheticCategory.lam.app _ ≫ background.nu.functor.map (S.map f) at hn
      rw [hn, F.map_comp]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      exact e.inv.naturality (S.map f)
    have hj : F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)) ≫ (j Y).hom =
        (j X).hom ≫ S.map f := by
      have hn := (F.commShiftIso (1:ℤ)).hom.naturality (background.nu.functor.map f)
      change F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)) ≫
        (F.commShiftIso (1:ℤ)).hom.app _ =
        (F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (F.map (background.nu.functor.map f)) at hn
      change F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)) ≫
          ((F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (e.hom.app Y)) =
        ((F.commShiftIso (1:ℤ)).hom.app _ ≫ S.map (e.hom.app X)) ≫ S.map f
      rw [← Category.assoc, hn]
      simp only [Category.assoc, ← S.map_comp]
      have he := background.recovery.nuRealizationIso.hom.naturality f
      change F.map (background.nu.functor.map f) ≫ e.hom.app Y = e.hom.app X ≫ f at he
      rw [he]
    apply (cancel_epi (β X).hom).mp
    apply (cancel_mono (j Y).hom).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc (β X).hom (F.map (G.map (background.nu.functor.map (S.map f)))), ← hβ]
    rw [← Category.assoc (F.map (background.nu.boundaryLandingIso X).hom)
      (F.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map f)))]
    rw [Category.assoc _ _ (j Y).hom, hj]
    dsimp only [β, j, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, F, e, S]
    simpa only [Category.assoc] using hk

  have suspension_square_of_boundary_square (N : NuFunctorData Spectrum SyntheticSpectrum)
      {X Y : Spectrum} (f : X ⟶ Y)
      (hb : (SyntheticCategory.biShift (0,-1)).map
          (N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
          (N.boundaryLandingIso Y).hom =
        (N.boundaryLandingIso X).hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (N.functor.map f)) :
      N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f) ≫ (N.suspensionIso Y).hom =
        (N.suspensionIso X).hom ≫ (SyntheticCategory.biShift (1,1)).map (N.functor.map f) := by
    let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    let j : SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (1,1) ⋙ G ≅ shiftFunctor SyntheticSpectrum (1:ℤ) :=
      SyntheticCategory.biShift_comp (1,1) (0,-1) ≪≫ SyntheticCategory.biShift_compat 1
    apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (0,-1)).map_injective
    apply (cancel_mono (j.hom.app (N.functor.obj Y))).mp
    simp only [Functor.map_comp, Category.assoc]
    change G.map (N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
        G.map (N.suspensionIso Y).hom ≫ j.hom.app (N.functor.obj Y) =
      G.map (N.suspensionIso X).hom ≫
        G.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
          j.hom.app (N.functor.obj Y)
    have hn := j.hom.naturality (N.functor.map f)
    change G.map ((SyntheticCategory.biShift (1,1)).map (N.functor.map f)) ≫
      j.hom.app (N.functor.obj Y) = j.hom.app (N.functor.obj X) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (N.functor.map f) at hn
    rw [hn]
    change G.map (N.functor.map ((shiftFunctor Spectrum (1:ℤ)).map f)) ≫
        (G.map (N.suspensionIso Y).hom ≫ j.hom.app (N.functor.obj Y)) =
      (G.map (N.suspensionIso X).hom ≫ j.hom.app (N.functor.obj X)) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (N.functor.map f) at hb
    simpa only [Category.assoc] using hb

  have suspension_square_of_realized_boundary_square

      (hb : background.recovery.realization.map ((SyntheticCategory.biShift (0,-1)).map
          (background.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map background.auxiliary.nuMap)) ≫
          (background.nu.boundaryLandingIso SphereSpectrum).hom) =
        background.recovery.realization.map ((background.nu.boundaryLandingIso (Sphere (C:=Spectrum) 3)).hom ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map (background.nu.functor.map background.auxiliary.nuMap))) :
      background.nu.functor.map ((shiftFunctor Spectrum (1:ℤ)).map background.auxiliary.nuMap) ≫
          (background.nu.suspensionIso SphereSpectrum).hom =
        (background.nu.suspensionIso (Sphere (C:=Spectrum) 3)).hom ≫
          (SyntheticCategory.biShift (1,1)).map (background.nu.functor.map background.auxiliary.nuMap) := by
    letI := background.exactness.realizationShift
    letI := background.recovery.adjunction.isLeftAdjoint
    letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts background.recovery.realization
    letI := Functor.additive_of_preservesBinaryBiproducts background.recovery.realization
    let F := background.recovery.realization
    let S := shiftFunctor SyntheticSpectrum (1:ℤ)
    let A := background.nu.functor.obj (Sphere (C:=Spectrum) 3)
    let B := background.nu.functor.obj SphereSpectrum
    have hinj : Function.Injective (fun a : A ⟶ B => F.map a) := by
      intro a b hab
      have hz : F.map ((nuSphereThree background).inv ≫ (a-b) ≫ background.nu.unitIso.hom) = 0 := by
        simp only [F.map_comp, Functor.map_sub, hab, sub_self, zero_comp, comp_zero]
      have ht := (low_realization_zero_iff (m:=3) (wt:=3) (by omega)
        ((nuSphereThree background).inv ≫ (a-b) ≫ background.nu.unitIso.hom)).mp hz
      apply sub_eq_zero.mp
      apply (cancel_mono background.nu.unitIso.hom).mp
      apply (cancel_epi (nuSphereThree background).inv).mp
      simpa only [Category.assoc, comp_zero, zero_comp] using ht
    have hshift : Function.Injective (fun a : S.obj A ⟶ S.obj B => F.map a) := by
      intro a b hab
      change F.map a = F.map b at hab
      have ha := S.map_preimage a
      have hb := S.map_preimage b
      have he : F.map (S.preimage a) = F.map (S.preimage b) := by
        apply (shiftFunctor Spectrum (1:ℤ)).map_injective
        apply (cancel_epi ((F.commShiftIso (1:ℤ)).hom.app A)).mp
        have hna := (F.commShiftIso (1:ℤ)).hom.naturality (S.preimage a)
        have hnb := (F.commShiftIso (1:ℤ)).hom.naturality (S.preimage b)
        change F.map (S.map (S.preimage a)) ≫ (F.commShiftIso (1:ℤ)).hom.app B =
          (F.commShiftIso (1:ℤ)).hom.app A ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map (S.preimage a)) at hna
        change F.map (S.map (S.preimage b)) ≫ (F.commShiftIso (1:ℤ)).hom.app B =
          (F.commShiftIso (1:ℤ)).hom.app A ≫ (shiftFunctor Spectrum (1:ℤ)).map (F.map (S.preimage b)) at hnb
        rw [ha] at hna
        rw [hb] at hnb
        rw [← hna, ← hnb, hab]
      calc a = S.map (S.preimage a) := ha.symm
           _ = S.map (S.preimage b) := congrArg S.map (hinj he)
           _ = b := hb
    apply suspension_square_of_boundary_square background.nu background.auxiliary.nuMap
    apply (cancel_epi (background.nu.boundaryLandingIso (Sphere (C:=Spectrum) 3)).inv).mp
    apply hshift
    simpa only [Functor.map_comp, Category.assoc] using congrArg (fun z =>
      F.map (background.nu.boundaryLandingIso (Sphere (C:=Spectrum) 3)).inv ≫ z) hb

  letI := background.exactness.realizationShift
  let S := shiftFunctor Spectrum (1:ℤ)
  let Z := Sphere (C:=Spectrum) 3
  let f := background.auxiliary.nuMap
  letI (X : Spectrum) := realization_lambda_iso (background.nu.functor.obj (S.obj X))
  let κ (X : Spectrum) : S.obj X ⟶ S.obj X :=
    background.recovery.nuRealizationIso.inv.app (S.obj X) ≫
      inv (background.recovery.realization.map (SyntheticCategory.lam.app _)) ≫
      background.recovery.realization.map (background.nu.boundaryLandingIso X).hom ≫
      (background.recovery.realization.commShiftIso (1:ℤ)).hom.app _ ≫
      S.map (background.recovery.nuRealizationIso.hom.app X)
  have hneg (a : (𝟙_ Spectrum) ⟶ Z) : a = 0 := by
    let F := shiftFunctor Spectrum (-3:ℤ)
    let e : F.obj Z ≅ 𝟙_ Spectrum :=
      (shiftFunctorCompIsoId Spectrum 3 (-3) (by omega)).app (𝟙_ Spectrum)
    have hz : F.map a ≫ e.hom = 0 := by
      haveI : Subsingleton (HomotopyGroup (-3) (SphereSpectrum : Spectrum)) :=
        sphere_connected (-3) (by omega)
      exact Subsingleton.elim _ _
    apply F.map_injective
    rw [Functor.map_zero]
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using hz
  have hF : MapFiltrationAtLeast background.classicalTower f 1 := by
    classical
    have he := nuCofiber_nu_exponent
    change (if MapFiltrationAtLeast background.classicalTower f 1 then 1 else 0)=1 at he
    by_contra hn
    simp only [if_neg hn] at he
    contradiction
  have hf : ZeroOnModTwoHomology background.coefficients f := by
    have hfac := (KIP126.AdamsSynthetic.Completed.factorization_filtration_iff f 1).mpr hF
    exact nuFactorizationZeroOnHomology (hfac 1 (by decide) (by decide))
  have hret (a : S.obj (𝟙_ Spectrum) ⟶ S.obj Z) : a = 0 := by
    have ha := S.map_preimage a
    rw [hneg (S.preimage a), Functor.map_zero] at ha
    exact ha.symm
  have hy : S.map f ≫ κ (𝟙_ Spectrum) = S.map f :=
    normalization_fixes_shift_of_tensor_zero f hf hret
  obtain ⟨hfullZ,hfaithZ⟩ := sphere_tensorRight_fullyFaithful 3
  letI : (tensorRight Z).Full := hfullZ
  letI : (tensorRight Z).Faithful := hfaithZ
  let q : Z ⊗ Z ⟶ Z := (f ▷ Z) ≫ (λ_ Z).hom
  have hq : ZeroOnModTwoHomology background.coefficients q := by
    let H := background.coefficients.object
    let F := tensorRight Z
    intro i x
    let e : Sphere (C:=Spectrum) (i-3) ⊗ Z ≅ Sphere i :=
      KIP126.AdamsSynthetic.Completed.closedBackground.smashSpheres (i-3) 3 ≪≫
        eqToIso (by congr 1; omega)
    let b : HomotopyGroup (i-3) (H ⊗ Z) :=
      F.preimage (e.hom ≫ x ≫ (α_ H Z Z).inv)
    have hb : F.map b = e.hom ≫ x ≫ (α_ H Z Z).inv := F.map_preimage _
    have hz := congrArg F.map (hf (i-3) b)
    change F.map (b ≫ (H ◁ f)) = F.map 0 at hz
    rw [Functor.map_comp, Functor.map_zero, hb] at hz
    have hz' := congrArg (fun z => z ≫ (α_ H (𝟙_ Spectrum) Z).hom) hz
    change ((e.hom ≫ x ≫ (α_ H Z Z).inv) ≫ ((H ◁ f) ▷ Z)) ≫
      (α_ H (𝟙_ Spectrum) Z).hom = _ at hz'
    simp only [Category.assoc, associator_naturality_middle, zero_comp] at hz'
    change e.hom ≫ x ≫ (α_ H Z Z).inv ≫ (α_ H Z Z).hom ≫
      H ◁ (f ▷ Z) = 0 at hz'
    simp only [Iso.inv_hom_id_assoc] at hz'
    have hz'' : x ≫ (H ◁ (f ▷ Z)) = 0 := by
      apply (cancel_epi e.hom).mp
      simpa only [Category.assoc, comp_zero] using hz'
    change x ≫ (H ◁ ((f ▷ Z) ≫ (λ_ Z).hom)) = 0
    rw [whiskerLeft_comp, ← Category.assoc, hz'', zero_comp]
  have hretq (a : S.obj Z ⟶ S.obj (Z ⊗ Z)) : a = 0 := by
    have ha := S.map_preimage a
    have hb := (tensorRight Z).map_preimage ((λ_ Z).hom ≫ S.preimage a)
    have hz := hneg ((tensorRight Z).preimage ((λ_ Z).hom ≫ S.preimage a))
    rw [hz, Functor.map_zero] at hb
    have hz' : S.preimage a = 0 := by
      apply (cancel_epi (λ_ Z).hom).mp
      simpa only [comp_zero] using hb.symm
    rw [hz', Functor.map_zero] at ha
    exact ha.symm
  have hxq : S.map q ≫ κ Z = S.map q :=
    normalization_fixes_shift_of_tensor_zero q hq hretq
  let e : S.obj (𝟙_ Spectrum) ⊗ Z ≅ S.obj Z :=
    ((tensorRight Z).commShiftIso (1:ℤ)).app (𝟙_ Spectrum) ≪≫ S.mapIso (λ_ Z)
  let j : S.obj Z ⊗ Z ≅ S.obj (Z ⊗ Z) :=
    ((tensorRight Z).commShiftIso (1:ℤ)).app Z
  have hj : (S.map f ▷ Z) ≫ e.hom = j.hom ≫ S.map q := by
    have hn := ((tensorRight Z).commShiftIso (1:ℤ)).hom.naturality f
    change (S.map f ▷ Z) ≫ ((tensorRight Z).commShiftIso (1:ℤ)).hom.app (𝟙_ Spectrum) =
      ((tensorRight Z).commShiftIso (1:ℤ)).hom.app Z ≫ S.map (f ▷ Z) at hn
    change (S.map f ▷ Z) ≫ (((tensorRight Z).commShiftIso (1:ℤ)).hom.app (𝟙_ Spectrum) ≫
      S.map (λ_ Z).hom) = _
    rw [← Category.assoc, hn, Category.assoc, ← S.map_comp]
    rfl
  have hκ : ((S.map f ▷ Z) ≫ e.hom) ≫ κ Z = (S.map f ▷ Z) ≫ e.hom := by
    rw [hj, Category.assoc, hxq]
  let a : S.obj Z ≅ Sphere (C:=Spectrum) 4 :=
    ((shiftFunctorAdd' Spectrum 3 1 4 (by omega)).app (𝟙_ Spectrum)).symm
  let ai : S.obj Z ⊗ Sphere (C:=Spectrum) (-4) ≅ 𝟙_ Spectrum :=
    (tensorRight (Sphere (C:=Spectrum) (-4))).mapIso a ≪≫
      ((tensorRight (Sphere (C:=Spectrum) (-4))).commShiftIso (4:ℤ)).app (𝟙_ Spectrum) ≪≫
      (shiftFunctor Spectrum (4:ℤ)).mapIso (λ_ (Sphere (C:=Spectrum) (-4))) ≪≫
      (shiftFunctorCompIsoId Spectrum (-4) 4 (by omega)).app (𝟙_ Spectrum)
  obtain ⟨hfullA,hfaithA⟩ := tensorRight_fullyFaithful_of_inverse
    (S.obj Z) (Sphere (C:=Spectrum) (-4)) ai
  letI : (tensorRight (S.obj Z)).Full := hfullA
  have hx : κ Z ≫ S.map f = S.map f :=
    scalar_end_cancellation (S.obj Z) (S.obj (𝟙_ Spectrum)) Z e (S.map f) (κ Z) hκ
  apply suspension_square_of_realized_boundary_square
  apply realized_boundary_square_of_normalization_natural f
  exact hy.trans hx.symm



private theorem nuCofiber_triangle_proof :
  ∀ he :
      (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g +
        normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h = 1,
    KIP126.Literature.NormalizedTriangleCompatible background background.auxiliary.nuRouteTriangle he :=
  triangle_of_suspension_square nu_suspension_square_proof

end TensorSupport
end
end NuCofiberConstruction
end NuCofiberConstructionScope

/-- The prescribed normalized arrows form a distinguished triangle. -/
public theorem nuCofiber_triangle :
  ∀ he :
      (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f : ℤ) +
        normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g +
        normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h = 1,
    NormalizedTriangleCompatible background background.auxiliary.nuRouteTriangle he := by
  exact NuCofiberConstruction.nuCofiber_triangle_proof

private def nuCofiberData : NuCofiberApplicability background where
  nu_exponent := nuCofiber_nu_exponent
  bottom_exponent := nuCofiber_bottom_exponent
  top_exponent := nuCofiber_top_exponent
  normalized_label := nuCofiber_normalized_label
  triangle := nuCofiber_triangle


public theorem nuCofiber_exponent_sum :
  (normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.f : ℤ) +
    normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.g +
    normalizedExponent background.classicalTower background.auxiliary.nuRouteTriangle.h = 1 := NuCofiberApplicability.exponent_sum background nuCofiberData


public theorem nuCofiber_distinguished :
  normalizedTriangle background background.auxiliary.nuRouteTriangle nuCofiber_exponent_sum ∈ distTriang SyntheticSpectrum := nuCofiber_triangle _


public theorem nu_cofiber :
  NuCofiberCriterion background := by
  sorry


public theorem lift :
  SyntheticLiftComparison background := by
  sorry

end KIP126.Literature.Standard
end
