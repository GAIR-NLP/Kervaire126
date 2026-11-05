module

import KIP126.Literature.Standard.ClassicalInputs
import KIP126.Literature.Standard.NormalizedTriangles
import KIP126.AdamsSynthetic.Completed.ClassicalSupport
import KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle
import KIP126.ProofTools.GeneralizedMahowald.BoundaryLambda
import KIP126.AdamsComputation.Moore.Object

/-! The normalized attaching map for the Moore-spectrum construction.
Lambda-division uniqueness uses first-quotient vanishing; a C₂ numerical
comparison and existence of a common lift are separate conditions. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

private theorem quotient_one_negative (X : AdamsObject (coefficients := background.coefficients)) (m w : ℤ)
    (h : w < m)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1)) :
    a = 0 := by
  let e := (background.quotients.functoriality.functor 1).mapIso
    ((SyntheticCategory.biShift_zero (Syn:=SyntheticSpectrum)).symm.app
      (background.nu.functor.obj (X.obj background.auxiliary)))
  haveI := classical_page_negative X 2 (w-m) w (by omega)
  have he : a ≫ e.hom = 0 := by
    let e0 := background.firstQuotient X 0 (w-m) w
    have hz : (e0 (homotopyRegrade (by omega) (by simp) (a≫e.hom))) = 0 :=
      Subsingleton.elim _ _
    have hz' : homotopyRegrade (m':=w-(w-m)) (w':=w+0) (by omega) (by simp) (a≫e.hom) = 0 :=
      e0.injective (hz.trans (map_zero e0).symm)
    have hc {m' w' : ℤ} (hm : m=m') (hw : w=w')
        (c : BiHom m w (XModLambdaN (nuZero background X) 1)) :
        homotopyRegrade hm hw c=0 ↔ c=0 := by
      subst m'; subst w'; rfl
    exact (hc _ _ _).mp hz'

  exact (cancel_mono e.hom).mp (by simpa only [zero_comp] using he)

private theorem lambda_one_injective_of_quotient_vanishing
    (D Y : SyntheticSpectrum)
    (hz : ∀ b : D⟦(1:ℤ)⟧ ⟶ XModLambdaN Y 1, b=0)
    (a : D ⟶ (SyntheticCategory.biShift (0,-1)).obj Y)
    (ha : a≫SyntheticCategory.lam.app Y=0) : a=0 := by
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a≫F.map (lambdaPow 1 Y)=0 := by
    rw [←Functor.map_comp,lambdaPow_one background.quotients.coherence,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y 1) (F.map a) hshift
  have hf : F.map a=0 := by rw [hb,hz b,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)

private theorem lambda_one_injective_at_diagonal (X : AdamsObject (coefficients := background.coefficients)) (m w : ℤ)
    (h : w ≤ m)
    (a : Smn (Syn:=SyntheticSpectrum) m w ⟶
      (SyntheticCategory.biShift (0,-1)).obj
        (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : a≫SyntheticCategory.lam.app _ = 0) : a = 0 := by
  let Y := background.nu.functor.obj (X.obj background.auxiliary)
  let F := shiftFunctor SyntheticSpectrum (1:ℤ)
  have hshift : F.map a ≫ F.map (lambdaPow 1 Y) = 0 := by
    rw [←Functor.map_comp]
    have hpow : lambdaPow 1 Y = SyntheticCategory.lam.app Y :=
      lambdaPow_one background.quotients.coherence Y
    rw [hpow,ha,Functor.map_zero]
  obtain ⟨b,hb⟩ := (XModLambdaN.cofiberTriangle Y 1).coyoneda_exact₁
    (XModLambdaN.cofiberTriangle_distinguished Y 1) (F.map a) hshift
  let eS : Smn (Syn:=SyntheticSpectrum) (m+1) w ≅ F.obj (Smn m w) :=
    ((biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app S_0_0).symm ≪≫
      (SyntheticCategory.biShift_compat 1).app (Smn m w)
  have hz : eS.hom≫b=0 := quotient_one_negative X (m+1) w (by omega) _
  have hb0 : b=0 := (cancel_epi eS.hom).mp (by simpa only [comp_zero] using hz)
  have hf : F.map a=0 := by rw [hb,hb0,zero_comp]
  exact F.map_injective (by simpa only [Functor.map_zero] using hf)

private theorem negative_lift_factorization {A B : SyntheticSpectrum} (k : ℕ)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) :
    negativeLift k f ≫ lambdaPow k B = lambdaToPositivePow k A ≫ f := by
  simp only [negativeLift,lambdaToPositivePow,Category.assoc]
  rw [lambdaPow_naturality]


private abbrev twoMap := KIP126.AdamsComputation.Moore.twoMap

private theorem twoMap_exponent : normalizedExponent background.classicalTower twoMap = 1 := by
  let T := background.classicalTower.tower (SphereSpectrum (C := Spectrum))
  obtain ⟨_, _, b, hb, _⟩ := KIP126.Literature.Standard.two_detection
  have hm : KIP126.Literature.classicalTwo (C := Spectrum) ∈ T.filtrationSubmodule 1 0 := by
    have h : KIP126.Literature.classicalTwo (C := Spectrum) ∈
        ModuleCat.subobjectModule _ (T.filtration.F 1 0) := ⟨b, hb⟩
    simpa only [AbstractAdamsTower.filtration, OrderIso.apply_symm_apply] using h
  obtain ⟨a,ha⟩ := hm
  change a ≫ T.projection 1 = KIP126.Literature.classicalTwo (C := Spectrum) at ha
  have hf : MapFiltrationAtLeast background.classicalTower twoMap 1 := by
    refine ⟨(shiftFunctorZero Spectrum ℤ).inv.app SphereSpectrum ≫ a, ?_⟩
    change ((shiftFunctorZero Spectrum ℤ).inv.app SphereSpectrum ≫ a) ≫ T.projection 1 = twoMap
    rw [Category.assoc,ha]
    dsimp only [KIP126.Literature.classicalTwo,twoMap]
    rw [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    rfl
  simp only [normalizedExponent,hf,ite_true]


set_option backward.defeqAttrib.useBackward false

private theorem h0_positive_factorization :
    lambdaToPositivePow 1 (S_0_0 : SyntheticSpectrum) ≫
      KIP126.Literature.Standard.syntheticH0 = 2 • 𝟙 _ := by
  have h := congrArg (fun z => SyntheticCategory.biShift_zero.inv.app
    (S_0_0 : SyntheticSpectrum) ≫ z) KIP126.Literature.Standard.lambdaMultiply_syntheticH0
  change (SyntheticCategory.biShift_zero.inv.app (S_0_0 : SyntheticSpectrum) ≫
    lambdaMultiply 1 KIP126.Literature.Standard.syntheticH0) = _ at h
  simp only [lambdaToPositivePow,lambdaMultiply,Route.syntheticTwo,
    eqToHom_refl,Category.id_comp,Category.assoc,Iso.inv_hom_id_app_assoc,
    Smn,S_0_0,Functor.id_obj] at h ⊢
  norm_num only at h ⊢
  exact h

private def h0NormalizedMap :
    (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj
      (SphereSpectrum (C := Spectrum))) ⟶ background.nu.functor.obj SphereSpectrum :=
  (SyntheticCategory.biShift (0,1)).map background.nu.unitIso.hom ≫
    KIP126.Literature.Standard.syntheticH0 ≫ background.nu.unitIso.inv

private def positiveLambdaSourceIso (k : ℕ) :
    (𝟭 SyntheticSpectrum) ≅ SyntheticCategory.biShift (0,(k:ℤ)) ⋙
      SyntheticCategory.biShift (0,-(k:ℤ)) :=
  SyntheticCategory.biShift_zero.symm ≪≫
    eqToIso (congrArg SyntheticCategory.biShift
      (show ((0:ℤ),(0:ℤ)) = (0,(k:ℤ))+(0,-(k:ℤ)) by ext <;> simp)) ≪≫
    (SyntheticCategory.biShift_comp (0,(k:ℤ)) (0,-(k:ℤ))).symm

private theorem positiveLambdaNaturality (k : ℕ) {A B : SyntheticSpectrum} (f : A ⟶ B) :
    lambdaToPositivePow k A ≫ (SyntheticCategory.biShift (0,(k:ℤ))).map f =
      f ≫ lambdaToPositivePow k B := by
  have factor (A : SyntheticSpectrum) : lambdaToPositivePow k A =
      (positiveLambdaSourceIso k).hom.app A ≫
        lambdaPow k ((SyntheticCategory.biShift (0,(k:ℤ))).obj A) := by
    simp only [positiveLambdaSourceIso,lambdaToPositivePow,Iso.trans_hom,
      Iso.symm_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,Category.assoc]
  rw [factor,factor,Category.assoc,←lambdaPow_naturality]
  have hn := (positiveLambdaSourceIso k).hom.naturality f
  dsimp only [Functor.id_map,Functor.comp_map] at hn
  simpa only [Category.assoc] using (congrArg (fun z => z ≫
    lambdaPow k ((SyntheticCategory.biShift (0,(k:ℤ))).obj B)) hn).symm

private theorem h0NormalizedMap_factorization :
    lambdaToPositivePow 1 (background.nu.functor.obj (SphereSpectrum (C := Spectrum))) ≫
      h0NormalizedMap = background.nu.functor.map twoMap := by
  letI := background.nu.additive
  have hn := positiveLambdaNaturality 1 background.nu.unitIso.hom
  have hf := congrArg (fun z => z ≫ KIP126.Literature.Standard.syntheticH0 ≫
    background.nu.unitIso.inv) hn
  change lambdaToPositivePow 1 (background.nu.functor.obj (SphereSpectrum (C := Spectrum))) ≫
    h0NormalizedMap = _
  calc
    _ = background.nu.unitIso.hom ≫ lambdaToPositivePow 1
        (S_0_0 : SyntheticSpectrum) ≫ KIP126.Literature.Standard.syntheticH0 ≫
          background.nu.unitIso.inv := by
      simp only [h0NormalizedMap,Category.assoc,S_0_0,Smn,SphereSpectrum,Functor.id_obj] at hf ⊢
      norm_num only at hf ⊢
      exact hf
    _ = background.nu.unitIso.hom ≫ (2 • 𝟙 (S_0_0 : SyntheticSpectrum)) ≫
        background.nu.unitIso.inv := by
      simpa only [Category.assoc] using congrArg (fun z => background.nu.unitIso.hom ≫ z ≫ background.nu.unitIso.inv)
        h0_positive_factorization
    _ = _ := by
      simp only [twoMap,KIP126.AdamsComputation.Moore.twoMap,two_smul,Functor.map_add,Functor.map_id,
        Preadditive.comp_add,Preadditive.add_comp,Category.id_comp,Category.comp_id,
        Iso.hom_inv_id,S_0_0]
      rw [background.nu.functor.map_id]


private def selectedTwoNormalized :
    (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj
      (SphereSpectrum (C := Spectrum))) ⟶ background.nu.functor.obj SphereSpectrum :=
  eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
    (background.nu.functor.obj (SphereSpectrum (C := Spectrum)))) twoMap_exponent.symm) ≫
      (background.normalizedMap .sphere .sphere twoMap).map

private theorem selectedTwoNormalized_factorization :
    lambdaToPositivePow 1 (background.nu.functor.obj (SphereSpectrum (C := Spectrum))) ≫
      selectedTwoNormalized = background.nu.functor.map twoMap := by
  have transport (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (background.nu.functor.obj (SphereSpectrum (C := Spectrum))) ⟶ background.nu.functor.obj SphereSpectrum)
      (hF : lambdaToPositivePow e _ ≫ F = background.nu.functor.map twoMap) :
      lambdaToPositivePow 1 _ ≫
        (eqToHom (congrArg (fun k : ℕ => (SyntheticCategory.biShift (0,(k:ℤ))).obj
          (background.nu.functor.obj (SphereSpectrum (C := Spectrum)))) he.symm) ≫ F) =
          background.nu.functor.map twoMap := by
    subst e
    simpa only [eqToHom_refl,Category.id_comp] using hF
  exact transport _ twoMap_exponent _ (background.normalizedMap .sphere .sphere twoMap).factorization

/-- At this sphere source, division by one lambda is unique.  The proof
uses the actual first-quotient vanishing in negative Adams filtration. -/
private theorem positiveLambda_one_unique
    (f g : (SyntheticCategory.biShift (0,1)).obj (background.nu.functor.obj
      (SphereSpectrum (C := Spectrum))) ⟶ background.nu.functor.obj SphereSpectrum)
    (h : lambdaToPositivePow 1 _ ≫ f = lambdaToPositivePow 1 _ ≫ g) : f=g := by
  let U := background.nu.functor.obj (SphereSpectrum (C := Spectrum))
  let a := negativeLift 1 f - negativeLift 1 g
  have ha : a ≫ lambdaPow 1 U = 0 := by
    dsimp only [a]
    rw [Preadditive.sub_comp,negative_lift_factorization,negative_lift_factorization,h,sub_self]
  let z : Smn (Syn := SyntheticSpectrum) 0 0 ⟶
      (SyntheticCategory.biShift (0,-1)).obj U :=
    SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum) ≫ background.nu.unitIso.inv ≫ a
  have hz : z=0 := lambda_one_injective_at_diagonal .sphere 0 0 (by decide) z (by
    rw [←lambdaPow_one background.quotients.coherence]
    change (_ ≫ _ ≫ a) ≫ lambdaPow 1 U=0
    rw [Category.assoc,Category.assoc,ha,comp_zero,comp_zero])
  have ha0 : a=0 := by
    apply (cancel_epi background.nu.unitIso.inv).mp
    apply (cancel_epi (SyntheticCategory.biShift_zero.hom.app (S_0_0 : SyntheticSpectrum))).mp
    simpa only [z,comp_zero] using hz
  have hn : negativeLift 1 f=negativeLift 1 g := sub_eq_zero.mp ha0
  have hp : (positiveLambdaSourceIso 1).hom.app U ≫
      (SyntheticCategory.biShift (0,-(1:ℤ))).map f =
    (positiveLambdaSourceIso 1).hom.app U ≫
      (SyntheticCategory.biShift (0,-(1:ℤ))).map g := by
    simp only [positiveLambdaSourceIso,negativeLift,Iso.trans_hom,Iso.symm_hom,
      NatTrans.comp_app,eqToIso.hom,eqToHom_app,Category.assoc,U,Functor.id_obj] at hn ⊢
    norm_num only at hn ⊢
    exact hn
  apply (SyntheticCategory.biShift_fullyFaithful (Syn := SyntheticSpectrum) (0,-(1:ℤ))).map_injective
  exact (cancel_epi ((positiveLambdaSourceIso 1).hom.app U)).mp hp

private theorem selectedTwoNormalized_eq_h0 : selectedTwoNormalized = h0NormalizedMap :=
  positiveLambda_one_unique _ _
    (selectedTwoNormalized_factorization.trans h0NormalizedMap_factorization.symm)

private theorem positive_factorization_zero_on_homology {X Y : Spectrum} {n : ℕ}
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

private theorem positive_filtration_zero_on_right_homology {X Y : Spectrum}
    (f : X ⟶ Y) (hf : MapFiltrationAtLeast background.classicalTower f 1)
    (i : ℤ) (x : HomotopyGroup i (X ⊗ background.coefficients.object)) :
    x ≫ (f ▷ background.coefficients.object) = 0 := by
  letI := KIP126.AdamsSynthetic.Completed.closedBackground.symmetric
  have hF : FactorizationFiltration background.coefficients f 1 :=
    (KIP126.AdamsSynthetic.Completed.factorization_filtration_iff f 1).mpr hf
  have hz := positive_factorization_zero_on_homology (hF 1 (by decide) (by decide))
  apply (cancel_mono (β_ Y background.coefficients.object).hom).mp
  rw [Category.assoc, BraidedCategory.braiding_naturality_left, ← Category.assoc]
  change modTwoHomologyMap background.coefficients f i
    (x ≫ (β_ X background.coefficients.object).hom) = _
  rw [hz, zero_comp]

/-- The two cell maps have exponent zero on the actual Moore cofiber.
This follows from represented mod-two homology and exactness, independently
of the numerical E₂ data used later. -/
private theorem moore_cell_exponents :
    normalizedExponent background.classicalTower KIP126.AdamsComputation.Moore.bottom = 0 ∧
    normalizedExponent background.classicalTower KIP126.AdamsComputation.Moore.top = 0 := by
  let B := KIP126.AdamsSynthetic.Completed.closedBackground
  let H := background.coefficients.object
  let F := tensorRight H
  letI := B.tensorShift H
  letI := B.tensorExact H
  let T := F.mapTriangle.obj
    (Triangle.mk twoMap KIP126.AdamsComputation.Moore.bottom
      KIP126.AdamsComputation.Moore.top)
  have hT : T ∈ distTriang Spectrum :=
    F.map_distinguished _ KIP126.AdamsComputation.Moore.cofiberSequence.distinguished
  have hF : MapFiltrationAtLeast background.classicalTower twoMap 1 := by
    classical
    have h := twoMap_exponent
    change (if MapFiltrationAtLeast background.classicalTower twoMap 1
      then 1 else 0) = 1 at h
    by_contra hn
    simp only [if_neg hn] at h
    contradiction
  have hf (i : ℤ) (x : HomotopyGroup i T.obj₁) : x ≫ T.mor₁ = 0 :=
    positive_filtration_zero_on_right_homology _ hF i x
  let a : HomotopyGroup 0 T.obj₁ :=
    background.coefficients.pi0Equiv.symm 1 ≫ (λ_ H).inv
  have ha : a ≠ 0 := by
    intro hz
    have h0 : background.coefficients.pi0Equiv.symm 1 = 0 := by
      have hh := congrArg (fun z => z ≫ (λ_ H).hom) hz
      simpa only [a, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        zero_comp] using hh
    have h10 : (1 : ZMod 2) = 0 := by
      simpa only [AddEquiv.apply_symm_apply, map_zero] using
        congrArg background.coefficients.pi0Equiv h0
    exact one_ne_zero h10
  have hbottom : ¬ MapFiltrationAtLeast background.classicalTower
      KIP126.AdamsComputation.Moore.bottom 1 := by
    intro hg
    have hag : a ≫ T.mor₂ = 0 :=
      positive_filtration_zero_on_right_homology _ hg 0 a
    obtain ⟨b, hb⟩ := T.coyoneda_exact₂ hT a hag
    exact ha (hb.trans (hf 0 b))
  have htop : ¬ MapFiltrationAtLeast background.classicalTower
      KIP126.AdamsComputation.Moore.top 1 := by
    intro hh
    let a₁ : HomotopyGroup 1 (T.obj₁⟦(1 : ℤ)⟧) :=
      (shiftFunctorAdd' Spectrum (0 : ℤ) 1 1 (by norm_num)).hom.app SphereSpectrum ≫
        (shiftFunctor Spectrum (1 : ℤ)).map a
    have ha₁ : a₁ ≠ 0 := by
      intro hz
      have h : (shiftFunctor Spectrum (1 : ℤ)).map a = 0 := by
        apply (cancel_epi
          ((shiftFunctorAdd' Spectrum (0 : ℤ) 1 1 (by norm_num)).hom.app SphereSpectrum)).mp
        simpa only [a₁, comp_zero] using hz
      apply ha
      apply (shiftFunctor Spectrum (1 : ℤ)).map_injective
      rw [Functor.map_zero]
      exact h
    have haf : a₁ ≫ (shiftFunctor Spectrum (1 : ℤ)).map T.mor₁ = 0 := by
      dsimp only [a₁]
      rw [Category.assoc, ← Functor.map_comp, hf 0 a, Functor.map_zero, comp_zero]
    obtain ⟨b, hb⟩ := T.coyoneda_exact₁ hT a₁ haf
    have hbh : b ≫ T.mor₃ = 0 := by
      change b ≫ ((KIP126.AdamsComputation.Moore.top ▷ H) ≫ _) = 0
      rw [← Category.assoc]
      have hz := positive_filtration_zero_on_right_homology
        KIP126.AdamsComputation.Moore.top hh 1 b
      change b ≫ (KIP126.AdamsComputation.Moore.top ▷ H) = 0 at hz
      rw [hz, zero_comp]
    exact ha₁ (hb.trans hbh)
  classical
  dsimp only [normalizedExponent]
  simp only [if_neg hbottom, if_neg htop, and_self]

private theorem moore_exponent_sum :
    (normalizedExponent background.classicalTower
      KIP126.AdamsComputation.Moore.triangle.f : ℤ) +
      normalizedExponent background.classicalTower KIP126.AdamsComputation.Moore.triangle.g +
      normalizedExponent background.classicalTower KIP126.AdamsComputation.Moore.triangle.h = 1 := by
  change (normalizedExponent background.classicalTower twoMap : ℤ) +
    normalizedExponent background.classicalTower KIP126.AdamsComputation.Moore.bottom +
    normalizedExponent background.classicalTower KIP126.AdamsComputation.Moore.top = 1
  rw [twoMap_exponent, moore_cell_exponents.1, moore_cell_exponents.2]
  norm_num

private theorem moore_normalized_triangle_distinguished :
    NormalizedTriangleCompatible background KIP126.AdamsComputation.Moore.triangle
      moore_exponent_sum :=
  KIP126.Literature.Standard.normalized_triangle_distinguished _ _


private theorem suspension_projection_one (Y : AdamsObject (coefficients := background.coefficients)) :
    ((background.classicalSuspension Y).tower 1).hom ≫
        (shiftFunctor Spectrum (1:ℤ)).map
          ((background.classicalTower.tower (Y.obj background.auxiliary)).projection 1) =
      (background.classicalTower.tower ((AdamsObject.shift 1 Y).obj background.auxiliary)).projection 1 := by
  have hcomm := (background.classicalSuspension Y).tower_comm 0 1 (by omega)
  have hzero := (background.classicalSuspension Y).tower_zero
  dsimp only [AbstractAdamsTower.projection,AbstractAdamsTower.mapAt,
    AdamsObject.obj, ClassicalObject.obj,Int.toNat_one,Int.toNat_zero] at *
  rw [Functor.map_comp,←Category.assoc,hcomm,Category.assoc,hzero]

private theorem map_filtration_one_shift_iff (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) :
    MapFiltrationAtLeast background.classicalTower ((shiftFunctor Spectrum (1:ℤ)).map f) 1 ↔
      MapFiltrationAtLeast background.classicalTower f 1 := by
  let S := background.classicalSuspension Y
  let ff := Functor.FullyFaithful.ofFullyFaithful (shiftFunctor Spectrum (1:ℤ))
  constructor
  · rintro ⟨a,ha⟩
    let b := ff.preimage (a≫(S.tower 1).hom)
    refine ⟨b,?_⟩
    apply ff.map_injective
    change (shiftFunctor Spectrum (1:ℤ)).map (b≫_) = _
    rw [Functor.map_comp]
    dsimp only [b]
    rw [Functor.FullyFaithful.map_preimage,Category.assoc]
    erw [suspension_projection_one Y]
    exact ha
  · rintro ⟨a,ha⟩
    refine ⟨(shiftFunctor Spectrum (1:ℤ)).map a≫(S.tower 1).inv,?_⟩
    rw [Category.assoc]
    erw [←suspension_projection_one Y]
    simp only [S,Iso.inv_hom_id_assoc]
    rw [←Functor.map_comp]
    exact congrArg (shiftFunctor Spectrum (1:ℤ)).map ha

private theorem map_filtration_one_neg_iff {X Y : Spectrum} (f : X ⟶ Y) :
    MapFiltrationAtLeast background.classicalTower (-f) 1 ↔
      MapFiltrationAtLeast background.classicalTower f 1 := by
  constructor <;> rintro ⟨a,ha⟩ <;> refine ⟨-a,?_⟩
  · rw [Preadditive.neg_comp,ha,neg_neg]
  · rw [Preadditive.neg_comp,ha]

private theorem normalized_exponent_neg_shift (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) :
    normalizedExponent background.classicalTower (-((shiftFunctor Spectrum (1:ℤ)).map f)) =
      normalizedExponent background.classicalTower f := by
  classical
  unfold normalizedExponent
  rw [map_filtration_one_neg_iff,map_filtration_one_shift_iff]


private def mooreTwiceRotatedTriangle : TriangleData background.auxiliary where
  X := KIP126.AdamsComputation.Moore.adamsObject
  Y := .shift 1 .sphere
  Z := .shift 1 .sphere
  f := KIP126.AdamsComputation.Moore.top
  g := -((shiftFunctor Spectrum (1:ℤ)).map twoMap)
  h := -((shiftFunctor Spectrum (1:ℤ)).map KIP126.AdamsComputation.Moore.bottom)
  distinguished := rot_of_distTriang _
    (rot_of_distTriang _ KIP126.AdamsComputation.Moore.triangle.distinguished)

private theorem moore_twice_rotated_exponent_sum :
    (normalizedExponent background.classicalTower mooreTwiceRotatedTriangle.f : ℤ) +
      normalizedExponent background.classicalTower mooreTwiceRotatedTriangle.g +
      normalizedExponent background.classicalTower mooreTwiceRotatedTriangle.h = 1 := by
  change (normalizedExponent background.classicalTower KIP126.AdamsComputation.Moore.top : ℤ) +
    normalizedExponent background.classicalTower (-((shiftFunctor Spectrum (1:ℤ)).map twoMap)) +
    normalizedExponent background.classicalTower
      (-((shiftFunctor Spectrum (1:ℤ)).map KIP126.AdamsComputation.Moore.bottom)) = 1
  rw [normalized_exponent_neg_shift .sphere .sphere twoMap,
    normalized_exponent_neg_shift .sphere KIP126.AdamsComputation.Moore.adamsObject
      KIP126.AdamsComputation.Moore.bottom,
    twoMap_exponent, moore_cell_exponents.1, moore_cell_exponents.2]
  norm_num

private abbrev mooreMayTriangle :=
  normalizedTriangle background mooreTwiceRotatedTriangle moore_twice_rotated_exponent_sum

private def mooreMaySuspensionIso :
    XModLambdaN (mooreMayTriangle.obj₂⟦(1:ℤ)⟧) 2 ≅
      (XModLambdaN mooreMayTriangle.obj₂ 2)⟦(1:ℤ)⟧ :=
  (KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    mooreTwiceRotatedTriangle moore_twice_rotated_exponent_sum 2 (by decide)).choose

private theorem moore_may_suspension_inclusion :
    XModLambdaN.incl (mooreMayTriangle.obj₂⟦(1:ℤ)⟧) 2 ≫ mooreMaySuspensionIso.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl mooreMayTriangle.obj₂ 2) :=
  (KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    mooreTwiceRotatedTriangle moore_twice_rotated_exponent_sum 2 (by decide)).choose_spec.1

/-- The signed common lift on the actual twice-rotated Moore triangle.
The input is the precise first-quotient boundary equality; its two output
identities concern one and the same lift. -/
private theorem moore_first_common_lift
    (a : BiHom 125 132 (XModLambdaN mooreMayTriangle.obj₃ 1))
    (b : BiHom 125 132 (((SyntheticCategory.biShift (0,-(1:ℤ))).obj
      (XModLambdaN mooreMayTriangle.obj₂ 1))⟦(1:ℤ)⟧))
    (hab : a ≫ ((background.quotients.tower mooreMayTriangle.obj₃).triangle
        (by decide : 0<1) (by decide : 1<2)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(1:ℤ))).map
          (XModLambdaN.map mooreMayTriangle.mor₂ 1))) :
    ∃ c : BiHom 125 132 (XModLambdaN (mooreMayTriangle.obj₁⟦(1:ℤ)⟧) 2),
      c ≫ (background.quotients.tower (mooreMayTriangle.obj₁⟦(1:ℤ)⟧)).rho
        1 2 (by decide) = a ≫ XModLambdaN.map mooreMayTriangle.mor₃ 1 ∧
      c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        mooreMayTriangle.mor₁) 2 ≫ mooreMaySuspensionIso.hom =
        -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((background.quotients.tower mooreMayTriangle.obj₂).triangle
            (by decide : 0<1) (by decide : 1<2)).lambdaMap) := by
  exact KIP126.ProofTools.Internal.Mahowald.finite_may_at_normalized_triangle_explicit_lengths
    mooreTwiceRotatedTriangle moore_twice_rotated_exponent_sum
    (KIP126.Literature.Standard.normalized_triangle_distinguished _ _)
    1 1 (by decide) (by decide) 125 132
    mooreMaySuspensionIso moore_may_suspension_inclusion a b hab

private theorem moore_detects_exists_of_infinity
    {X : SyntheticSpectrum} (c : SyntheticTowerConvergence background.syntheticTower X)
    (i : Tridegree) (x : (background.family.obj X).E₂ i)
    (e : ((background.family.obj X).sequence.ssData i).eInfty)
    (hx : HasInfinityRepresentative (background.family.obj X) 2 i x e) :
    ∃ a : BiHom (i.2.1-i.1) i.2.2 X, Detects c i x a := by
  classical
  let F := background.syntheticTower.filtration X
  haveI : Epi (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2)) :=
    inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨a,ha⟩ :=
    (ModuleCat.epi_iff_surjective (F.toAssociatedGraded i.1 (i.2.1-i.1,i.2.2))).mp
      inferInstance ((c.identification i).hom e)
  exact ⟨(F.F i.1 (i.2.1-i.1,i.2.2)).arrow a,e,hx,a,rfl,ha.symm⟩

/-- The actual fourth-quotient representative of a Moore class reaching E₅.
The numerical zero differentials must supply the cycle premise. -/
private theorem moore_fourth_source_representative
    (x : KIP126.AdamsComputation.Moore.Page 8 132)
    (hx : x ∈ cycles background KIP126.AdamsComputation.Moore.adamsObject 4 (8,132)) :
    ∃ c : BiHom 124 132
        (XModLambdaN (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4),
      Detects (background.convergence
        (.quotient 4 (.nu KIP126.AdamsComputation.Moore.adamsObject))) (8,132,132)
        (finiteTargetLabel background KIP126.AdamsComputation.Moore.adamsObject 4 8 132 0 x) c := by
  let X := KIP126.AdamsComputation.Moore.adamsObject
  let P := KIP126.Literature.Standard.infinityFiniteWindow X 4 (by decide)
    (8,132) 132 (by constructor <;> decide)
  let y : cycles background X (4-132+132) (8,132) := ⟨x,by simpa using hx⟩
  let e := P.symm (subquotientClass _ _ y)
  have he : HasInfinityRepresentative
      (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) 4)
      2 (8,132,132) (finiteTargetLabel background X 4 8 132 0 x) e := by
    apply (KIP126.ProofTools.Internal.Mahowald.finite_target_label_iff
      X 4 (by decide) 8 132 0 (by decide) y e).mpr
    exact P.apply_symm_apply _
  exact moore_detects_exists_of_infinity (background.convergence (.quotient 4 (.nu X)))
    (8,132,132) _ e he

end
end KIP126.Main.Internal.Moore
end
