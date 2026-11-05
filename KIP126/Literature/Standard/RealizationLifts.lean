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

/-! Realization and λ lifts for every object in the Adams range, using the
fixed literature background. -/

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

public def realizeNu := realizeNuZero background realizationData

section SelectedFiltrationLambdaConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000


section General
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X : Syn}

private theorem selectedFiltration_filtration_at_zero (P : SyntheticTowerPresentation unit F)
    (X : Syn) (m w : ℤ) (a : BiHom m w X) : FiltrationAtLeast P 0 a := by
  refine ⟨a ≫ (P.tower X).zeroIso.inv, ?_⟩
  change (a ≫ (P.tower X).zeroIso.inv) ≫ (P.tower X).projection 0 = a
  simp only [AbstractAdamsTower.projection, Int.toNat_zero, (P.tower X).map_self]
  erw [Category.assoc, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

private theorem selectedFiltration_filtration_iff_of_infinity_zero (c : SyntheticTowerConvergence P X)
    (s t m w : ℤ) (hst : s ≤ t)
    (hz : ∀ j, s ≤ j → j < t → IsZero (((F.obj X).sequence.ssData (j,m+j,w)).eInfty))
    (a : BiHom m w X) : FiltrationAtLeast P s a ↔ FiltrationAtLeast P t a := by
  have hgraded (j : ℤ) (hj : s ≤ j) (hjt : j < t) :
      IsZero ((P.filtration X).associatedGraded j (m,w)) :=
    (hz j hj hjt).of_iso (towerGradedIso c (m,w) j).symm
  have he := (P.filtration X).eq_of_associatedGraded_isZero s t (m,w) hst hgraded
  have he' := congrArg (fun Q => a ∈ (ModuleCat.subobjectModule (syntheticHomotopy X (m,w))) Q) he
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply,
    FiltrationAtLeast] using Iff.of_eq he'
end General

private theorem selectedFiltration_finite_infinity_zero_outside (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (s t w : ℤ) (hw : ¬ (0 ≤ t-w ∧ t-w < q)) :
    IsZero (((background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData
      (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.finiteEInftyModel background X q (s,t) w) := by
    delta KIP126.Literature.finiteEInftyModel; simp only [hw, ite_false]
    infer_instance
  haveI : Subsingleton (((background.family.quotient
      (background.nu.functor.obj (X.obj background.auxiliary)) q).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_finite X q hq (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem selectedFiltration_finite_high_filtration_zero (X : AdamsObject) (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : FiltrationAtLeast background.syntheticTower s a) : a = 0 := by
  apply KIP126.AdamsSynthetic.Completed.synthetic_homotopy_separated (.nu X) q m w a
  intro j
  by_cases hj : s ≤ (j:ℤ)
  · exact (selectedFiltration_filtration_iff_of_infinity_zero (background.convergence (.quotient q (.nu X)))
      s j m w hj (fun k hk _ => selectedFiltration_finite_infinity_zero_outside X q hq k (m+k) w (by omega)) a).mp ha
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha


-- Definition calculation, as in the existing Coherence.lambda_regrade_eq.
private theorem selectedFiltration_regrade_lambda (m u : ℤ) (k : ℕ) (w : ℤ) (h : u-k=w)
    (A : SyntheticSpectrum) (b : BiHom m u A) :
    homotopyRegrade rfl h (lambdaMultiply k b) =
      (biShiftAddIso (m,u) (0,-(k:ℤ)) (m,w) (by ext <;> dsimp <;> omega)).inv.app S_0_0 ≫
        lambdaPow k (Smn m u) ≫ b := by
  subst w
  delta KIP126.Synthetic.Context.homotopyRegrade KIP126.Synthetic.Context.lambdaMultiply
  simp only [biShiftAddIso, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, Category.assoc]

private theorem selectedFiltration_lambda_filtration {A : SyntheticSpectrum} {m w : ℤ}
    (k : ℕ) (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (lambdaMultiply k a) := by
  obtain ⟨z,hz⟩ := ha
  refine ⟨lambdaMultiply k z,?_⟩
  change lambdaMultiply k z ≫ (background.syntheticTower.tower A).projection s = _
  change z ≫ (background.syntheticTower.tower A).projection s = a at hz
  delta KIP126.Synthetic.Context.lambdaMultiply
  simp only [Category.assoc,hz]

private theorem selectedFiltration_regrade_filtration {A : SyntheticSpectrum} {m m' w w' : ℤ}
    (hm : m=m') (hw : w=w') (s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (homotopyRegrade hm hw a) := by
  subst m'; subst w'; exact ha

private theorem selectedFiltration_map_filtration {A B : SyntheticSpectrum} (f : A ⟶ B)
    (m w s : ℤ) (a : BiHom m w A)
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (a ≫ f) := by
  obtain ⟨z,hz⟩ := ha
  let φ := background.syntheticTower.map f
  refine ⟨z ≫ φ.stage s.toNat, ?_⟩
  change (z ≫ φ.stage s.toNat) ≫ (background.syntheticTower.tower B).projection s = a ≫ f
  change z ≫ (background.syntheticTower.tower A).projection s = a at hz
  rw [Category.assoc, TowerMap.projection, ←Category.assoc, hz]

private theorem selectedFiltration_nu_above_zero (X : AdamsObject) (s t w : ℤ) (hw : t<w) :
    IsZero (((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w)).eInfty) := by
  haveI : Subsingleton (nuEInftyModel background X (s,t) w) := by
    delta KIP126.Literature.nuEInftyModel; simp only [not_le.mpr hw, ite_false]
    infer_instance
  haveI : Subsingleton (((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_nu X (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem selectedFiltration_nu_bottom (X : AdamsObject) (m s : ℤ)
    (b : BiHom m (m+s) (background.nu.functor.obj (X.obj background.auxiliary))) :
    FiltrationAtLeast background.syntheticTower s b := by
  have hb0 := selectedFiltration_filtration_at_zero background.syntheticTower _ m (m+s) b
  by_cases hs : s ≤ 0
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (m,m+s) hs hb0
  · exact (selectedFiltration_filtration_iff_of_infinity_zero (background.convergence (.nu X))
      0 s m (m+s) (by omega)
      (fun j _ hj => selectedFiltration_nu_above_zero X j (m+j) (m+s) (by omega)) b).mp hb0

private theorem selectedFiltration_divide_of_quotient_zero (X : AdamsObject) (m u w : ℤ)
    (k : ℕ) (h : u-k=w)
    (a : BiHom m w (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : quotientClass k a=0) :
    ∃ b : BiHom m u (background.nu.functor.obj (X.obj background.auxiliary)),
      homotopyRegrade rfl h (lambdaMultiply k b)=a := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  obtain ⟨c,hc⟩ := (XModLambdaN.cofiberTriangle A k).coyoneda_exact₂
    (XModLambdaN.cofiberTriangle_distinguished A k) a ha
  change a = c ≫ lambdaPow k A at hc
  let e := (biShiftAddIso (m,u) (0,-(k:ℤ)) (m,w) (by ext <;> dsimp <;> omega)).app
    (S_0_0:SyntheticSpectrum)
  obtain ⟨b,hb⟩ := (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum)
    (0,-(k:ℤ))).homEquiv.surjective (e.hom ≫ c)
  change (SyntheticCategory.biShift (0,-(k:ℤ))).map b = e.hom ≫ c at hb
  refine ⟨b,?_⟩
  rw [selectedFiltration_regrade_lambda]
  change e.inv ≫ lambdaPow k (Smn m u) ≫ b = a
  rw [←lambdaPow_naturality, hb]
  simpa only [Category.assoc,e.inv_hom_id_assoc] using hc.symm

/-- Finite quotient vanishing and exactness identify filtration with the actual λ divisibility. -/
public theorem filtration_lambda :
    ∀ X : AdamsObject, FiltrationLambdaAt background X := by
  intro X m w s h a
  let k := (m+s-w).toNat
  have hk : (k:ℤ)=m+s-w := Int.toNat_of_nonneg (by omega)
  constructor
  · intro ha
    by_cases hk0 : k=0
    · have hz : quotientClass k a=0 := by
        rw [hk0]
        let A := background.nu.functor.obj (X.obj background.auxiliary)
        letI : IsIso (lambdaPow 0 A) := by
          change IsIso (SyntheticCategory.biShift_zero.hom.app A)
          infer_instance
        have hi : XModLambdaN.incl A 0 = 0 := by
          apply (cancel_epi (lambdaPow 0 A)).mp
          simpa only [comp_zero] using XModLambdaN.lambdaPow_comp_incl A 0
        exact (congrArg (fun f => a ≫ f) hi).trans (comp_zero)
      exact selectedFiltration_divide_of_quotient_zero X m (m+s) w k (by omega) a hz
    · have hq : 0<k := Nat.pos_of_ne_zero hk0
      have himage : FiltrationAtLeast background.syntheticTower s (quotientClass k a) :=
        selectedFiltration_map_filtration (XModLambdaN.incl _ k) m w s a ha
      have hz : quotientClass k a=0 :=
        selectedFiltration_finite_high_filtration_zero X k hq m w s (by omega) _ himage
      exact selectedFiltration_divide_of_quotient_zero X m (m+s) w k (by omega) a hz
  · rintro ⟨b,hb⟩
    rw [←hb]
    exact selectedFiltration_regrade_filtration rfl (by omega) s _ (selectedFiltration_lambda_filtration k s b (selectedFiltration_nu_bottom X m s b))


end SelectedFiltrationLambdaConstruction


/- Filtered detection and lambda transport. -/


namespace SelectedLifetimeConstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 6000000
private theorem family_infinity_representative_map {X Y : SyntheticSpectrum}
    (g : X ⟶ Y) (i : Tridegree) (x : (background.family.obj X).Page 2 i)
    (e : ((background.family.obj X).sequence.ssData i).eInfty)
    (h : HasInfinityRepresentative (background.family.obj X) 2 i x e) :
    HasInfinityRepresentative (background.family.obj Y) 2 i
      (background.family.pageMap g 2 i x) ((background.family.map g).eInftyMap i e) :=
  KIP126.Literature.Standard.rhoInfinityRepresentativeMap g i h
private theorem family_page_comp {X Y Z : SyntheticSpectrum}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℤ) (i : Tridegree) :
    familyPageMap background.family f r i ≫ familyPageMap background.family g r i =
      familyPageMap background.family (f ≫ g) r i := by
  change (background.family.map f).pageMap r i ≫ (background.family.map g).pageMap r i = _
  rw [← SpectralSequenceMorphism.pageMap_comp, ← SyntheticAdamsFamily.map_comp]
  rfl
private theorem graded_map_representative {ι : Type} {A B : ι → ModuleCat.{0} ℤ}
    {F : Filtration A} {G : Filtration B} (f : FilteredMorphism F G) (s : ℤ) (i : ι)
    (a : (Subobject.underlying.obj (F.F s i) : ModuleCat ℤ)) :
    f.inducedGrMap s i (F.toAssociatedGraded s i a) =
      G.toAssociatedGraded s i ((f.compat s i).choose a) := by
  have h : F.toAssociatedGraded s i ≫ f.inducedGrMap s i =
      (f.compat s i).choose ≫ G.toAssociatedGraded s i := by
    unfold Filtration.toAssociatedGraded FilteredMorphism.inducedGrMap
      Filtration.inducedAssocGradedMap
    dsimp only [cokernel.map]
    exact cokernel.π_desc _ _ _
  exact ConcreteCategory.congr_hom h a
private theorem filtration_representative_exists (A : SyntheticSpectrum) (p : ℤ × ℤ)
    (s : ℤ) (a : BiHom p.1 p.2 A)
    (ha : a ∈ background.syntheticTower.filtrationSubmodule A s p) :
    ∃ a' : (Subobject.underlying.obj ((background.syntheticTower.filtration A).F s p) : ModuleCat ℤ),
      ((background.syntheticTower.filtration A).F s p).arrow a' = a := by
  have hm : a ∈ ModuleCat.subobjectModule _ ((background.syntheticTower.filtration A).F s p) := by
    change a ∈ (ModuleCat.subobjectModule (syntheticHomotopy A p))
      ((ModuleCat.subobjectModule (syntheticHomotopy A p)).symm
        (background.syntheticTower.filtrationSubmodule A s p))
    simpa only [OrderIso.apply_symm_apply] using ha
  exact hm
private theorem grade_natural (A B : SyntheticObject)
    (f : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary) (i : Tridegree)
    (a : (Subobject.underlying.obj ((background.syntheticTower.filtration
      (A.obj background.nu background.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (b : (Subobject.underlying.obj ((background.syntheticTower.filtration
      (B.obj background.nu background.auxiliary)).F i.1 (i.2.1-i.1,i.2.2)) : ModuleCat ℤ))
    (hab : ((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow a ≫ f =
      ((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow b) :
    ((background.convergence B).identification i).inv
      ((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b) =
      (background.family.map f).eInftyMap i (((background.convergence A).identification i).inv
        ((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).toAssociatedGraded
          i.1 (i.2.1-i.1,i.2.2) a)) := by
  let M := background.convergentMap A B f
  let FA := background.syntheticTower.filtration (A.obj background.nu background.auxiliary)
  let FB := background.syntheticTower.filtration (B.obj background.nu background.auxiliary)
  let p := (i.2.1-i.1,i.2.2)
  have hb : (M.filteredMap.compat i.1 p).choose a = b := by
    apply (ModuleCat.mono_iff_injective (FB.F i.1 p).arrow).mp inferInstance
    have h := ConcreteCategory.congr_hom (M.filteredMap.compat i.1 p).choose_spec a
    change (FB.F i.1 p).arrow ((M.filteredMap.compat i.1 p).choose a) =
      M.filteredMap.map p ((FA.F i.1 p).arrow a) at h
    have hm := ConcreteCategory.congr_hom (M.filteredMap_map p) ((FA.F i.1 p).arrow a)
    change M.filteredMap.map p ((FA.F i.1 p).arrow a) = (FA.F i.1 p).arrow a ≫ f at hm
    exact h.trans (hm.trans hab)
  have hp := graded_map_representative M.filteredMap i.1 p a
  rw [hb] at hp
  apply ((background.convergence B).identification i).toLinearEquiv.injective
  have hn := ConcreteCategory.congr_hom (M.infinity_action_graded i)
    (((background.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))
  change M.filteredMap.inducedGrMap i.1 p
      (((background.convergence A).identification i).hom
        (((background.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))) =
    ((background.convergence B).identification i).hom
      ((background.family.map f).eInftyMap i
        (((background.convergence A).identification i).inv (FA.toAssociatedGraded i.1 p a))) at hn
  have hA := ((background.convergence A).identification i).toLinearEquiv.apply_symm_apply
    (FA.toAssociatedGraded i.1 p a)
  have hB := ((background.convergence B).identification i).toLinearEquiv.apply_symm_apply
    (FB.toAssociatedGraded i.1 p b)
  exact hB.trans (hp.symm.trans
    ((congrArg (M.filteredMap.inducedGrMap i.1 p) hA.symm).trans hn))

private theorem detects_map (A B : SyntheticObject)
    (f : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary) (i : Tridegree)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence A) i x a) :
    Detects (background.convergence B) i (familyPageMap background.family f 2 i x) (a ≫ f) := by
  obtain ⟨e,he,a',ha',hga⟩ := ha
  let M := background.convergentMap A B f
  let b := (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose a'
  have hb : ((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).F
      i.1 (i.2.1-i.1,i.2.2)).arrow b = a ≫ f := by
    have h := ConcreteCategory.congr_hom
      (M.filteredMap.compat i.1 (i.2.1-i.1,i.2.2)).choose_spec a'
    change _ = M.filteredMap.map (i.2.1-i.1,i.2.2) _ at h
    have hm := ConcreteCategory.congr_hom (M.filteredMap_map (i.2.1-i.1,i.2.2))
      (((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F
        i.1 (i.2.1-i.1,i.2.2)).arrow a')
    change _ = _ ≫ f at hm
    exact h.trans (hm.trans (congrArg (fun z => z ≫ f) ha'))
  refine ⟨_,family_infinity_representative_map f i x e he,b,hb,?_⟩
  have h := grade_natural A B f i a' b (by rw [ha',hb])
  have haE : ((background.convergence A).identification i).inv
      ((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) a') = e := by
    rw [← hga]
    exact ((background.convergence A).identification i).toLinearEquiv.symm_apply_apply e
  rw [haE] at h
  exact (congrArg ((background.convergence B).identification i).hom h).symm.trans
    (((background.convergence B).identification i).toLinearEquiv.apply_symm_apply _)

private theorem detects_reflect (A B : SyntheticObject)
    (f : A.obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary) (i : Tridegree)
    (hf : Function.Injective ((background.family.map f).eInftyMap i).hom)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ i)
    (e : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative _ 2 i x e)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower i.1 a)
    (hb : Detects (background.convergence B) i (familyPageMap background.family f 2 i x) (a ≫ f)) :
    Detects (background.convergence A) i x a := by
  obtain ⟨a',ha'⟩ := filtration_representative_exists
    (A.obj background.nu background.auxiliary) (i.2.1-i.1,i.2.2) i.1 a ha
  obtain ⟨eB,heB,b,hb,hgb⟩ := hb
  have huniq := heB.unique (family_infinity_representative_map f i x e he)
  have h := grade_natural A B f i a' b (by rw [ha',hb])
  have hB : ((background.convergence B).identification i).inv
      ((background.syntheticTower.filtration (B.obj background.nu background.auxiliary)).toAssociatedGraded
        i.1 (i.2.1-i.1,i.2.2) b) = (background.family.map f).eInftyMap i e := by
    rw [← hgb]
    exact (((background.convergence B).identification i).toLinearEquiv.symm_apply_apply eB).trans huniq
  have hA := hf (h.symm.trans hB)
  refine ⟨e,he,a',ha',?_⟩
  exact (congrArg ((background.convergence A).identification i).hom hA).symm.trans
    (((background.convergence A).identification i).toLinearEquiv.apply_symm_apply _)

section Frames
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- A filtration frame, reindexed by the same stem, gives detection. -/
theorem source_frame_detects (cx : SyntheticTowerConvergence P X)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (x0 : (F.obj X).E₂ (s,p.1+s,p.2))
    (hx : HasInfinityRepresentative _ 2 _ x0 x)
    (a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ))
    (ha : (P.filtration X).toAssociatedGraded s p a = (towerGradedIso cx p s).hom x) :
    Detects cx (s,p.1+s,p.2) x0
      (homotopyRegrade (by dsimp; omega) rfl (((P.filtration X).F s p).arrow a)) := by
  have lift_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
      (I : V ≅ (P.filtration X).associatedGraded s (m',w))
      (a : (Subobject.underlying.obj ((P.filtration X).F s (m,w)) : ModuleCat.{v} ℤ))
      (ha : (P.filtration X).toAssociatedGraded s (m,w) a =
        (I ≪≫ eqToIso (congrArg
          (fun z => (P.filtration X).associatedGraded s (z,w)) hm.symm)).hom e) :
      ∃ a' : (Subobject.underlying.obj ((P.filtration X).F s (m',w)) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s (m',w)).arrow a' =
          homotopyRegrade hm rfl (((P.filtration X).F s (m,w)).arrow a) ∧
        I.hom e = (P.filtration X).toAssociatedGraded s (m',w) a' := by
    subst m'
    refine ⟨a,rfl,?_⟩
    simpa only [eqToIso_refl, Iso.trans_refl] using ha.symm
  obtain ⟨a',ha',hga⟩ := lift_frame p.1 ((p.1+s)-s) p.2 s (by omega) x
    (cx.identification (s,p.1+s,p.2)) a ha
  exact ⟨x,hx,a',ha',hga⟩

/-- Detection supplies a frame in the original stem coordinates. -/
theorem frame_of_source_detects (cx : SyntheticTowerConvergence P X)
    (p : ℤ × ℤ) (s : ℤ) (x0 : (F.obj X).E₂ (s,p.1+s,p.2))
    (a0 : BiHom p.1 p.2 X)
    (ha0 : Detects cx (s,p.1+s,p.2) x0 (homotopyRegrade (by dsimp; omega) rfl a0)) :
    ∃ x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty,
      HasInfinityRepresentative _ 2 _ x0 x ∧
      ∃ a : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s p).arrow a = a0 ∧
        (P.filtration X).toAssociatedGraded s p a = (towerGradedIso cx p s).hom x := by
  have lower_frame (m m' w s : ℤ) (hm : m=m') {V : ModuleCat.{v} ℤ} (e : V)
      (I : V ≅ (P.filtration X).associatedGraded s (m',w))
      (a0 : BiHom m w X)
      (a' : (Subobject.underlying.obj ((P.filtration X).F s (m',w)) : ModuleCat.{v} ℤ))
      (ha' : ((P.filtration X).F s (m',w)).arrow a' = homotopyRegrade hm rfl a0)
      (hga : I.hom e = (P.filtration X).toAssociatedGraded s (m',w) a') :
      ∃ a : (Subobject.underlying.obj ((P.filtration X).F s (m,w)) : ModuleCat.{v} ℤ),
        ((P.filtration X).F s (m,w)).arrow a = a0 ∧
        (P.filtration X).toAssociatedGraded s (m,w) a =
          (I ≪≫ eqToIso (congrArg
            (fun z => (P.filtration X).associatedGraded s (z,w)) hm.symm)).hom e := by
    subst m'
    exact ⟨a',ha',hga.symm⟩
  obtain ⟨e,he,a',ha',hga⟩ := ha0
  obtain ⟨a,ha,hg⟩ := lower_frame p.1 ((p.1+s)-s) p.2 s (by omega) e
    (cx.identification (s,p.1+s,p.2)) a0 a' ha' hga
  exact ⟨e,he,a,ha,hg⟩

end Frames
private theorem shift_frame (A : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (e : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (a : (Subobject.underlying.obj ((background.syntheticTower.filtration
      (A.obj background.nu background.auxiliary)).F s p) : ModuleCat ℤ))
    (ha : (background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).toAssociatedGraded s p a =
      (towerGradedIso (background.convergence A) p s).hom e) :
    ∃ b : (Subobject.underlying.obj ((background.syntheticTower.filtration
      ((SyntheticObject.shift δ A).obj background.nu background.auxiliary)).F s (p+δ)) : ModuleCat ℤ),
      ((background.syntheticTower.filtration ((SyntheticObject.shift δ A).obj background.nu background.auxiliary)).F
        s (p+δ)).arrow b = shiftHomotopyClass δ p
          (((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F s p).arrow a) ∧
      (background.syntheticTower.filtration ((SyntheticObject.shift δ A).obj background.nu background.auxiliary)).toAssociatedGraded
        s (p+δ) b = (towerGradedIso (background.convergence (.shift δ A)) (p+δ) s).hom
          ((towerInfinityIso (background.convergence A) (background.convergence (.shift δ A))
            ((essShift δ).filtered A p) s).hom e) := by
  let S := (essShift δ).filtered A p
  refine ⟨(S.level s).hom a,?_,?_⟩
  · exact (ConcreteCategory.congr_hom (S.level_arrow s) a).trans
      ((essShift δ).ambient_eq A p _)
  · have h := ConcreteCategory.congr_hom (S.projection_comm s) a
    simp only [ModuleCat.comp_apply] at h
    rw [ha] at h
    rw [←h]
    change (S.gradedIso s).hom ((towerGradedIso (background.convergence A) p s).hom e) =
      (towerGradedIso (background.convergence (.shift δ A)) (p+δ) s).hom
        ((towerInfinityIso (background.convergence A) (background.convergence (.shift δ A)) S s).hom e)
    simp only [towerInfinityIso, Iso.trans_hom, Iso.symm_hom, ←ModuleCat.comp_apply,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem detects_shift (A : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ (s,p.1+s,p.2))
    (a : BiHom p.1 p.2 (A.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence A) (s,p.1+s,p.2) x
      (homotopyRegrade (by dsimp; omega) rfl a)) :
    Detects (background.convergence (.shift δ A)) (s,(p+δ).1+s,(p+δ).2)
      (((essShift δ).page A 2 (by decide) p s).hom x)
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a)) := by
  obtain ⟨e,he,a',ha',hga⟩ := frame_of_source_detects (background.convergence A) p s x a ha
  obtain ⟨b,hb,hgb⟩ := shift_frame A δ p s e a' hga
  have hdet := source_frame_detects (background.convergence (.shift δ A)) (p+δ) s _ _
    ((essShift δ).representative_iff A 2 (by decide) p s x e |>.mp he) b
    hgb
  rw [hb,ha'] at hdet
  exact hdet

private theorem regrade_comp {m m' w w' : ℤ} {A B : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) (f : A ⟶ B) :
    homotopyRegrade hm hw (a≫f) = homotopyRegrade hm hw a ≫ f := by
  subst m'; subst w'; rfl

private theorem shifted_map_detects (A B : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (g : (SyntheticObject.shift δ A).obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ (s,p.1+s,p.2))
    (a : BiHom p.1 p.2 (A.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence A) (s,p.1+s,p.2) x (homotopyRegrade (by dsimp; omega) rfl a)) :
    Detects (background.convergence B) (s,(p+δ).1+s,(p+δ).2)
      (familyPageMap background.family g 2 (s,(p+δ).1+s,(p+δ).2)
        (((essShift δ).page A 2 (by decide) p s).hom x))
      (homotopyRegrade (by dsimp; omega) rfl (shiftHomotopyClass δ p a) ≫ g) :=
  detects_map (.shift δ A) B g (s,(p+δ).1+s,(p+δ).2) _ _
    (detects_shift A δ p s x a ha)

private theorem shifted_representative_map (A B : SyntheticObject) (δ p : ℤ × ℤ) (s : ℤ)
    (g : (SyntheticObject.shift δ A).obj background.nu background.auxiliary ⟶ B.obj background.nu background.auxiliary)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ (s,p.1+s,p.2))
    (e : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,p.1+s,p.2) x e) :
    HasInfinityRepresentative _ 2 (s,(p+δ).1+s,(p+δ).2)
      (familyPageMap background.family g 2 (s,(p+δ).1+s,(p+δ).2)
        (((essShift δ).page A 2 (by decide) p s).hom x))
      ((background.family.map g).eInftyMap (s,(p+δ).1+s,(p+δ).2)
        ((towerInfinityIso (background.convergence A) (background.convergence (.shift δ A))
          ((essShift δ).filtered A p) s).hom e)) :=
  family_infinity_representative_map g (s,(p+δ).1+s,(p+δ).2) _ _
    (((essShift δ).representative_iff A 2 (by decide) p s x e).mp he)

private theorem detects_transport {A : SyntheticObject} {i j : Tridegree} (h : i=j)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ i)
    (a : BiHom (i.2.1-i.1) i.2.2 (A.obj background.nu background.auxiliary))
    (ha : Detects (background.convergence A) i x a) :
    Detects (background.convergence A) j (regradeE2 h x)
      (homotopyRegrade (congrArg (fun k : Tridegree => k.2.1-k.1) h)
        (congrArg (fun k : Tridegree => k.2.2) h) a) := by
  subst j
  exact ha

private theorem representative_transport {A : SyntheticAdamsSS.{0}} {i j : Tridegree} (h : i=j)
    (x : A.E₂ i) (e : (A.sequence.ssData i).eInfty)
    (he : HasInfinityRepresentative A 2 i x e) :
    HasInfinityRepresentative A 2 j (regradeE2 h x)
      ((eqToHom (congrArg (fun k => (A.sequence.ssData k).eInfty) h)) e) := by
  subst j
  exact he

private theorem map_regrade {A B : SyntheticSpectrum} (f : A ⟶ B) {i j : Tridegree} (h : i=j)
    (x : (background.family.obj A).E₂ i) :
    familyPageMap background.family f 2 j (regradeE2 h x) =
      regradeE2 h (familyPageMap background.family f 2 i x) := by
  subst j
  rfl

private theorem zero_weight_label (X : AdamsObject) (q : ℕ) (s t : ℤ) (y : ((background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))) :
    (background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap 2 (s,t,t)
      (nuWeightLabel background X s t t (by omega) y) =
    regradeE2 (by simp) (finiteTargetLabel background X q s t 0 y) := by
  unfold nuWeightLabel
  have transport (j : ℕ) (hj : j=0) (h : (s,t,t-j)=(s,t,t)) :
      familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (regradeE2 h (targetNuLabel background X s t j y)) =
      regradeE2 (by simp) (finiteTargetLabel background X q s t 0 y) := by
    subst j
    exact map_regrade _ h _
  exact transport _ (by omega) _

private theorem infinity_map_regrade {A B : SyntheticSpectrum} (f : A ⟶ B) {i j : Tridegree} (h : i=j)
    (x : ((background.family.obj A).sequence.ssData i).eInfty) :
    ((eqToHom (congrArg (fun k => ((background.family.obj B).sequence.ssData k).eInfty) h)))
      ((background.family.map f).eInftyMap i x) =
    (background.family.map f).eInftyMap j
      ((eqToHom (congrArg (fun k => ((background.family.obj A).sequence.ssData k).eInfty) h)) x) := by
  subst j
  rfl

private theorem regrade_precomp {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) :
    homotopyRegrade hm hw a =
      eqToHom (congrArg (fun p : ℤ × ℤ => Smn p.1 p.2 (Syn := SyntheticSpectrum))
        (show (m',w')=(m,w) by rw [hm,hw])) ≫ a := by
  subst m'; subst w'
  change a = 𝟙 _ ≫ a
  simp only [Category.id_comp]

private theorem first_label_detects_unshifted
    (X : AdamsObject) (s t : ℤ) (x : ((background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (ha : a = KIP126.Literature.firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X 1 s t 0 x)) a := by
  let Z := background.nu.functor.obj (X.obj background.auxiliary)
  let f : KIP126.Literature.nuZero background X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  have h0 : (s,t,t+0-(0:ℕ))=(s,t,t) := by simp
  let x0 : (background.family.obj (KIP126.Literature.nuZero background X)).E₂ (s,t,t) :=
    (congrArg (fun i => ((background.family.obj (KIP126.Literature.nuZero background X)).E₂ i : Type)) h0).mp
      (background.comparison.nuE2 X 0 s t 0 x)
  let xq0 (n : ℕ) := familyPageMap background.family (XModLambdaN.incl (KIP126.Literature.nuZero background X) n) 2 (s,t,t) x0
  let xq (n : ℕ) := familyPageMap background.family (XModLambdaN.incl Z n) 2 (s,t,t)
    (familyPageMap background.family f 2 (s,t,t) x0)
  have map_label (n : ℕ) :
      familyPageMap background.family (XModLambdaN.map f n) 2 (s,t,t) (xq0 n) = xq n := by
    dsimp only [xq0,xq]
    rw [←ModuleCat.comp_apply,family_page_comp,←XModLambdaN.incl_naturality]
    rw [←family_page_comp,ModuleCat.comp_apply]
  have map_cast {A B : SyntheticSpectrum} (g : A ⟶ B) {i j : Tridegree} (h : i=j)
      (x : (background.family.obj A).E₂ i) :
      (congrArg (fun k => ((background.family.obj B).E₂ k : Type)) h).mp
        (familyPageMap background.family g 2 i x) =
      familyPageMap background.family g 2 j
        ((congrArg (fun k => ((background.family.obj A).E₂ k : Type)) h).mp x) := by
    subst j
    rfl
  have hb0 : Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X))))
      (s,t,t) (xq0 1) (KIP126.Literature.firstLabel background X s t x) := by
    have transport_detects {A : SyntheticObject} {i j : Tridegree} (h : i=j)
        (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ i)
        (a : BiHom (i.2.1-i.1) i.2.2 (A.obj background.nu background.auxiliary))
        (ha : Detects (background.convergence A) i x a) :
        Detects (background.convergence A) j
          ((congrArg (fun k => ((background.family.obj (A.obj background.nu background.auxiliary)).E₂ k : Type)) h).mp x)
          ((congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2 (A.obj background.nu background.auxiliary)) h).mp a) := by
      subst j
      exact ha
    have h1 : (s,t,t+0)=(s,t,t) := by simp
    have h01 : (s,t,t+0-(0:ℕ))=(s,t,t+0) := by simp only [Nat.cast_zero,sub_zero]
    let x1 : (background.family.obj (KIP126.Literature.nuZero background X)).E₂ (s,t,t+0) :=
      (congrArg (fun k => ((background.family.obj (KIP126.Literature.nuZero background X)).E₂ k : Type)) h01).mp
        (background.comparison.nuE2 X 0 s t 0 x)
    let a1 : BiHom (t-s) (t+0) (XModLambdaN (KIP126.Literature.nuZero background X) 1) :=
      (background.firstQuotient X 0 s t).symm x
    have hr : Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X)))) (s,t,t+0)
        (familyPageMap background.family (XModLambdaN.incl (KIP126.Literature.nuZero background X) 1) 2 (s,t,t+0) x1) a1 :=
      background.comparisonCompatible.first_quotient X 0 s t x
    have hh := transport_detects h1 _ _ hr
    have cast_comp {A B C : Type} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
        hBC.mp (hAB.mp a) = hAC.mp a := by
      subst B
      subst C
      rfl
    have hx1 : (congrArg (fun k => ((background.family.obj (KIP126.Literature.nuZero background X)).E₂ k : Type)) h1).mp x1 = x0 := by
      exact cast_comp
        (congrArg (fun k => ((background.family.obj (KIP126.Literature.nuZero background X)).E₂ k : Type)) h01)
        (congrArg (fun k => ((background.family.obj (KIP126.Literature.nuZero background X)).E₂ k : Type)) h1)
        (congrArg (fun k => ((background.family.obj (KIP126.Literature.nuZero background X)).E₂ k : Type)) h0)
        (background.comparison.nuE2 X 0 s t 0 x)
    have hlabel : (congrArg (fun k => ((background.family.obj (XModLambdaN (KIP126.Literature.nuZero background X) 1)).E₂ k : Type)) h1).mp
        (familyPageMap background.family (XModLambdaN.incl (KIP126.Literature.nuZero background X) 1) 2 (s,t,t+0) x1) = xq0 1 :=
      (map_cast _ h1 x1).trans (congrArg (familyPageMap background.family (XModLambdaN.incl (KIP126.Literature.nuZero background X) 1)
        2 (s,t,t)) hx1)
    have halabel : (congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2
        (XModLambdaN (KIP126.Literature.nuZero background X) 1)) h1).mp a1 = KIP126.Literature.firstLabel background X s t x := by
      rfl
    exact (congrArg₂ (fun z a => Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X))))
      (s,t,t) z a) hlabel halabel).mp hh
  have hb := detects_map (.quotient 1 (.shift (0,0) (.nu X))) (.quotient 1 (.nu X))
    (XModLambdaN.map f 1) (s,t,t) _ _ hb0
  have hb' : Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) (xq 1)
      (KIP126.Literature.firstLabel background X s t x ≫ XModLambdaN.map f 1) :=
    (congrArg (fun z => Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) z
      (KIP126.Literature.firstLabel background X s t x ≫ XModLambdaN.map f 1)) (map_label 1)).mp hb
  rw [ha]
  convert hb' using 1
  unfold finiteTargetLabel
  rw [← map_regrade]
  unfold targetNuLabel
  rw [← map_regrade]
  congr 2
  have cast_heq {A B : Type} (h : A=B) (a : A) : HEq (h.mp a) a := by cases h; rfl
  have eqToHom_heq {A B : ModuleCat.{0} ℤ} (h : A=B) (a : A) : HEq ((eqToHom h) a) a := by
    cases h; rfl
  exact eq_of_heq ((eqToHom_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
private theorem subquotientMap_injective {R : Type*} [Ring R] {A : Type*} [AddCommGroup A] [Module R A]
    {Z Z' B : Submodule R A} (hZ : Z ≤ Z') :
    Function.Injective (KIP126.Literature.subquotientMap hZ (le_rfl : B ≤ B)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    obtain ⟨x,rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change KIP126.Literature.subquotientMap hZ (le_rfl : B ≤ B) (Submodule.Quotient.mk x) = 0 at hx
    change Submodule.Quotient.mk (Submodule.inclusion hZ x) = 0 at hx
    have hxB := (Submodule.Quotient.mk_eq_zero _).mp hx
    change x.val ∈ B at hxB
    change Submodule.Quotient.mk x = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr hxB
  · exact bot_le

private theorem nu_bottom_filtration (X : AdamsObject) (s t : ℤ)
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary))) :
    FiltrationAtLeast background.syntheticTower s a := by
  have hzero := KIP126.Literature.Standard.selectedFiltration_filtration_at_zero background.syntheticTower _ (t-s) t a
  by_cases hs : s ≤ 0
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) hs hzero
  · exact (KIP126.Literature.Standard.selectedFiltration_filtration_iff_of_infinity_zero (background.convergence (.nu X))
      0 s (t-s) t (by omega)
      (fun k _ hk => KIP126.Literature.Standard.selectedFiltration_nu_above_zero X k (t-s+k) t (by omega)) a).mp hzero

private theorem nu_projection_infinity_injective (X : AdamsObject) (q : ℕ) (hq : 0<q)
    (s t w : ℤ) (hw : 0≤t-w ∧ t-w<q) :
    Function.Injective ((background.family.map (XModLambdaN.incl
      (background.nu.functor.obj (X.obj background.auxiliary)) q)).eInftyMap (s,t,w)) := by
  intro x y hxy
  apply (KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).injective
  apply subquotientMap_injective (permanentCycles_le_cycles background X (s,t) ((q:ℤ)-t+w))
  have hx := KIP126.Literature.Standard.eInfinity_rho_nu X q hq (s,t) w hw x
  have hy := KIP126.Literature.Standard.eInfinity_rho_nu X q hq (s,t) w hw y
  exact hx.symm.trans ((congrArg (KIP126.Literature.Standard.infinityFiniteWindow X q hq (s,t) w hw) hxy).trans hy)

private theorem nu_first_label_detects (X : AdamsObject) (s t : ℤ)
    (x : ((background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))) (hx : x ∈ KIP126.Literature.permanentCycles background X (s,t))
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = KIP126.Literature.firstLabel background X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (background.convergence (.nu X)) (s,t,t)
      (nuWeightLabel background X s t t (by omega) x) a := by
  let e := (KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).symm
    (subquotientClass (KIP126.Literature.permanentCycles background X (s,t)) (KIP126.Literature.boundaries background X (1+t-t) (s,t)) ⟨x,hx⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t) (nuWeightLabel background X s t t (by omega) x) e := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) x e).mpr
    exact ⟨hx,(KIP126.Literature.Standard.infinityNuWindow X (s,t) t (by omega)).apply_symm_apply _⟩
  apply detects_reflect (.nu X) (.quotient 1 (.nu X)) (XModLambdaN.incl _ 1)
    (s,t,t) (nu_projection_infinity_injective X 1 (by omega) s t t (by omega))
    _ e he a (nu_bottom_filtration X s t a)
  have hz := zero_weight_label X 1 s t x
  change familyPageMap background.family (XModLambdaN.incl _ 1) 2 (s,t,t)
    (nuWeightLabel background X s t t (by omega) x) = _ at hz
  have hd := first_label_detects_unshifted X s t x (a ≫ XModLambdaN.incl _ 1) ha
  exact (congrArg (fun z => Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) z
    (a ≫ XModLambdaN.incl _ 1)) hz).mpr hd

private theorem nu_lambda_detects (X : AdamsObject) (k : ℕ) (hk : 0 < k)
    (s t : ℤ) (y : ((background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)))
    (hy : y ∈ KIP126.Literature.permanentCycles background X (s,t))
    (α : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (hα : α ≫ XModLambdaN.incl _ 1 = KIP126.Literature.firstLabel background X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (background.convergence (.nu X)) (s,t,t-k)
      (nuWeightLabel background X s t (t-k) (by omega) y) (lambdaMultiply k α) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have ha := nu_first_label_detects X s t y hy α hα
  have hsource : (s,t,t)=(s,(t-s)+s,t) := by simp
  have hstem := detects_transport hsource _ _ ha
  let L : ((SyntheticObject.shift (0,-(k:ℤ)) (.nu X)).obj background.nu background.auxiliary) ⟶ A := lambdaPow k A
  have hmap := shifted_map_detects (.nu X) (.nu X) (0,-(k:ℤ)) (t-s,t) s L
    (regradeE2 hsource (nuWeightLabel background X s t t (by omega) y)) α hstem
  have hindex : (s,((t-s,t)+(0,-(k:ℤ))).1+s,((t-s,t)+(0,-(k:ℤ))).2) =
      (s,t,t-k) := by ext <;> simp [sub_eq_add_neg]
  have hmap := detects_transport hindex _ _ hmap
  obtain ⟨e,he,b,hb,hgb⟩ := hmap
  obtain ⟨e0,he0,_⟩ := ha
  have heStem := representative_transport hsource _ _ he0
  have heMap := shifted_representative_map (.nu X) (.nu X)
    (0,-(k:ℤ)) (t-s,t) s L _ _ heStem
  have heMap := representative_transport hindex _ _ heMap
  have heq := he.unique heMap
  have heq' : e = KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) t e0 := by
    convert heq using 1
    delta KIP126.Literature.Standard.infinityLambda
      InfinityShiftCoordinates.lambdaMap InfinityShiftCoordinates.shift infinityShift
      KIP126.Literature.Standard.infinityShiftData
      KIP126.Literature.Standard.infinityShift_comparison
    dsimp only []
    simp only [show k ≠ 0 by omega, ↓reduceDIte,
      Iso.trans_hom, ModuleCat.comp_apply, eqToIso.hom]
    exact (infinity_map_regrade L hindex _).symm
  have hlabel : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel background X s t (t-k) (by omega) y)
      (KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) t e0) := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-k) (by omega) y _).mpr
    refine ⟨hy,?_⟩
    rw [KIP126.Literature.Standard.eInfinity_lambda_nu X k (s,t) t (by omega)]
    have he0' := (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) y e0).mp he0
    rw [he0'.2]
    rfl
  have heFinal : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel background X s t (t-k) (by omega) y) e := by
    rw [heq']
    exact hlabel
  refine ⟨e,heFinal,b,?_,hgb⟩
  convert hb using 1
  repeat rw [regrade_precomp]
  delta lambdaMultiply
  simp only [L, shiftHomotopyClass, Category.assoc]
  simp only [A]
  erw [lambdaPow_naturality k α]
  simp only [←Category.assoc,eqToHom_trans]

private theorem detected_zero_infinity (A : SyntheticObject) (p : Tridegree)
    (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ p)
    (h : Detects (background.convergence A) p x 0) :
    HasInfinityRepresentative _ 2 p x 0 := by
  obtain ⟨e,he,a,ha,hga⟩ := h
  have haz : a = 0 := (ModuleCat.mono_iff_injective
    ((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).F p.1 (p.2.1-p.1,p.2.2)).arrow).mp
      inferInstance (ha.trans (map_zero _).symm)
  have hez : e = 0 := ((background.convergence A).identification p).toLinearEquiv.injective (by
    change ((background.convergence A).identification p).hom e =
      ((background.convergence A).identification p).hom 0
    rw [hga,haz,map_zero,map_zero])
  rwa [hez] at he


private theorem normalizeInitialProjection
    (P : SSData (ModuleCat.{0} ℤ)) (n m : WithTop ℕ)
    (hn : n = 0) (hnm : n ≤ m) :
    Subobject.ofLE (P.Z m) (P.Z n) (P.Z_anti hnm) ≫ P.pageπ n =
      Subobject.ofLE (P.Z m) (P.Z 0) (P.Z_anti bot_le) ≫ P.pageπ 0 ≫
        eqToHom (congrArg P.page hn.symm) := by
  subst n
  simp only [eqToHom_refl, Category.comp_id]

private theorem boundary_represents_zero (X : AdamsObject) (r : ℤ) (hr : 2 ≤ r)
    (p : Bidegree) (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 p)
    (hy : y ∈ KIP126.Literature.boundaries background X (r-1) p) :
    RepresentsOnPage (background.classical.obj (X.obj background.auxiliary)) r p y 0 := by
  let E := background.classical.obj (X.obj background.auxiliary)
  let P := E.ssData p
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [background.classical.firstPage]; rfl
  have hn : (↑(r-1-1).toNat : WithTop ℕ)=n := by
    dsimp [n,E]; rw [background.classical.firstPage]; congr 2; omega
  change ∃ b, boundaryLabel background X (↑(r-1-1).toNat) p b = y at hy
  rw [hn] at hy
  obtain ⟨b,hb⟩ := hy
  let j := Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n)
  refine ⟨hr,j b,?_,?_⟩
  · change (j ≫ Subobject.ofLE (P.Z n) (P.Z n₀) _ ≫ P.pageπ n₀) b=y
    rw [normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)]
    change ((j ≫ Subobject.ofLE (P.Z n) (P.Z 0) _) ≫ P.pageπ 0 ≫ _) b=y
    rw [show j ≫ Subobject.ofLE (P.Z n) (P.Z 0) _ =
      Subobject.ofLE (P.B n) (P.Z 0) _ by simp only [j,Subobject.ofLE_comp_ofLE]]
    exact hb
  · exact (P.pageπ_eq_zero_iff n (j b)).mpr ⟨b,rfl⟩

private theorem permanent_membership (X : AdamsObject) (s t : ℤ)
    (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (hy : ClassicalPermanentCycle background X (s,t) y) : y ∈ KIP126.Literature.permanentCycles background X (s,t) := by
  obtain ⟨z,hz⟩ := hy
  refine ⟨z,?_⟩
  have h := normalizeInitialProjection ((background.classical.obj (X.obj background.auxiliary)).ssData (s,t))
    (↑(2-(background.classical.obj (X.obj background.auxiliary)).r₀).toNat)
    ⊤ (by rw [background.classical.firstPage]; rfl) le_top
  exact (congrArg (fun f => f z) h).symm.trans hz

private theorem subquotient_zero_iff {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    (Z B : Submodule R A) (y : Z) : subquotientClass Z B y = 0 ↔ y.val ∈ B :=
  Submodule.Quotient.mk_eq_zero _

private theorem lifetime_proof :
  ∀ (X : AdamsObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (KIP126.Literature.nuZero background X)),
    ClassicalPermanentCycle background X (s,t) x →
    SurvivesTo (background.classical.obj (X.obj background.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = KIP126.Literature.firstLabel background X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  intro X s t r hr x a hx hsurv hlabel hz
  let α := a ≫ SyntheticCategory.biShift_zero.hom.app _
  have hα : α ≫ XModLambdaN.incl _ 1 = KIP126.Literature.firstLabel background X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
    dsimp only [α]
    rw [Category.assoc, XModLambdaN.incl_naturality, ←Category.assoc]
    exact congrArg (fun z => z ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) hlabel
  have hzero : lambdaMultiply (r-1) α = 0 := by
    have h : lambdaMultiply (r-1) a ≫ SyntheticCategory.biShift_zero.hom.app _ = 0 := by
      rw [hz, zero_comp]
    delta lambdaMultiply at h ⊢
    simpa only [α, Category.assoc] using h
  have hmem := permanent_membership X s t x hx
  have hbound : x ∈ KIP126.Literature.boundaries background X r (s,t) := by
    by_cases hk : 0 < r-1
    · have hd := nu_lambda_detects X (r-1) hk s t x hmem α hα
      rw [hzero] at hd
      have he := detected_zero_infinity (.nu X) (s,t,t-(r-1:ℕ)) _ hd
      have hclass := (KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-(r-1:ℕ)) (by omega) x 0).mp he
      have hb : x ∈ KIP126.Literature.boundaries background X (1+t-(t-(r-1:ℕ))) (s,t) :=
        (subquotient_zero_iff _ _ ⟨x,hclass.1⟩).mp (by rw [←hclass.2,map_zero])
      convert hb using 1
      congr 1
      omega
    · have hr1 : r=1 := by omega
      subst r
      have hzα : α=0 := by
        have h := KIP126.Literature.Standard.lambdaMultiplyZero α
        have hz' : lambdaMultiply 0 α=0 := hzero
        have zero_cast {w w' : ℤ} (h : w=w') : HEq (0 : BiHom (t-s) w (background.nu.functor.obj (X.obj background.auxiliary))) (0 : BiHom (t-s) w' (background.nu.functor.obj (X.obj background.auxiliary))) := by cases h; rfl
        exact eq_of_heq (h.symm.trans ((heq_of_eq hz').trans (zero_cast (by simp))))
      have hd := nu_first_label_detects X s t x hmem α hα
      rw [hzα] at hd
      have he := detected_zero_infinity (.nu X) (s,t,t) _ hd
      have hclass := (KIP126.Literature.Standard.eInfinity_nu_labels X s t t (by omega) x 0).mp he
      have hb : x ∈ KIP126.Literature.boundaries background X (1+t-t) (s,t) :=
        (subquotient_zero_iff _ _ ⟨x,hclass.1⟩).mp (by rw [←hclass.2,map_zero])
      convert hb using 1
      congr 1
      omega
  obtain ⟨xr,hrep,hne⟩ := hsurv
  exact hne (hrep.unique (boundary_represents_zero X (r+1) (by omega) (s,t) x (by
    simpa only [add_sub_cancel_right] using hbound)))


private theorem permanent_of_membership (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.permanentCycles background X (s,t)) :
    ClassicalPermanentCycle background X (s,t) x := by
  obtain ⟨z,hz⟩ := hx
  refine ⟨z,?_⟩
  have h := normalizeInitialProjection ((background.classical.obj (X.obj background.auxiliary)).ssData (s,t))
    (↑(2-(background.classical.obj (X.obj background.auxiliary)).r₀).toNat)
    ⊤ (by rw [background.classical.firstPage]; rfl) le_top
  exact (congrArg (fun f => f z) h).trans hz

private theorem finite_first_detection_unique (X : AdamsObject) (s t : ℤ)
    (x : (background.family.quotient (background.nu.functor.obj (X.obj background.auxiliary)) 1).E₂ (s,t,t))
    (a b : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) 1))
    (ha : Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) x a)
    (hb : Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) x b) : a=b := by
  have hf := detects_sub_filtration (background.convergence (.quotient 1 (.nu X))) (s,t,t) ha hb
  apply sub_eq_zero.mp
  exact Standard.selectedFiltration_finite_high_filtration_zero X 1 (by decide)
    (t-s) t (s+1) (by omega) (a-b) hf

private theorem projection_eq_first_of_detects (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : Detects (background.convergence (.nu X)) (s,t,t)
      (nuWeightLabel background X s t t (by omega) x) a) :
    a ≫ XModLambdaN.incl _ 1 = firstLabel background X s t x ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  have hp := detects_map (.nu X) (.quotient 1 (.nu X)) (XModLambdaN.incl _ 1)
    (s,t,t) _ _ ha
  have hz := zero_weight_label X 1 s t x
  change familyPageMap background.family (XModLambdaN.incl _ 1) 2 (s,t,t)
    (nuWeightLabel background X s t t (by omega) x) = _ at hz
  have hp' := (congrArg (fun z => Detects (background.convergence (.quotient 1 (.nu X)))
    (s,t,t) z (a ≫ XModLambdaN.incl _ 1)) hz).mp hp
  exact finite_first_detection_unique X s t _ _ _ hp'
    (first_label_detects_unshifted X s t x _ rfl)

private theorem detects_lift_exists (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.permanentCycles background X (s,t)) :
    ∃ a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      Detects (background.convergence (.nu X)) (s,t,t)
        (nuWeightLabel background X s t t (by omega) x) a := by
  let e := (Standard.infinityNuWindow X (s,t) t (by omega)).symm
    (subquotientClass (KIP126.Literature.permanentCycles background X (s,t))
      (KIP126.Literature.boundaries background X (1+t-t) (s,t)) ⟨x,hx⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t) (nuWeightLabel background X s t t (by omega) x) e := by
    apply (Standard.eInfinity_nu_labels X s t t (by omega) x e).mpr
    exact ⟨hx,(Standard.infinityNuWindow X (s,t) t (by omega)).apply_symm_apply _⟩
  let F := background.syntheticTower.filtration (background.nu.functor.obj (X.obj background.auxiliary))
  letI : Epi (F.toAssociatedGraded s (t-s,t)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t))).mp
    inferInstance (((background.convergence (.nu X)).identification (s,t,t)).hom e)
  exact ⟨(F.F s (t-s,t)).arrow b,e,he,b,rfl,hb.symm⟩

private theorem subquotientClass_surjective {R A : Type*} [Ring R]
    [AddCommGroup A] [Module R A] (Z B : Submodule R A) :
    Function.Surjective (subquotientClass Z B) :=
  Submodule.mkQ_surjective _

private theorem detects_permanent_label (X : AdamsObject) (s t : ℤ)
    (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary))) :
    ∃ x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t),
      ClassicalPermanentCycle background X (s,t) x ∧
      Detects (background.convergence (.nu X)) (s,t,t)
        (nuWeightLabel background X s t t (by omega) x) a := by
  obtain ⟨b,hb⟩ := filtration_representative_exists _ (t-s,t) s a (nu_bottom_filtration X s t a)
  let e := ((background.convergence (.nu X)).identification (s,t,t)).inv
    ((background.syntheticTower.filtration _).toAssociatedGraded s (t-s,t) b)
  obtain ⟨x,hx⟩ := subquotientClass_surjective _ _
    (Standard.infinityNuWindow X (s,t) t (by omega) e)
  refine ⟨x.val,permanent_of_membership X s t x.val x.property,e,?_,b,hb,?_⟩
  · exact (Standard.eInfinity_nu_labels X s t t (by omega) x.val e).mpr ⟨x.property,hx.symm⟩
  · exact ((background.convergence (.nu X)).identification (s,t,t)).toLinearEquiv.apply_symm_apply _

private theorem first_label_injective (X : AdamsObject) (s t : ℤ) :
    Function.Injective (firstLabel background X s t) := by
  intro x y h
  apply (background.firstQuotient X 0 s t).symm.injective
  have cast_inj {A B : Type} (hAB : A=B) (x y : A) (h : hAB.mp x = hAB.mp y) : x=y := by
    cases hAB
    exact h
  unfold firstLabel at h
  exact cast_inj _ _ _ h

private theorem permanent_lift_proof : ∀ X : AdamsObject, PermanentLiftAt background X := by
  intro X s t x
  let Z := background.nu.functor.obj (X.obj background.auxiliary)
  let f : nuZero background X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero background X := SyntheticCategory.biShift_zero.inv.app _
  letI : IsIso f := inferInstanceAs (IsIso (SyntheticCategory.biShift_zero.hom.app _))
  letI : IsIso (XModLambdaN.map f 1) :=
    inferInstanceAs (IsIso ((background.quotients.functoriality.functor 1).map f))
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := detects_lift_exists X s t x (permanent_membership X s t x hx)
    refine ⟨a ≫ g,?_⟩
    have hp := projection_eq_first_of_detects X s t x a ha
    apply (cancel_mono (XModLambdaN.map f 1)).mp
    change ((a ≫ g) ≫ XModLambdaN.incl _ 1) ≫ XModLambdaN.map f 1 = _
    rw [Category.assoc]
    rw [←XModLambdaN.incl_naturality]
    simpa only [f,g,Category.assoc,Iso.inv_hom_id_app_assoc] using hp
  · rintro ⟨a,ha⟩
    obtain ⟨y,hy,hd⟩ := detects_permanent_label X s t (a ≫ f)
    have hp := projection_eq_first_of_detects X s t y (a ≫ f) hd
    have hh : firstLabel background X s t x = firstLabel background X s t y := by
      apply (cancel_mono (XModLambdaN.map f 1)).mp
      rw [←hp,Category.assoc,XModLambdaN.incl_naturality,←Category.assoc]
      exact congrArg (fun z => z ≫ XModLambdaN.map f 1) ha.symm
    exact (first_label_injective X s t hh).symm ▸ hy


private theorem reaches_iff_cycle (X : AdamsObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t)) :
    ReachesPage (background.classical.obj (X.obj background.auxiliary)) (q+1) (s,t) x ↔
      x ∈ KIP126.Literature.cycles background X q (s,t) := by
  let E := background.classical.obj (X.obj background.auxiliary)
  let P := E.ssData (s,t)
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑((q:ℤ)+1-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [background.classical.firstPage]; rfl
  have hn : (↑((q:ℤ)-1).toNat : WithTop ℕ)=n := by
    dsimp [n,E]; rw [background.classical.firstPage]; congr 2; omega
  change (∃ xr, RepresentsOnPage E (q+1) (s,t) x xr) ↔
    ∃ z, cycleLabel background X (↑((q:ℤ)-1).toNat) (s,t) z = x
  rw [hn]
  constructor
  · rintro ⟨xr,hr,z,hz,_⟩
    refine ⟨z,?_⟩
    have h := normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)
    exact (congrArg (fun f => f z) h).symm.trans hz
  · rintro ⟨z,hz⟩
    refine ⟨P.pageπ n z,by omega,z,?_,rfl⟩
    have h := normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)
    exact (congrArg (fun f => f z) h).trans hz

private theorem finite_bottom_filtration (X : AdamsObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    FiltrationAtLeast background.syntheticTower s a := by
  have hzero := Standard.selectedFiltration_filtration_at_zero background.syntheticTower _ (t-s) t a
  by_cases hs : s ≤ 0
  · exact background.syntheticTower.filtrationSubmodule_antitone _ (t-s,t) hs hzero
  · exact (Standard.selectedFiltration_filtration_iff_of_infinity_zero
      (background.convergence (.quotient q (.nu X))) 0 s (t-s) t (by omega)
      (fun k _ hk => Standard.selectedFiltration_finite_infinity_zero_outside X q hq k
        (t-s+k) t (by omega)) a).mp hzero

private theorem finite_detects_lift_exists (X : AdamsObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (hx : x ∈ KIP126.Literature.cycles background X q (s,t)) :
    ∃ a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
      Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
        (familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t)
          (nuWeightLabel background X s t t (by omega) x)) a := by
  have hx' : x ∈ KIP126.Literature.cycles background X ((q:ℤ)-t+t) (s,t) := by simpa using hx
  let e := (Standard.infinityFiniteWindow X q hq (s,t) t (by omega)).symm
    (subquotientClass (KIP126.Literature.cycles background X ((q:ℤ)-t+t) (s,t))
      (KIP126.Literature.boundaries background X (1+t-t) (s,t)) ⟨x,hx'⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,t)
      (familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (nuWeightLabel background X s t t (by omega) x)) e := by
    apply (Standard.eInfinity_finite_labels X q hq s t t (by omega) x e).mpr
    exact ⟨hx',(Standard.infinityFiniteWindow X q hq (s,t) t (by omega)).apply_symm_apply _⟩
  let F := background.syntheticTower.filtration (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)
  letI : Epi (F.toAssociatedGraded s (t-s,t)) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective (F.toAssociatedGraded s (t-s,t))).mp
    inferInstance (((background.convergence (.quotient q (.nu X))).identification (s,t,t)).hom e)
  exact ⟨(F.F s (t-s,t)).arrow b,e,he,b,rfl,hb.symm⟩

private theorem finite_detects_cycle_label (X : AdamsObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)) :
    ∃ x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t),
      x ∈ KIP126.Literature.cycles background X q (s,t) ∧
      Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
        (familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t)
          (nuWeightLabel background X s t t (by omega) x)) a := by
  obtain ⟨b,hb⟩ := filtration_representative_exists _ (t-s,t) s a
    (finite_bottom_filtration X q hq s t a)
  let e := ((background.convergence (.quotient q (.nu X))).identification (s,t,t)).inv
    ((background.syntheticTower.filtration _).toAssociatedGraded s (t-s,t) b)
  obtain ⟨x,hx⟩ := subquotientClass_surjective _ _
    (Standard.infinityFiniteWindow X q hq (s,t) t (by omega) e)
  refine ⟨x.val,by simpa using x.property,e,?_,b,hb,?_⟩
  · exact (Standard.eInfinity_finite_labels X q hq s t t (by omega) x.val e).mpr ⟨x.property,hx.symm⟩
  · exact ((background.convergence (.quotient q (.nu X))).identification (s,t,t)).toLinearEquiv.apply_symm_apply _

private theorem finite_restrict_eq_first_of_detects (X : AdamsObject) (q : ℕ) (hq : 0<q)
    (s t : ℤ) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
      (familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (nuWeightLabel background X s t t (by omega) x)) a) :
    a ≫ (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho 1 q (by omega) =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  let rho := (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho 1 q (by omega)
  have hp := detects_map (.quotient q (.nu X)) (.quotient 1 (.nu X)) rho (s,t,t) _ _ ha
  have hz : familyPageMap background.family rho 2 (s,t,t)
      (familyPageMap background.family (XModLambdaN.incl _ q) 2 (s,t,t)
        (nuWeightLabel background X s t t (by omega) x)) =
      regradeE2 (by simp) (finiteTargetLabel background X 1 s t 0 x) := by
    rw [←ModuleCat.comp_apply,family_page_comp]
    dsimp only [rho]
    rw [(background.quotients.tower _).rho_quotient]
    exact zero_weight_label X 1 s t x
  have hp' := (congrArg (fun z => Detects (background.convergence (.quotient 1 (.nu X)))
    (s,t,t) z (a ≫ rho)) hz).mp hp
  exact finite_first_detection_unique X s t _ _ _ hp'
    (first_label_detects_unshifted X s t x _ rfl)

private theorem finite_lift_proof : FiniteLiftCriterion background := by
  intro X q hq s t x
  let Z := background.nu.functor.obj (X.obj background.auxiliary)
  let f : nuZero background X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero background X := SyntheticCategory.biShift_zero.inv.app _
  letI : IsIso f := inferInstanceAs (IsIso (SyntheticCategory.biShift_zero.hom.app _))
  letI : IsIso (XModLambdaN.map f 1) :=
    inferInstanceAs (IsIso ((background.quotients.functoriality.functor 1).map f))
  have hgf : XModLambdaN.map g 1 ≫ XModLambdaN.map f 1 = 𝟙 _ := by
    rw [←background.quotients.functoriality.map_comp]
    simp only [g,f,Iso.inv_hom_id_app]
    exact background.quotients.functoriality.map_id _ _
  constructor
  · intro hx
    obtain ⟨a,ha⟩ := finite_detects_lift_exists X q hq s t x ((reaches_iff_cycle X q hq s t x).mp hx)
    refine ⟨a ≫ XModLambdaN.map g q,?_⟩
    apply (cancel_mono (XModLambdaN.map f 1)).mp
    have hp := finite_restrict_eq_first_of_detects X q hq s t x a ha
    have hrho := (background.quotients.natural g).rho_naturality (i:=1) (j:=q) (by omega)
    have he := congrArg (fun z => (a ≫ z) ≫ XModLambdaN.map f 1) hrho.symm
    have he' : ((a ≫ XModLambdaN.map g q) ≫
        (background.quotients.tower (nuZero background X)).rho 1 q (by omega)) ≫ XModLambdaN.map f 1 =
        a ≫ (background.quotients.tower Z).rho 1 q (by omega) := by
      repeat rw [Category.assoc] at he
      rw [hgf, Category.comp_id] at he
      repeat rw [Category.assoc]
      exact he
    exact he'.trans hp
  · rintro ⟨a,ha⟩
    obtain ⟨y,hy,hd⟩ := finite_detects_cycle_label X q hq s t (a ≫ XModLambdaN.map f q)
    have hp := finite_restrict_eq_first_of_detects X q hq s t y _ hd
    have hh : firstLabel background X s t x = firstLabel background X s t y := by
      apply (cancel_mono (XModLambdaN.map f 1)).mp
      rw [←hp,Category.assoc,←(background.quotients.natural f).rho_naturality,←Category.assoc]
      exact congrArg (fun z => z ≫ XModLambdaN.map f 1) ha.symm
    exact (first_label_injective X s t hh).symm ▸ (reaches_iff_cycle X q hq s t y).mpr hy


private theorem zero_rep_boundary (X : AdamsObject) (r : ℤ) (p : Bidegree)
    (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 p)
    (hy : RepresentsOnPage (background.classical.obj (X.obj background.auxiliary)) r p y 0) :
    y ∈ KIP126.Literature.boundaries background X (r-1) p := by
  let E := background.classical.obj (X.obj background.auxiliary)
  let P := E.ssData p
  let n₀ : WithTop ℕ := ↑(2-E.r₀).toNat
  let n : WithTop ℕ := ↑(r-E.r₀).toNat
  have hn₀ : n₀=0 := by dsimp [n₀,E]; rw [background.classical.firstPage]; rfl
  have hn : (↑(r-1-1).toNat : WithTop ℕ)=n := by
    dsimp [n,E]; rw [background.classical.firstPage]; congr 2; omega
  obtain ⟨hr,z,hz,hz0⟩ := hy
  have hproj := normalizeInitialProjection P n₀ n hn₀ (by rw [hn₀]; exact bot_le)
  have hlabel : cycleLabel background X n p z = y := (congrArg (fun f => f z) hproj).symm.trans hz
  obtain ⟨b,hb⟩ := (P.pageπ_eq_zero_iff n z).mp hz0
  change ∃ b, boundaryLabel background X (↑(r-1-1).toNat) p b = y
  rw [hn]
  refine ⟨b,?_⟩
  have hcomp : Subobject.ofLE (P.B n) (P.Z n) (P.B_le_Z n) ≫
      cycleLabel background X n p = boundaryLabel background X n p := by
    dsimp only [P,E]
    delta cycleLabel boundaryLabel
    simp only [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hcomp,ModuleCat.comp_apply,hb]
  exact hlabel

private theorem hit_boundary (X : AdamsObject) (r : ℕ) (hr : 2≤r)
    (p : Bidegree) (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 p)
    (hy : HitOnPage (background.classical.obj (X.obj background.auxiliary)) r p y) :
    y ∈ KIP126.Literature.boundaries background X r p := by
  obtain ⟨q,h,z,yr,hyr,_,hd⟩ := hy
  obtain ⟨x,hx⟩ := FinitePageCalculus.page_has_representative (by omega : 2≤(r:ℤ)) z
  have heq : HasDifferential (background.classical.obj (X.obj background.auxiliary)) r q p x y :=
    ⟨h,z,yr,hx,hyr,hd⟩
  have hz := FinitePageCalculus.differential_target_later_zero
    (t:=(r:ℤ)+1) (by rw [background.classical.firstPage]; omega) (by omega) heq
  simpa only [add_sub_cancel_right] using zero_rep_boundary X ((r:ℤ)+1) p y hz

private theorem regrade_heq {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') (a : BiHom m w A) : HEq (homotopyRegrade hm hw a) a := by
  subst m'; subst w'; rfl

private theorem regrade_zero {m m' w w' : ℤ} {A : SyntheticSpectrum}
    (hm : m=m') (hw : w=w') : homotopyRegrade hm hw (0 : BiHom m w A) = 0 := by
  subst m'; subst w'; rfl

private theorem lambda_quotient_zero {m w : ℤ} {A : SyntheticSpectrum}
    (a : BiHom m w A) : quotientClass 1 (lambdaMultiply 1 a) = 0 := by
  delta quotientClass lambdaMultiply
  rw [←lambdaPow_naturality]
  simp only [Category.assoc,XModLambdaN.lambdaPow_comp_incl,comp_zero]

private theorem boundary_lift_unshifted (X : AdamsObject) (r : ℕ) (hr : 2≤r)
    (s t : ℤ) (y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (hy : ClassicalPermanentCycle background X (s,t) y)
    (hhit : HitOnPage (background.classical.obj (X.obj background.auxiliary)) r (s,t) y) :
    ∃ a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)),
      a ≫ XModLambdaN.incl _ 1 = firstLabel background X s t y ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 ∧
      lambdaMultiply (r-1) a = 0 := by
  let k := r-1
  have hk : 0<k := by dsimp [k]; omega
  have hym := permanent_membership X s t y hy
  obtain ⟨α,hα⟩ := detects_lift_exists X s t y hym
  have hlabel := projection_eq_first_of_detects X s t y α hα
  have hdet := nu_lambda_detects X k hk s t y hym α hlabel
  have hbound := hit_boundary X r hr (s,t) y hhit
  have hinf0 : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel background X s t (t-k) (by omega) y) 0 := by
    apply (Standard.eInfinity_nu_labels X s t (t-k) (by omega) y 0).mpr
    refine ⟨hym,?_⟩
    rw [map_zero]
    symm
    apply (subquotient_zero_iff _ _ ⟨y,hym⟩).mpr
    convert hbound using 1
    congr 1
    dsimp [k]
    omega
  have hf := detects_zero_infinity_filtration (background.convergence (.nu X)) (s,t,t-k) hdet hinf0
  obtain ⟨β,hβ⟩ := (Standard.filtration_lambda X (t-s) (t-k) (s+1) (by omega)
    (lambdaMultiply k α)).mp hf
  let b : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary)) :=
    homotopyRegrade rfl (by omega : ((t-s)+(s+1))-(1:ℕ)=t) (lambdaMultiply 1 β)
  have hb0 : b ≫ XModLambdaN.incl _ 1 = 0 := by
    change homotopyRegrade _ _ (lambdaMultiply 1 β) ≫ XModLambdaN.incl _ 1 = 0
    rw [←regrade_comp]
    have hz := lambda_quotient_zero β
    change lambdaMultiply 1 β ≫ XModLambdaN.incl _ 1 = 0 at hz
    rw [hz]
    exact regrade_zero _ _
  have hbα : lambdaMultiply k b = lambdaMultiply k α := by
    have hN : ((t-s+(s+1)-(t-(k:ℤ))).toNat) = 1+k := by omega
    have exp_transport (i j : ℕ) (h : i=j) : HEq (lambdaMultiply i β) (lambdaMultiply j β) := by
      subst j
      rfl
    have hβ0 : HEq (lambdaMultiply (1+k) β) (lambdaMultiply k α) :=
      (exp_transport _ _ hN.symm).trans ((regrade_heq _ _ _).symm.trans (heq_of_eq hβ))
    have hbheq := Standard.multiply_heq k (by omega : t=((t-s)+(s+1))-(1:ℕ))
      (regrade_heq rfl (by omega) (lambdaMultiply 1 β))
    have hc := Standard.lambda_multiply_compose 1 k β
    exact eq_of_heq (hbheq.trans (hc.trans hβ0))
  refine ⟨α-b,?_,?_⟩
  · rw [Preadditive.sub_comp,hlabel,hb0,sub_zero]
  · change lambdaMultiply k (α-b)=0
    have hsub : lambdaMultiply k (α-b)=lambdaMultiply k α-lambdaMultiply k b := by
      delta lambdaMultiply
      simp only [Preadditive.comp_sub]
    rw [hsub,hbα,sub_self]

private theorem boundary_lift_proof :
  ∀ (X : AdamsObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle background X (s,t) y →
    HitOnPage (background.classical.obj (X.obj background.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero background X), quotientClass 1 a = firstLabel background X s t y ∧
      lambdaMultiply (r-1) a = 0 := by
  intro X s t r hr y hy hhit
  obtain ⟨a,ha,hak⟩ := boundary_lift_unshifted X r hr s t y hy hhit
  let Z := background.nu.functor.obj (X.obj background.auxiliary)
  let f : nuZero background X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero background X := SyntheticCategory.biShift_zero.inv.app _
  letI : IsIso f := inferInstanceAs (IsIso (SyntheticCategory.biShift_zero.hom.app _))
  letI : IsIso (XModLambdaN.map f 1) :=
    inferInstanceAs (IsIso ((background.quotients.functoriality.functor 1).map f))
  refine ⟨a ≫ g,?_,?_⟩
  · apply (cancel_mono (XModLambdaN.map f 1)).mp
    change ((a ≫ g) ≫ XModLambdaN.incl _ 1) ≫ XModLambdaN.map f 1 = _
    rw [Category.assoc,←XModLambdaN.incl_naturality]
    simpa only [f,g,Category.assoc,Iso.inv_hom_id_app_assoc] using ha
  · have he : lambdaMultiply (r-1) (a ≫ g) = lambdaMultiply (r-1) a ≫ g := by
      delta lambdaMultiply
      simp only [Category.assoc]
    rw [he,hak,zero_comp]

end
end SelectedLifetimeConstruction

/-- The one-step quotient is concentrated at the matching filtration, so
its detection class determines the actual first-quotient lift. -/
public theorem permanent_lift :
  ∀ X : AdamsObject, PermanentLiftAt background X := by
  exact SelectedLifetimeConstruction.permanent_lift_proof

/-- A zero lambda power would put the same first-quotient label in the
earlier boundary submodule, contradicting its specified nonzero survival. -/
public theorem realization_lifetime :
  ∀ (X : AdamsObject) (s t : ℤ) (r : ℕ), 1 ≤ r →
    ∀ (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
      (a : BiHom (t-s) t (nuZero background X)),
    ClassicalPermanentCycle background X (s,t) x →
    SurvivesTo (background.classical.obj (X.obj background.auxiliary)) (r+1) (s,t) x →
    quotientClass 1 a = firstLabel background X s t x → lambdaMultiply (r-1) a ≠ 0 := by
  exact SelectedLifetimeConstruction.lifetime_proof


public theorem realization_detection :
  ∀ (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : BiHom (t-s) t (nuZero background X)),
    NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x →
    quotientClass 1 a = firstLabel background X s t x →
    ClassicalDetects (background.classicalConvergence X) (s,t) x (realizeNu X a) := by
  sorry


public theorem realization_prescribed_lift :
  ∀ (X : AdamsObject) (s t : ℤ)
    (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t))
    (a : HomotopyGroup (t-s) (X.obj background.auxiliary)),
    NonzeroSurvival (background.classical.obj (X.obj background.auxiliary)) (s,t) x →
    ClassicalDetects (background.classicalConvergence X) (s,t) x a →
    ∃ b : BiHom (t-s) t (nuZero background X), quotientClass 1 b = firstLabel background X s t x ∧
      realizeNu X b = a := by
  sorry

/-- A permanent label hit on the specified page has a first-quotient lift
annihilated by the corresponding power of λ. -/
public theorem realization_boundary_lift :
  ∀ (X : AdamsObject) (s t : ℤ) (r : ℕ), 2 ≤ r →
    ∀ y : (background.classical.obj (X.obj background.auxiliary)).Page 2 (s,t),
    ClassicalPermanentCycle background X (s,t) y →
    HitOnPage (background.classical.obj (X.obj background.auxiliary)) r (s,t) y →
    ∃ a : BiHom (t-s) t (nuZero background X), quotientClass 1 a = firstLabel background X s t y ∧
      lambdaMultiply (r-1) a = 0 := by
  exact SelectedLifetimeConstruction.boundary_lift_proof

set_option backward.isDefEq.respectTransparency false in
private theorem absorbedTheta5Lift :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum),
    KIP126.Literature.Theta5Detected background a ∧ realizeSphere 62 64 a = theta5 := by
  obtain ⟨b, hb, hr⟩ := realization_prescribed_lift .sphere 2 64
    (background.standardClasses.standardHiSquare 5) theta5
    h5Square_permanent theta5_detection
  change BiHom 62 64 (KIP126.Literature.nuZero background .sphere) at b
  change (realization_sphere 62 64).hom ≫ background.recovery.realization.map b ≫
      background.recovery.realization.map (SyntheticCategory.biShift_zero.hom.app _) ≫
      background.recovery.nuRealizationIso.hom.app SphereSpectrum = theta5 at hr
  let e : KIP126.Literature.nuZero background .sphere ≅ (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.app _ ≪≫ background.nu.unitIso
  let a : BiHom 62 64 (S_0_0 : SyntheticSpectrum) := b ≫ e.hom
  have hq : quotientClass 1 a ≫ XModLambdaN.map e.inv 1 = quotientClass 1 b := by
    dsimp only [a, quotientClass]
    simp (config := { congrConsts := false }) only [Category.assoc]
    rw [← XModLambdaN.incl_naturality]
    simp (config := { congrConsts := false }) only [Category.assoc, Iso.hom_inv_id_assoc]
  refine ⟨a, ?_, ?_⟩
  · change (background.firstQuotient .sphere 0 2 64)
      (quotientClass 1 a ≫ XModLambdaN.map e.inv 1) = _
    rw [hq]
    have hb' : quotientClass 1 b =
        (background.firstQuotient .sphere 0 2 64).symm
          (background.standardClasses.standardHiSquare 5) := hb
    rw [hb']
    exact (background.firstQuotient .sphere 0 2 64).apply_symm_apply _
  · have hu : background.recovery.realization.map e.hom ≫
        background.recovery.realization.map background.nu.unitIso.inv =
        background.recovery.realization.map
          (SyntheticCategory.biShift_zero.hom.app
            (background.nu.functor.obj SphereSpectrum)) := by
      have hu0 : e.hom ≫ background.nu.unitIso.inv =
          SyntheticCategory.biShift_zero.hom.app
            (background.nu.functor.obj SphereSpectrum) :=
        (Category.assoc
          (SyntheticCategory.biShift_zero.hom.app
            (background.nu.functor.obj SphereSpectrum))
          background.nu.unitIso.hom background.nu.unitIso.inv).trans
          ((congrArg (fun k =>
              SyntheticCategory.biShift_zero.hom.app
                (background.nu.functor.obj SphereSpectrum) ≫ k)
            background.nu.unitIso.hom_inv_id).trans (Category.comp_id _))
      exact (background.recovery.realization.map_comp e.hom background.nu.unitIso.inv).symm.trans
        (congrArg (fun f => background.recovery.realization.map f) hu0)
    change (realization_sphere 62 64).hom ≫
      background.recovery.realization.map (b ≫ e.hom) ≫
      background.recovery.realization.map background.nu.unitIso.inv ≫
      background.recovery.nuRealizationIso.hom.app SphereSpectrum = theta5
    calc
      _ = (realization_sphere 62 64).hom ≫ background.recovery.realization.map b ≫
          (background.recovery.realization.map e.hom ≫
            background.recovery.realization.map background.nu.unitIso.inv) ≫
          background.recovery.nuRealizationIso.hom.app SphereSpectrum := by
        rw [Functor.map_comp]
        simp (config := { congrConsts := false }) only [Category.assoc]
      _ = _ := by rw [hu]; exact hr

/-- The prescribed realization lift, transported by the specified ν-unit isomorphism.
The same classical θ₅ and the same prescribed witness are retained. -/
public theorem theta5_lift :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum),
    Theta5Detected background a ∧ realizeSphere 62 64 a = theta5 := absorbedTheta5Lift


public theorem theta5_detected_exists :
  ∃ a : BiHom 62 64 (S_0_0 : SyntheticSpectrum), Theta5Detected background a := by
  obtain ⟨a, ha, _⟩ := theta5_lift
  exact ⟨a, ha⟩

end KIP126.Literature.Standard
end
