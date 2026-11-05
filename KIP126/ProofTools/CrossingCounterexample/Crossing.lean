module

import all KIP126.ProofTools.CrossingCounterexample.Base
import all KIP126.ProofTools.CrossingCounterexample.H0Action
import all KIP126.ProofTools.CrossingCounterexample.Matrix
import all KIP126.ProofTools.GeneralizedMahowald.RotatedNuPremises
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingLift

/-! Actual filtration and infinity-class assembly for the crossing counterexample.
Every correction is made in the homotopy group of the specified synthetic object.
-/
@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

section ActualFiltration
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- The exact image of a filtered representative supplies the actual infinity
classes. Nonvanishing is checked in the full target associated graded group. -/
private theorem actual_extension_of_filtered_image
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ) (hn : 0 ≤ n)
    (a : BiHom p.1 p.2 X) (ha : a ∈ P.filtrationSubmodule X s p)
    (himage : a ≫ g ∈ P.filtrationSubmodule Y (s+n) p)
    (hnonzero : a ≫ g ∉ P.filtrationSubmodule Y (s+n+1) p) :
    ∃ (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
      (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty),
      y ≠ 0 ∧ TowerExtensionEquation M p s n x y := by
  obtain ⟨ar, har⟩ := filtration_representative_exists P X p s a ha
  obtain ⟨br, hbr⟩ := filtration_representative_exists P Y p (s+n) (a ≫ g) himage
  let x := (infinityGradedIso cx p s).inv ((P.filtration X).toAssociatedGraded s p ar)
  let y := (infinityGradedIso cy p (s+n)).inv
    ((P.filtration Y).toAssociatedGraded (s+n) p br)
  have hx : (P.filtration X).toAssociatedGraded s p ar =
      (infinityGradedIso cx p s).hom x :=
    ((infinityGradedIso cx p s).toLinearEquiv.apply_symm_apply _).symm
  have hy : (P.filtration Y).toAssociatedGraded (s+n) p br =
      (infinityGradedIso cy p (s+n)).hom y :=
    ((infinityGradedIso cy p (s+n)).toLinearEquiv.apply_symm_apply _).symm
  refine ⟨x, y, ?_, (tower_extension_iff M p s n x y).mpr
    ⟨hn, ar, br, by rw [har, hbr], hx, hy⟩⟩
  intro hz
  have hg : (P.filtration Y).toAssociatedGraded (s+n) p br = 0 := by
    rw [hy, hz, map_zero]
  have hm := ((P.filtration Y).toAssociatedGraded_eq_zero_iff (s+n) p br).mp hg
  rw [hbr] at hm
  apply hnonzero
  simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply] using hm

/-- A representative with the same leading source and vanishing leading
image proves nonessentiality in the full target. -/
private theorem actual_not_essential_of_correction
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (hcorrect : ∀ a : BiHom p.1 p.2 X,
      a ∈ P.filtrationSubmodule X s p →
      a ≫ g ∈ P.filtrationSubmodule Y (s+n) p →
      ∃ b : BiHom p.1 p.2 X,
        b ∈ P.filtrationSubmodule X s p ∧
        a-b ∈ P.filtrationSubmodule X (s+1) p ∧
        b ≫ g ∈ P.filtrationSubmodule Y (s+n+1) p)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty) :
    ¬ TowerEssentialExtension M p s n x y := by
  intro hess
  obtain ⟨hn,ar,br,hab,hax,hby⟩ := (tower_extension_iff M p s n x y).mp hess.1
  let a := ((P.filtration X).F s p).arrow ar
  have ha : a ∈ P.filtrationSubmodule X s p := by
    have h : a ∈ ModuleCat.subobjectModule _ ((P.filtration X).F s p) := ⟨ar,rfl⟩
    simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply] using h
  have hfa : a ≫ g ∈ P.filtrationSubmodule Y (s+n) p := by
    have h : a ≫ g ∈ ModuleCat.subobjectModule _ ((P.filtration Y).F (s+n) p) :=
      ⟨br,hab.symm⟩
    simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply] using h
  obtain ⟨b,hb,hdiff,hzero⟩ := hcorrect a ha hfa
  obtain ⟨ar',har'⟩ := filtration_representative_exists P X p s b hb
  have hzero' : b ≫ g ∈ P.filtrationSubmodule Y (s+n) p :=
    P.filtrationSubmodule_antitone Y p (by omega) hzero
  obtain ⟨br',hbr'⟩ := filtration_representative_exists P Y p (s+n) (b≫g) hzero'
  have hs : (P.filtration X).toAssociatedGraded s p ar' =
      (infinityGradedIso cx p s).hom x := by
    have hd : ((P.filtration X).F s p).arrow ar -
        ((P.filtration X).F s p).arrow ar' ∈
        ModuleCat.subobjectModule _ ((P.filtration X).F (s+1) p) := by
      rw [har']
      simpa only [a, SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply]
        using hdiff
    exact ((element_grade_equal_iff (P.filtration X) s p ar ar').mpr hd).symm.trans hax
  have ht : (P.filtration Y).toAssociatedGraded (s+n) p br' =
      (infinityGradedIso cy p (s+n)).hom 0 := by
    rw [map_zero]
    apply ((P.filtration Y).toAssociatedGraded_eq_zero_iff (s+n) p br').mpr
    rw [hbr']
    simpa only [SyntheticTowerPresentation.filtration, OrderIso.apply_symm_apply]
      using hzero
  have he0 : TowerExtensionEquation M p s n x 0 :=
    (tower_extension_iff M p s n x 0).mpr
      ⟨hn,ar',br',by rw [har',hbr'],hs,ht⟩
  exact ((tower_essential_iff_no_zero M p s n x y hess.1).mp hess) he0

end ActualFiltration

/-- The original range at r=4,n=2,e(f)=0 has exactly three windows. -/
private theorem crossing_windows (a b : ℕ) (ha : 0 < a) (ha2 : a ≤ 4-2)
    (hb : (b:ℤ) ≤ 2-a-(0:ℤ)) :
    (a=1 ∧ b=0) ∨ (a=1 ∧ b=1) ∨ (a=2 ∧ b=0) := by omega

/-- The premise of the original assertion permits zero labels. All cycle,
degree, source-label, target-label and equation premises are retained. -/
private def candidateZeroWitness :
    FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
      matrixMap 4 2 1 1 0 0 :=
  zero_finite_extension_witness _ _ _ _ _ _ _ (by decide)
    (by rw [matrixMap_normalizedExponent]; norm_num)
    (by rw [matrixMap_normalizedExponent]; norm_num)

private theorem candidate_finite_extension :
    FiniteExtension background candidateAdamsObject candidateAdamsObject
      matrixMap 4 2 1 1 0 0 := ⟨candidateZeroWitness⟩

private theorem second_sphere_rho_kernel_filtration
    (a : BiHom 0 2 ((quotientNu 2).obj S))
    (ha : a ≫ (background.quotients.tower (background.nu.functor.obj S)).rho
      1 2 (by decide) = 0) :
    FiltrationAtLeast background.syntheticTower 3 a := by
  obtain ⟨b,hb⟩ := second_sphere_quotient_rho_kernel 0 2 a ha
  have hf : FiltrationAtLeast background.syntheticTower 3 b :=
    shifted_quotient_bottom_filtration .sphere 1 (by decide) (-1) 0 2 b
  have hm := map_preserves_filtration (background.convergentMap
    (.shift (0,-1) (.quotient 1 (.nu .sphere))) (.quotient 2 (.nu .sphere))
    ((background.quotients.tower (background.nu.functor.obj S)).triangle
      (by decide : 0<1) (by decide : 1<2)).lambdaMap) (0,2) 3 b hf
  rwa [hb] at hm

/-- The actual first quotient detects the first sphere coordinate even though
the Moore quotient itself may have additional homotopy classes. -/
private theorem second_sphere_filtration_of_bottom_high
    (a : BiHom 0 2 ((quotientNu 2).obj S))
    (ha : FiltrationAtLeast background.syntheticTower 3 (a ≫ (quotientNu 2).map bottom)) :
    FiltrationAtLeast background.syntheticTower 3 a := by
  let rhoS := (background.quotients.tower (background.nu.functor.obj S)).rho 1 2 (by decide)
  let rhoM := (background.quotients.tower (background.nu.functor.obj mooreFour)).rho
    1 2 (by decide)
  have hf := map_preserves_filtration (background.convergentMap
    (.quotient 2 (.nu mooreAdamsObject)) (.quotient 1 (.nu mooreAdamsObject)) rhoM)
      (0,2) 3 (a ≫ (quotientNu 2).map bottom) ha
  have hz : (a ≫ (quotientNu 2).map bottom) ≫ rhoM = 0 :=
    finite_high_filtration_zero mooreAdamsObject 1 (by decide) 0 2 3 (by decide) _ hf
  have hn := (background.quotients.natural (background.nu.functor.map bottom)).rho_naturality
    (show 1≤2 by decide)
  change rhoS ≫ (quotientNu 1).map bottom = (quotientNu 2).map bottom ≫ rhoM at hn
  have he : (a ≫ rhoS) ≫ (quotientNu 1).map bottom = 0 := by
    rw [Category.assoc, hn, ← Category.assoc, hz]
  have hr : a ≫ rhoS = 0 := by
    apply moore_first_quotient_bottom_injective 0 2
    simpa only [zero_comp] using he
  exact second_sphere_rho_kernel_filtration a hr

/-- Remove the first sphere coordinate from an arbitrary representative.
The difference has filtration three and the corrected image is actually zero. -/
private theorem candidate_length_one_correction
    (a : BiHom 0 2 ((SyntheticObject.quotient 2
      (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap)).obj
        background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower 2 a)
    (himage : FiltrationAtLeast background.syntheticTower 3
      (a ≫ finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 2)) :
    ∃ b, FiltrationAtLeast background.syntheticTower 2 b ∧
      FiltrationAtLeast background.syntheticTower 3 (a-b) ∧
      b ≫ finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 2 = 0 := by
  let A : SyntheticObject (coefficients := background.coefficients) :=
    .quotient 2 (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap)
  let B : SyntheticObject (coefficients := background.coefficients) := .quotient 2 (.nu candidateAdamsObject)
  let f := finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 2
  let I := matrixFiniteCoordinates 2 (by decide)
  let J := candidateQuotientBiprodIso 2 (by decide)
  let c := a ≫ I.hom
  let a₁ := c ≫ biprod.fst
  let a₂ := c ≫ biprod.snd ≫ biprod.fst
  let a₃ := c ≫ biprod.snd ≫ biprod.snd
  have hc : biprod.lift a₁ (biprod.lift a₂ a₃) = c := by
    apply biprod.hom_ext
    · simp [a₁]
    · apply biprod.hom_ext <;> simp [a₂,a₃,Category.assoc]
  have hrec : biprod.lift a₁ (biprod.lift a₂ a₃) ≫ I.inv = a := by
    rw [hc]
    simp [c]
  have hm : (a ≫ f) ≫ J.hom = biprod.lift ((4:ℕ) • a₃)
      (biprod.lift (a₁ ≫ (quotientNu 2).map bottom) ((2:ℕ) • a₁)) := by
    have h := matrix_image 2 (by decide) 0 2 a₁ a₂ a₃
    rw [hrec] at h
    simpa only [Category.assoc] using h
  have hmiddle : (a ≫ f) ≫ (J.hom ≫ biprod.snd ≫ biprod.fst) =
      a₁ ≫ (quotientNu 2).map bottom := by
    have h := congrArg (fun z => z ≫ biprod.snd ≫ biprod.fst) hm
    simpa only [Category.assoc,biprod.lift_snd_assoc,biprod.lift_fst] using h
  have hhigh : FiltrationAtLeast background.syntheticTower 3 a₁ := by
    apply second_sphere_filtration_of_bottom_high
    rw [←hmiddle]
    exact map_preserves_filtration (background.convergentMap B
      (.quotient 2 (.nu mooreAdamsObject)) (J.hom ≫ biprod.snd ≫ biprod.fst))
        (0,2) 3 (a≫f) himage
  let removed := a₁ ≫ biprod.inl ≫ I.inv
  have hremoved : FiltrationAtLeast background.syntheticTower 3 removed :=
    map_preserves_filtration (background.convergentMap
      (.quotient 2 (.nu .sphere)) A (biprod.inl ≫ I.inv)) (0,2) 3 a₁ hhigh
  let b := biprod.lift (0 : BiHom 0 2 ((quotientNu 2).obj S))
    (biprod.lift a₂ a₃) ≫ I.inv
  have hdiff : a-b=removed := by
    apply (cancel_mono I.hom).mp
    simp only [Preadditive.sub_comp, b, removed, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    change c - biprod.lift 0 (biprod.lift a₂ a₃) = a₁ ≫ biprod.inl
    rw [←hc]
    apply biprod.hom_ext
    · simp [Preadditive.sub_comp]
    · apply biprod.hom_ext <;> simp [Preadditive.sub_comp,Category.assoc]
  have hb : FiltrationAtLeast background.syntheticTower 2 b := by
    have hr2 : FiltrationAtLeast background.syntheticTower 2 removed :=
      background.syntheticTower.filtrationSubmodule_antitone _ (0,2) (by decide) hremoved
    have h := (background.syntheticTower.filtrationSubmodule _ 2 (0,2)).sub_mem ha hr2
    simpa only [FiltrationAtLeast,←hdiff,sub_sub_cancel] using h
  refine ⟨b,hb,by rwa [hdiff],?_⟩
  apply (cancel_mono J.hom).mp
  have h := matrix_image 2 (by decide) 0 2 (0 : BiHom 0 2 ((quotientNu 2).obj S)) a₂ a₃
  change b≫f≫J.hom = _ at h
  rw [Category.assoc]
  rw [h]
  simp only [zero_comp,nsmul_zero]
  apply biprod.hom_ext
  · simp only [biprod.lift_fst,zero_comp]
    exact second_sphere_quotient_four 0 2 a₃
  · apply biprod.hom_ext <;> simp

private theorem candidate_length_one_not_essential
    (x : Ambient background candidateAdamsObject (2,2))
    (y : Ambient background candidateAdamsObject (2+1,2+1))
    (W : FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
      matrixMap 3 1 2 2 x y) : ¬ W.Essential := by
  have hcorrect := actual_not_essential_of_correction
    (background.convergentMap
      (.quotient 2 (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap))
      (.quotient 2 (.nu candidateAdamsObject))
      (finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 2))
      (0,2) 2 1 (by
        intro a ha hfa
        obtain ⟨b,hb,hd,hz⟩ := candidate_length_one_correction a ha hfa
        refine ⟨b,hb,hd,?_⟩
        rw [hz]
        exact Submodule.zero_mem _)
  intro hess
  unfold FiniteExtensionWitness.Essential at hess
  have htransport (p : ℤ × ℤ) (hp : p=(0,2)) :
      ∀ (x : ((background.family.obj ((SyntheticObject.quotient 2
          (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap)).obj
            background.nu background.auxiliary)).sequence.ssData (2,p.1+2,p.2)).eInfty)
        (y : ((background.family.obj ((SyntheticObject.quotient 2 (.nu candidateAdamsObject)).obj
          background.nu background.auxiliary)).sequence.ssData (2+1,p.1+(2+1),p.2)).eInfty),
        ¬ TowerEssentialExtension (background.convergentMap
          (.quotient 2 (extensionSourceObject background candidateAdamsObject candidateAdamsObject matrixMap))
          (.quotient 2 (.nu candidateAdamsObject))
          (finiteExtensionMap background candidateAdamsObject candidateAdamsObject matrixMap 2))
          p 2 1 x y := by
    subst p
    exact hcorrect
  exact htransport (2-2,2+normalizedExponent background.classicalTower matrixMap)
    (by rw [matrixMap_normalizedExponent]; norm_num) W.source W.target hess

/-- Exhaust the actual paper definition, with essentiality required only in
the positive-length window and the exact boundary exclusions in the others. -/
private theorem candidate_not_finite_crossing
    (h10 : ∀ (x : Ambient background candidateAdamsObject (2,2))
      (y : Ambient background candidateAdamsObject (2+1,2+1))
      (W : FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
        matrixMap 3 1 2 2 x y), ¬ W.Essential)
    (h11 : ∀ (x : Ambient background candidateAdamsObject (2,2))
      (y : Ambient background candidateAdamsObject (2+0,2+0))
      (_W : FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
        matrixMap 3 0 2 2 x y),
        y ∈ boundaries background candidateAdamsObject 2 (2,2))
    (h20 : ∀ (x : Ambient background candidateAdamsObject (3,3))
      (y : Ambient background candidateAdamsObject (3+0,3+0))
      (_W : FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
        matrixMap 2 0 3 3 x y),
        y ∈ boundaries background candidateAdamsObject 3 (3,3)) :
    ¬ FiniteHasCrossing background candidateAdamsObject candidateAdamsObject
      matrixMap 4 2 1 1 := by
  rintro ⟨a,b,ha,ha2,hb,x,y,W,hess,hboundary⟩
  rw [matrixMap_normalizedExponent] at hb
  rcases crossing_windows a b ha ha2 hb with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact h10 x y W hess
  · apply hboundary
    change y ∈ boundaries background candidateAdamsObject
      (2-normalizedExponent background.classicalTower matrixMap) (2,2)
    simpa only [matrixMap_normalizedExponent, Nat.cast_zero, sub_zero] using h11 x y W
  · apply hboundary
    change y ∈ boundaries background candidateAdamsObject
      (3-normalizedExponent background.classicalTower matrixMap) (3,3)
    simpa only [matrixMap_normalizedExponent, Nat.cast_zero, sub_zero] using h20 x y W

end
end KIP126.ProofTools.Internal.CrossingCounterexample
