module

import all KIP126.ProofTools.CrossingCounterexample.Matrix
import all KIP126.ProofTools.CrossingCounterexample.H0Action
import all KIP126.ProofTools.CrossingCounterexample.Moore
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.GeneralizedMahowald.ExtensionImage
import all KIP126.ProofTools.MahowaldLeibniz.Filtration

/-! The length-zero windows for the actual crossing counterexample. -/

@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

private abbrev mooreMiddleInclusion : mooreFour ⟶ candidateSpectrum :=
  biprod.inl ≫ biprod.inr

private theorem candidate_first_matrix_image (m w : ℤ)
    (a : BiHom m w ((quotientNu 1).obj candidateSpectrum)) :
    a ≫ (quotientNu 1).map matrixMap =
      a ≫ (quotientNu 1).map (biprod.fst : candidateSpectrum ⟶ S) ≫
        (quotientNu 1).map bottom ≫ (quotientNu 1).map mooreMiddleInclusion := by
  let F := quotientNu 1
  letI : F.Additive := quotientNu_additive 1 (by decide)
  have hz₂ : (2 : ℕ) • (a ≫ F.map (biprod.fst : candidateSpectrum ⟶ S)) = 0 :=
    first_sphere_quotient_two m w _
  have hz₄ : (4 : ℕ) • (a ≫ F.map (biprod.snd ≫ biprod.snd : candidateSpectrum ⟶ S)) = 0 := by
    have h := congrArg (fun z => (2 : ℕ) • z)
      (first_sphere_quotient_two m w
        (a ≫ F.map (biprod.snd ≫ biprod.snd : candidateSpectrum ⟶ S)))
    rw [smul_smul, smul_zero] at h
    exact h
  have hz₄' : (4 : ℕ) • (a ≫ F.map biprod.snd ≫ F.map biprod.snd ≫
      F.map (biprod.inl : S ⟶ candidateSpectrum)) = 0 := by
    have h := congrArg (fun z => z ≫ F.map (biprod.inl : S ⟶ candidateSpectrum)) hz₄
    simpa only [Preadditive.nsmul_comp, Functor.map_comp, Category.assoc, zero_comp] using h
  have hz₂' : (2 : ℕ) • (a ≫ F.map biprod.fst ≫ F.map
      (biprod.inr : S ⟶ mooreFour ⊞ S) ≫
        F.map (biprod.inr : mooreFour ⊞ S ⟶ candidateSpectrum)) = 0 := by
    have h := congrArg (fun z => z ≫ F.map (biprod.inr : S ⟶ mooreFour ⊞ S) ≫
      F.map (biprod.inr : mooreFour ⊞ S ⟶ candidateSpectrum)) hz₂
    simpa only [Preadditive.nsmul_comp, Category.assoc, zero_comp] using h
  change a ≫ F.map matrixMap = a ≫ F.map _ ≫ F.map _ ≫ F.map _
  simp only [matrixMap, biprod.lift_eq, four, mooreMiddleInclusion,
    Functor.map_add, Functor.map_comp, Functor.map_nsmul,
    Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
    Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id] at ⊢
  erw [hz₄', hz₂', zero_add, add_zero]

private theorem candidate_classical_matrix_image (s t : ℤ)
    (x : Ambient background candidateAdamsObject (s,t)) :
    (background.classical.map matrixMap).pageMap 2 (s,t) x =
      (background.classical.map mooreMiddleInclusion).pageMap 2 (s,t)
        ((background.classical.map bottom).pageMap 2 (s,t)
          ((background.classical.map (biprod.fst : candidateSpectrum ⟶ S)).pageMap 2 (s,t) x)) := by
  apply native_first_label_injective candidateAdamsObject s t
  let x₁ := (background.classical.map (biprod.fst : candidateSpectrum ⟶ S)).pageMap 2 (s,t) x
  let x₂ := (background.classical.map bottom).pageMap 2 (s,t) x₁
  have h₁ := native_first_label_natural candidateAdamsObject .sphere biprod.fst s t x
  have h₂ := native_first_label_natural .sphere mooreAdamsObject bottom s t x₁
  have h₃ := native_first_label_natural mooreAdamsObject candidateAdamsObject
    mooreMiddleInclusion s t x₂
  have hm := native_first_label_natural candidateAdamsObject candidateAdamsObject
    matrixMap s t x
  apply hm.symm.trans
  apply (candidate_first_matrix_image (t-s) t (nativeFirstLabel candidateAdamsObject s t x)).trans
  change nativeFirstLabel candidateAdamsObject s t x ≫ XModLambdaN.map
    (background.nu.functor.map biprod.fst) 1 ≫ XModLambdaN.map
    (background.nu.functor.map bottom) 1 ≫ XModLambdaN.map
    (background.nu.functor.map mooreMiddleInclusion) 1 = _
  rw [← Category.assoc, ← Category.assoc, h₁]
  exact (congrArg (fun z => z ≫ XModLambdaN.map
    (background.nu.functor.map mooreMiddleInclusion) 1) h₂).trans h₃


private theorem classical_boundaries_map
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (b : ℤ) (p : Bidegree) (x : (background.classical.obj (X.obj background.auxiliary)).Page 2 p)
    (hx : x ∈ boundaries background X b p) :
    (background.classical.map f).pageMap 2 p x ∈ boundaries background Y b p := by
  let F := (background.classical.map f).toSSDataMorphism
  let n : WithTop ℕ := ↑(b-1).toNat
  let DX := (background.classical.obj (X.obj background.auxiliary)).ssData p
  let DY := (background.classical.obj (Y.obj background.auxiliary)).ssData p
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨g, hg⟩ := F.preserves_B p n
  refine ⟨g z, ?_⟩
  have hinc : g ≫ Subobject.ofLE (DY.B n) (DY.Z 0)
      ((DY.B_le_Z n).trans (DY.Z_anti bot_le)) =
      Subobject.ofLE (DX.B n) (DX.Z 0) ((DX.B_le_Z n).trans (DX.Z_anti bot_le)) ≫
        F.cycleMap p 0 := by
    apply (cancel_mono (DY.Z 0).arrow).mp
    dsimp only [DX, DY]
    simp only [Category.assoc, Subobject.ofLE_arrow, F.cycleMap_arrow,
      Subobject.ofLE_arrow_assoc]
    exact hg
  have hraw := congrArg (fun k => k ≫ DY.pageπ 0) hinc
  rw [Category.assoc, Category.assoc, ← F.pageπ_pageMap] at hraw
  have hx0 : (↑(2-(background.classical.obj (X.obj background.auxiliary)).r₀).toNat : WithTop ℕ) = 0 := by
    rw [background.classical.firstPage]
    rfl
  have hy0 : (↑(2-(background.classical.obj (Y.obj background.auxiliary)).r₀).toNat : WithTop ℕ) = 0 := by
    rw [background.classical.firstPage]
    rfl
  have transport (i j : WithTop ℕ) (hi : i=0) (hj : j=0) :
      eqToHom (congrArg DX.page hi.symm) ≫
        (F.pageMap p i ≫ eqToHom (congrArg DY.page (hi.trans hj.symm))) =
      F.pageMap p 0 ≫ eqToHom (congrArg DY.page hj.symm) := by
    subst i; subst j
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have hmap : g ≫ boundaryLabel background Y n p =
      boundaryLabel background X n p ≫ (background.classical.map f).pageMap 2 p := by
    unfold boundaryLabel
    change g ≫ (Subobject.ofLE (DY.B n) (DY.Z 0) _ ≫ DY.pageπ 0 ≫
      eqToHom (congrArg DY.page hy0.symm)) =
      (Subobject.ofLE (DX.B n) (DX.Z 0) _ ≫ DX.pageπ 0 ≫
        eqToHom (congrArg DX.page hx0.symm)) ≫
        (F.pageMap p _ ≫ eqToHom (congrArg DY.page (hx0.trans hy0.symm)))
    simp only [Category.assoc]
    rw [transport _ _ hx0 hy0]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ eqToHom (congrArg DY.page hy0.symm)) hraw
  exact ConcreteCategory.congr_hom hmap z

private theorem weight_label_bijective (X : AdamsObject) (s t w : ℤ) (hw : w ≤ t) :
    Function.Bijective (nuWeightLabel background X s t w hw) := by
  let zeroIso := SyntheticCategory.biShift_zero.app
    (background.nu.functor.obj (X.obj background.auxiliary))
  let zeroPage := familyPageIso zeroIso 2 (s,t,t-(t-w).toNat)
  have hzero : Function.Bijective zeroPage.hom := ConcreteCategory.bijective_of_isIso _
  change Function.Bijective (fun x => nuWeightLabel background X s t w hw x)
  dsimp only [nuWeightLabel, regradeE2, targetNuLabel]
  apply Function.Bijective.comp
  · exact ConcreteCategory.bijective_of_isIso _
  · apply Function.Bijective.comp
    · exact hzero
    · change Function.Bijective
        ((fun z : (background.family.obj ((SyntheticCategory.biShift (0,0)).obj
            (background.nu.functor.obj (X.obj background.auxiliary)))).E₂
              (s,t,t+0-(t-w).toNat) =>
          Eq.mp (by simp only [add_zero]) z) ∘
            (background.comparison.nuE2 X 0 s t (t-w).toNat))
      exact (Equiv.cast _).bijective.comp
        (background.comparison.nuE2 X 0 s t (t-w).toNat).bijective

private theorem candidate_zero_length_target_in_range (r : ℕ) (s t : ℤ)
    (x : Ambient background candidateAdamsObject (s,t))
    (y : Ambient background candidateAdamsObject (s+0,t+0))
    (W : FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
      matrixMap r 0 s t x y) :
    ∃ x' : Ambient background candidateAdamsObject (s+0,t+0),
      (background.classical.map matrixMap).pageMap 2 (s+0,t+0) x' = y := by
  have H := zero_extension_map_e2_bottom_target candidateAdamsObject candidateAdamsObject
    matrixMap r s t x y W
  rw [matrix_normalized_map, ← family_page_comp, ModuleCat.comp_apply] at H
  obtain ⟨x', hx'⟩ := (weight_label_bijective candidateAdamsObject (s+0) (t+0) (t+0)
    le_rfl).surjective (familyPageMap background.family matrixSourceIso.hom 2 (s+0,t+0,t+0)
      (regradeE2 (by have := W.length_lower; ext <;> dsimp <;> omega)
        (infiniteSourceForExtension background candidateAdamsObject candidateAdamsObject
          matrixMap s t x)))
  refine ⟨x', (weight_label_bijective candidateAdamsObject (s+0) (t+0) (t+0) le_rfl).injective ?_⟩
  have hn := KIP126.ProofTools.Internal.MahowaldLeibniz.weightLabelNatural
    candidateAdamsObject candidateAdamsObject matrixMap (s+0) (t+0) (t+0) le_rfl x'
  apply hn.symm.trans
  change familyPageMap background.family (background.nu.functor.map matrixMap) 2
    (s+0,t+0,t+0) (nuWeightLabel background candidateAdamsObject (s+0) (t+0) (t+0) le_rfl x') = _
  rw [hx']
  exact H
private theorem candidate_matrix_degree_two_boundary
    (x : Ambient background candidateAdamsObject (2,2)) :
    (background.classical.map matrixMap).pageMap 2 (2,2) x ∈
      boundaries background candidateAdamsObject 2 (2,2) := by
  rw [candidate_classical_matrix_image]
  exact classical_boundaries_map mooreAdamsObject candidateAdamsObject mooreMiddleInclusion
    2 (2,2) _ (moore_bottom_degree_two_boundary _)

private theorem candidate_matrix_degree_three_boundary
    (x : Ambient background candidateAdamsObject (3,3)) :
    (background.classical.map matrixMap).pageMap 2 (3,3) x ∈
      boundaries background candidateAdamsObject 3 (3,3) := by
  rw [candidate_classical_matrix_image]
  exact classical_boundaries_map mooreAdamsObject candidateAdamsObject mooreMiddleInclusion
    3 (3,3) _ (moore_bottom_degree_three_boundary _)

private theorem candidate_zero_length_two_boundary
    (x : Ambient background candidateAdamsObject (2,2))
    (y : Ambient background candidateAdamsObject (2+0,2+0))
    (W : FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
      matrixMap 3 0 2 2 x y) :
    y ∈ boundaries background candidateAdamsObject 2 (2,2) := by
  obtain ⟨x', hx'⟩ := candidate_zero_length_target_in_range 3 2 2 x y W
  rw [← hx']
  exact candidate_matrix_degree_two_boundary x'

private theorem candidate_zero_length_three_boundary
    (x : Ambient background candidateAdamsObject (3,3))
    (y : Ambient background candidateAdamsObject (3+0,3+0))
    (W : FiniteExtensionWitness background candidateAdamsObject candidateAdamsObject
      matrixMap 2 0 3 3 x y) :
    y ∈ boundaries background candidateAdamsObject 3 (3,3) := by
  obtain ⟨x', hx'⟩ := candidate_zero_length_target_in_range 2 3 3 x y W
  rw [← hx']
  exact candidate_matrix_degree_three_boundary x'

end
end KIP126.ProofTools.Internal.CrossingCounterexample
