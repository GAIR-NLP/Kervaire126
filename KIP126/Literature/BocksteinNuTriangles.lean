module
import KIP126.AdamsSynthetic.Completed.Filtration
/-! Relative ν triangles for positive intervals in the classical coefficient
Adams tower, from ν short-exactness and filtration, with first arrow obtained
by inverse rotation.
-/
@[expose] section
namespace KIP126.Literature.Standard.Internal.NuRelativeTriangles
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed KIP126.Classical.Adams
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
private theorem factorization_zero_on_homology
    {X Y : Spectrum} {n : ℕ} {f : X ⟶ Y}
    (h : AdamsMapFactorization coefficients n f) :
    ZeroOnModTwoHomology coefficients f := by
  cases h with
  | single f hf => exact hf
  | prepend f g hf hg =>
      intro i x
      change x ≫ (coefficients.object ◁ (f ≫ g)) = 0
      rw [whiskerLeft_comp, ← Category.assoc]
      change modTwoHomologyMap coefficients f i x ≫ _ = 0
      rw [hf i x, zero_comp]

private theorem zero_on_homology_shift
    {X Y : Spectrum} (f : X ⟶ Y) (k : ℤ)
    (hf : ZeroOnModTwoHomology coefficients f) :
    ZeroOnModTwoHomology coefficients
      ((shiftFunctor Spectrum k).map f) := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  let e := (BraidedCategory.tensorLeftIsoTensorRight coefficients.object).symm
  letI := Functor.CommShift.ofIso e ℤ
  letI := Functor.CommShift.ofIso_compatibility e ℤ
  let F := tensorLeft coefficients.object
  let S := shiftFunctor Spectrum k
  intro n x
  let eS : Sphere (C := Spectrum) n ≅ S.obj (Sphere (n-k)) :=
    (shiftFunctorAdd' Spectrum (n-k) k n (by omega)).app SphereSpectrum
  let b : Sphere (C := Spectrum) (n-k) ⟶ F.obj X :=
    S.preimage (eS.inv ≫ x ≫ (F.commShiftIso k).hom.app X)
  have hb : S.map b = eS.inv ≫ x ≫ (F.commShiftIso k).hom.app X :=
    S.map_preimage _
  have hz : b ≫ F.map f = 0 := hf (n-k) b
  have hs : S.map b ≫ S.map (F.map f) = 0 := by
    rw [← Functor.map_comp, hz, Functor.map_zero]
  rw [hb] at hs
  simp only [Category.assoc] at hs
  rw [← F.commShiftIso_hom_naturality f k] at hs
  change x ≫ F.map (S.map f) = 0
  apply (cancel_mono ((F.commShiftIso k).hom.app Y)).mp
  rw [zero_comp]
  apply (cancel_epi eS.inv).mp
  rw [comp_zero]
  simpa only [Category.assoc] using hs

private theorem zero_on_homology_neg
    {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ZeroOnModTwoHomology coefficients f) :
    ZeroOnModTwoHomology coefficients (-f) := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  let e := (BraidedCategory.tensorLeftIsoTensorRight coefficients.object).symm
  letI := Functor.CommShift.ofIso e ℤ
  letI := Functor.CommShift.ofIso_compatibility e ℤ
  letI := Functor.isTriangulated_of_iso e
  let F := tensorLeft coefficients.object
  intro n x
  have hz : x ≫ F.map f = 0 := hf n x
  change x ≫ F.map (-f) = 0
  rw [Functor.map_neg, Preadditive.comp_neg, hz, neg_zero]

private theorem homology_short_exact_of_boundary_zero
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hz : ZeroOnModTwoHomology coefficients T.mor₃) :
    HomologyShortExact coefficients T := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  letI := closedBackground.tensorExact coefficients.object
  let e := (BraidedCategory.tensorLeftIsoTensorRight coefficients.object).symm
  letI := Functor.CommShift.ofIso e ℤ
  letI := Functor.CommShift.ofIso_compatibility e ℤ
  letI := Functor.isTriangulated_of_iso e
  let F := tensorLeft coefficients.object
  let U := F.mapTriangle.obj T
  have hU : U ∈ distTriang Spectrum := F.map_distinguished T hT
  have hu (n : ℤ) (a : HomotopyGroup n U.obj₃) : a ≫ U.mor₃ = 0 := by
    change a ≫ F.map T.mor₃ ≫ _ = 0
    change a ≫ (coefficients.object ◁ T.mor₃) ≫ _ = 0
    have hh : a ≫ (coefficients.object ◁ T.mor₃) = 0 := hz n a
    rw [← Category.assoc, hh, zero_comp]
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a-b) ≫ U.mor₁ = 0 := by
      change a ≫ U.mor₁ = b ≫ U.mor₁ at hab
      rw [Preadditive.sub_comp, hab, sub_self]
    let S := shiftFunctor Spectrum (1 : ℤ)
    have hh : S.map (a-b) ≫ S.map U.mor₁ = 0 := by
      rw [← Functor.map_comp, hab', Functor.map_zero]
    obtain ⟨d, hd⟩ := U.coyoneda_exact₁ hU (S.map (a-b)) hh
    let eS : Sphere (C := Spectrum) (n+1) ≅ S.obj (Sphere n) :=
      (shiftFunctorAdd' Spectrum n 1 (n+1) rfl).app SphereSpectrum
    have hz' : (eS.hom ≫ d) ≫ U.mor₃ = 0 := hu (n+1) _
    have hd0 : d ≫ U.mor₃ = 0 := (cancel_epi eS.hom).mp
      (by simpa only [Category.assoc, comp_zero] using hz')
    have hs0 : S.map (a-b) = 0 := hd.trans hd0
    have hab0 : a-b = 0 := S.map_injective
      (by simpa only [Functor.map_zero] using hs0)
    exact sub_eq_zero.mp hab0
  · intro a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := U.coyoneda_exact₂ hU a ha
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      change (b ≫ U.mor₁) ≫ U.mor₂ = 0
      rw [Category.assoc, comp_distTriang_mor_zero₁₂ U hU, comp_zero]
  · intro a
    obtain ⟨b, hb⟩ := U.coyoneda_exact₃ hU a (hu n a)
    exact ⟨b, hb.symm⟩



private def unitAt (A : Spectrum) : A ⟶ coefficients.object ⊗ A :=
  (λ_ A).inv ≫ coefficients.unit ▷ A

private theorem unitAt_natural {A B : Spectrum} (f : A ⟶ B) :
    f ≫ unitAt B = unitAt A ≫ coefficients.object ◁ f := by
  simp only [unitAt, ← Category.assoc, leftUnitor_inv_naturality]
  simp only [Category.assoc, whisker_exchange]

/-- Every actual coefficient-tower step factors through the fixed first
stage on its target, by exactness and the SAME coefficient unit. -/
private theorem step_filtration_one {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℕ) :
    MapFiltrationAtLeast classicalTower (T.map (Nat.le_succ s)) 1 := by
  let U := classicalTower.tower (T.stage s)
  let f := T.map (Nat.le_succ s)
  have hf : f ≫ unitAt (T.stage s) = 0 := by
    change f ≫ ((λ_ (T.stage s)).inv ≫ coefficients.unit ▷ T.stage s) = 0
    have hcomp : f ≫ HasFunctorialCofiber.cofibι f = 0 :=
      comp_distTriang_mor_zero₁₂ _ (HasFunctorialCofiber.cofib_distinguished f)
    rw [←T.layer_unit s, ←Category.assoc]
    change (f ≫ HasFunctorialCofiber.cofibι f) ≫ _ = 0
    rw [hcomp, zero_comp]
  have hz : (f ≫ U.zeroIso.inv) ≫
      HasFunctorialCofiber.cofibι (U.map (Nat.le_succ 0)) = 0 := by
    apply (cancel_mono (U.layerIso 0).hom).mp
    rw [Category.assoc, zero_comp, U.layer_unit 0]
    change (f ≫ U.zeroIso.inv) ≫ unitAt (U.stage 0) = 0
    rw [Category.assoc, unitAt_natural, ←Category.assoc, hf, zero_comp]
  obtain ⟨a,ha⟩ := Triangle.coyoneda_exact₂ _
    (HasFunctorialCofiber.cofib_distinguished (U.map (Nat.le_succ 0)))
    (f ≫ U.zeroIso.inv) hz
  change T.stage (s+1) ⟶ U.stage 1 at a
  change f ≫ U.zeroIso.inv = a ≫ U.map (Nat.le_succ 0) at ha
  refine ⟨a, ?_⟩
  change a ≫ (U.map (Nat.zero_le 1) ≫ U.zeroIso.hom) = f
  rw [←Category.assoc, ←ha, Category.assoc, U.zeroIso.inv_hom_id, Category.comp_id]

private theorem composite_filtration_one {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) {s t : ℕ} (h : s < t) :
    MapFiltrationAtLeast classicalTower (T.map (Nat.le_of_lt h)) 1 := by
  obtain ⟨a,ha⟩ := step_filtration_one T s
  refine ⟨T.map (show s+1 ≤ t by omega) ≫ a, ?_⟩
  rw [Category.assoc, ha]
  exact T.map_comp (Nat.le_succ s) (show s+1 ≤ t by omega)

private theorem composite_zero_homology {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) {s t : ℕ} (h : s < t) :
    ZeroOnModTwoHomology coefficients (T.map (Nat.le_of_lt h)) := by
  have hF := (factorization_filtration_iff (T.map (Nat.le_of_lt h)) 1).mpr
    (composite_filtration_one T h)
  exact factorization_zero_on_homology (hF 1 (by decide) (by decide))

private theorem hzero_rotated_short_exact
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hf : ZeroOnModTwoHomology coefficients T.mor₁) :
    HomologyShortExact coefficients T.rotate := by
  apply homology_short_exact_of_boundary_zero T.rotate (rot_of_distTriang T hT)
  exact zero_on_homology_neg _ (zero_on_homology_shift T.mor₁ 1 hf)

/-- Actual source from the ν theorem, preserving νg and νh. -/
private theorem exists_nu_relative_triangle
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hf : ZeroOnModTwoHomology coefficients T.mor₁) :
    ∃ j : (nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))⟦(-1:ℤ)⟧ ⟶ nu.functor.obj T.obj₂,
      Triangle.mk j (nu.functor.map T.mor₂)
        (nu.functor.map T.mor₃ ≫
          (shiftEquiv SyntheticSpectrum (1:ℤ)).counitIso.inv.app
            (nu.functor.obj (T.obj₁⟦(1:ℤ)⟧))) ∈ distTriang SyntheticSpectrum := by
  obtain ⟨δ,hδ⟩ := nu_preserves_triangle T.rotate (rot_of_distTriang T hT)
    (hzero_rotated_short_exact T hT hf)
  refine ⟨-(shiftFunctor SyntheticSpectrum (-1:ℤ)).map δ ≫
    (shiftEquiv SyntheticSpectrum (1:ℤ)).unitIso.inv.app (nu.functor.obj T.obj₂), ?_⟩
  exact inv_rot_of_distTriang _ hδ

private def positiveSourceIso (X : Spectrum) :
    (SyntheticCategory.biShift (0,1)).obj (nu.functor.obj X) ≅
      (nu.functor.obj (X⟦(1:ℤ)⟧))⟦(-1:ℤ)⟧ :=
  (eqToIso (by congr 1) :
    (SyntheticCategory.biShift (0,1)).obj (nu.functor.obj X) ≅
      (SyntheticCategory.biShift ((1,1)+(-1,0))).obj (nu.functor.obj X)) ≪≫
  (SyntheticCategory.biShift_comp (1,1) (-1,0)).symm.app (nu.functor.obj X) ≪≫
    (SyntheticCategory.biShift_compat (-1)).app _ ≪≫
    (shiftFunctor SyntheticSpectrum (-1:ℤ)).mapIso (nu.suspensionIso X).symm

private def relativeThird (T : Triangle Spectrum) :
    nu.functor.obj T.obj₃ ⟶
      ((SyntheticCategory.biShift (0,1)).obj (nu.functor.obj T.obj₁))⟦(1:ℤ)⟧ :=
  nu.functor.map T.mor₃ ≫
    (shiftEquiv SyntheticSpectrum (1:ℤ)).counitIso.inv.app _ ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (positiveSourceIso T.obj₁).inv

/-- A ν-relative triangle in the positive source convention,
with its original νg and specified νh coordinate. -/
private theorem exists_positive_nu_relative_triangle
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hf : ZeroOnModTwoHomology coefficients T.mor₁) :
    ∃ j : (SyntheticCategory.biShift (0,1)).obj (nu.functor.obj T.obj₁) ⟶
        nu.functor.obj T.obj₂,
      Triangle.mk j (nu.functor.map T.mor₂) (relativeThird T) ∈
        distTriang SyntheticSpectrum := by
  obtain ⟨j,hj⟩ := exists_nu_relative_triangle T hT hf
  let e := positiveSourceIso T.obj₁
  refine ⟨e.hom ≫ j, ?_⟩
  apply isomorphic_distinguished _ hj _
  refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp
  · simp
  · change (nu.functor.map T.mor₃ ≫ _ ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map e.inv) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map e.hom = _
    simp only [Category.assoc, ←Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id, Iso.refl_hom, Category.id_comp,
      Triangle.mk_mor₃]

/-- Applies to every positive relative segment of the actual classical
coefficient tower, on an arbitrary spectrum. -/
private theorem exists_adams_relative_triangle (X : Spectrum) {s t : ℕ} (h : s < t) :
    let T := classicalTower.tower X
    let f := T.map (Nat.le_of_lt h)
    ∃ j : (SyntheticCategory.biShift (0,1)).obj (nu.functor.obj (T.stage t)) ⟶
        nu.functor.obj (T.stage s),
      Triangle.mk j (nu.functor.map (HasFunctorialCofiber.cofibι f))
        (relativeThird (Triangle.mk f (HasFunctorialCofiber.cofibι f)
          (HasFunctorialCofiber.cofibδ f))) ∈ distTriang SyntheticSpectrum := by
  exact exists_positive_nu_relative_triangle _
    (HasFunctorialCofiber.cofib_distinguished _)
    (composite_zero_homology (classicalTower.tower X) h)

end
end KIP126.Literature.Standard.Internal.NuRelativeTriangles
