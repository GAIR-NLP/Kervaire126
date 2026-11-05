module
public import KIP126.AdamsSynthetic.Completed.SpectrumScope.Basic

/-! The general Adams objects are bounded below and finite mod-two type by
their input conditions, the selected connective instances, and integer suspension.
Their actual Adams filtration is complete, has finite finite-stage quotients,
and is separated, using the specified completeness, quotient-finiteness
and separation comparisons for these towers. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Integer suspension changes the homotopy degree by its negative. -/
private def homotopyShiftEquiv (X : Spectrum) (n d : ℤ) :
    HomotopyGroup d ((shiftFunctor Spectrum n).obj X) ≃ HomotopyGroup (d-n) X := by
  let E := shiftEquiv' Spectrum (-n) n (by omega)
  let e := (shiftFunctorAdd' Spectrum d (-n) (d-n) (by omega)).app SphereSpectrum
  exact (E.toAdjunction.homEquiv (Sphere (C := Spectrum) d) X).symm.trans
    (Iso.homCongr e.symm (Iso.refl X))

private theorem isBoundedBelow_shift (X : Spectrum) (hX : IsBoundedBelow X) (n : ℤ) :
    IsBoundedBelow ((shiftFunctor Spectrum n).obj X) := by
  obtain ⟨b,hb⟩ := hX
  refine ⟨b+n, ?_⟩
  intro d hd
  letI := hb (d-n) (by omega)
  exact (homotopyShiftEquiv X n d).subsingleton

private def homologyShiftIso (X : Spectrum) (n : ℤ) :
    coefficients.object ⊗ (shiftFunctor Spectrum n).obj X ≅
      (shiftFunctor Spectrum n).obj (coefficients.object ⊗ X) := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift coefficients.object
  exact (β_ coefficients.object ((shiftFunctor Spectrum n).obj X)) ≪≫
    ((tensorRight coefficients.object).commShiftIso n).app X ≪≫
    (shiftFunctor Spectrum n).mapIso (β_ coefficients.object X).symm

private theorem isFiniteModTwoType_shift (X : Spectrum)
    (hX : IsFiniteModTwoType coefficients X) (n : ℤ) :
    IsFiniteModTwoType coefficients ((shiftFunctor Spectrum n).obj X) := by
  intro d
  let e := (Iso.homCongr (Iso.refl (Sphere (C := Spectrum) d))
    (homologyShiftIso X n)).trans
      (homotopyShiftEquiv (coefficients.object ⊗ X) n d)
  exact e.finite_iff.mpr (hX (d-n))

private theorem boundedBelowFiniteModTwoType_shift (X : Spectrum)
    (hX : IsBoundedBelowFiniteModTwoType coefficients X) (n : ℤ) :
    IsBoundedBelowFiniteModTwoType coefficients ((shiftFunctor Spectrum n).obj X) :=
  ⟨isBoundedBelow_shift X hX.1 n, isFiniteModTwoType_shift X hX.2 n⟩

/-- The general object expressions retain exactly their supplied scope, with
selected objects obtained from the three connective finite-type instances. -/
private theorem adamsObject_scope (X : AdamsObject) :
    IsBoundedBelowFiniteModTwoType coefficients (X.obj auxiliary) := by
  induction X with
  | selected X =>
    induction X with
    | sphere => exact sphere_isPaperSpectrum.isBoundedBelowFiniteModTwoType
    | nuCofiber => exact nuCofiber_isPaperSpectrum.isBoundedBelowFiniteModTwoType
    | detector => exact detector_isPaperSpectrum.isBoundedBelowFiniteModTwoType
    | shift n X ih => exact boundedBelowFiniteModTwoType_shift (X.obj auxiliary) ih n
  | spectrum X hX => exact hX
  | shift n X ih => exact boundedBelowFiniteModTwoType_shift (X.obj auxiliary) ih n

public theorem classicalObject_boundedBelow (X : AdamsObject) :
    ∃ b : ℤ, ∀ d : ℤ, d < b → Subsingleton (HomotopyGroup d (X.obj auxiliary)) :=
  (adamsObject_scope X).1
/-- Finite type refers to HF₂ homology in each degree, not finite cell count. -/
public theorem classicalObject_finite_modTwoHomology (X : AdamsObject) (d : ℤ) :
    Finite (ModTwoHomology coefficients d (X.obj auxiliary)) :=
  (adamsObject_scope X).2 d
public theorem classical_filtration_complete (X : AdamsObject) (d : ℤ) :
    Nonempty (Filtration.CompletionWitness (classicalTower.tower (X.obj auxiliary)).filtration d) := by sorry
public theorem classical_filtration_quotient_finite (X : AdamsObject) (d : ℤ) (n : ℕ) :
    Finite (HomotopyGroup d (X.obj auxiliary) ⧸
      (classicalTower.tower (X.obj auxiliary)).filtrationSubmodule n d) := by sorry
public theorem classical_filtration_separated (X : AdamsObject) (d : ℤ)
    (a : HomotopyGroup d (X.obj auxiliary))
    (ha : ∀ n : ℕ, a ∈ (classicalTower.tower (X.obj auxiliary)).filtrationSubmodule n d) : a = 0 := by
  classical
  let T := classicalTower.tower (X.obj auxiliary)
  let A : GradedObject ℤ (ModuleCat.{0} ℤ) :=
    fun e => ModuleCat.of ℤ (HomotopyGroup e (X.obj auxiliary))
  let F : Filtration A := T.filtration
  let hc := Classical.choice (classical_filtration_complete X d)
  have heq : elementMap a =
      (0 : ModuleCat.of ℤ (ULift.{0} ℤ) ⟶ AbstractAdamsTower.homotopy (X.obj auxiliary) d) := by
    apply hc.isLimit.hom_ext
    intro n
    have hn : a ∈ T.filtrationSubmodule n d :=
      (T.filtrationSubmodule_antitone d (Int.self_le_toNat n)) (ha n.toNat)
    have hmem : a ∈ ModuleCat.subobjectModule _ (F.F n d) := by
      simpa only [F, A, AbstractAdamsTower.homotopy, AbstractAdamsTower.filtration,
        OrderIso.apply_symm_apply] using hn
    change ∃ b, (F.F n d).arrow.hom b = a at hmem
    obtain ⟨b, hb⟩ := hmem
    have hproj : F.quotientProjection n d a = 0 := by
      rw [← hb]
      exact ConcreteCategory.congr_hom (cokernel.condition (F.F n d).arrow) b
    rw [zero_comp]
    ext z
    change F.quotientProjection n d (z.down • a) = 0
    rw [map_zsmul, hproj]
    exact zsmul_zero z.down
  have h := ConcreteCategory.congr_hom heq (ULift.up (1 : ℤ))
  change (1 : ℤ) • a = 0 at h
  simpa only [one_smul] using h
end
end KIP126.AdamsSynthetic.Completed
