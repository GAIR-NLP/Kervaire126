





module


public import KIP126.AdamsSynthetic.Ordinary.Background
public import KIP126.AdamsSynthetic.Source
public import Mathlib.CategoryTheory.Localization.Predicate
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.DerivedSmash
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Replacement.Spectra.Prespectrum.Replacement.Cubical.Proofs
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Replacement.Spectra.Prespectrum.Replacement.Cubical.Good.Proofs
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.PointSetRecognition
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.AdamsSequence
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.MilnorComparison
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.SurvivalTransport

/-! Source recognition for the selected background objects.
The ordinary stable source and HF₂ completion are kept distinct. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Ordinary
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.Classical.Adams
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Recognition of the fixed ordinary category, sphere, integer homotopy,
HF₂ object, coordinate and normalized actual point-set unit. -/
public def sourceComparison : ClassicalSourceRecognition Spectrum coefficients := by
  sorry

/-- Tensor comparison on good suspension-spectrum generators. -/
public def sourceGeneratorTensorRecognition :
    ClassicalSourceGeneratorTensorRecognition sourceComparison := by
  sorry

/-- Actual mapping-cone comparison, including its inclusion and boundary. -/
public def sourceCofiberRecognition :
    ClassicalSourceCofiberRecognition sourceComparison := by
  sorry

set_option backward.privateInPublic true in
private theorem sourceReplacementNonempty : Nonempty ClassicalSourceReplacementData := by
  exact ⟨{
    replacement := KIP126.AdamsSynthetic.Source.Prespectrum.cubicalReplacementFunctor
    comparison := KIP126.AdamsSynthetic.Source.Prespectrum.cubicalReplacementComparison
    good X := KIP126.AdamsSynthetic.Source.Prespectrum.cubicalReplacementFunctor_level_isGood X
    stable X := KIP126.AdamsSynthetic.Source.Prespectrum.cubicalReplacementComparison_stableEquivalence X }⟩

set_option backward.privateInPublic true in
/-- A levelwise good replacement of the same actual prespectra, with a
specified natural stable equivalence to the identity. -/
public def sourceReplacement : ClassicalSourceReplacementData :=
  Classical.choice sourceReplacementNonempty

/-- Recognition of the fixed tensor on all actual prespectra by their
replacement followed by the actual even/odd diagonal smash. -/
public def sourceDerivedSmashRecognition :
    ClassicalSourceDerivedSmashRecognition sourceComparison sourceReplacement := by
  sorry

universe u v

open KIP126.AdamsSynthetic.Source CategoryTheory.MonoidalCategory in
/-- The full natural tensor comparison reflects preservation of actual
stable homotopy groups. Its construction is independent of this flatness result. -/
private theorem sourceReplacementFlatness_of_recognition
    {C : Type u} [StableHomotopyCategory.{u,v} C] {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (P : SourceReplacementData)
    (D : SourceDerivedSmashRecognition R P) : SourceReplacementFlatness P := by
  intro X Y X' Y' f g hf hg
  haveI : IsIso (sourceLocalization.map f) := Prespectrum.stableEquivalences.Q_inverts f hf
  haveI : IsIso (sourceLocalization.map g) := Prespectrum.stableEquivalences.Q_inverts g hg
  let k := R.equivalence.functor.map (sourceLocalization.map (P.derivedSmashMap f g))
  have heq : k = (D.comparison X Y).inv ≫
      (R.equivalence.functor.map (sourceLocalization.map f) ⊗ₘ
        R.equivalence.functor.map (sourceLocalization.map g)) ≫
      (D.comparison X' Y').hom := by
    have hh := congrArg (fun z => (D.comparison X Y).inv ≫ z) (D.natural f g)
    simpa only [k, Category.assoc, Iso.inv_hom_id_assoc] using hh.symm
  haveI : IsIso k := by rw [heq]; infer_instance
  intro d
  change Function.Bijective (Prespectrum.stableHomotopyMap (P.derivedSmashMap f g) d)
  constructor
  · intro x y h
    obtain ⟨a,rfl⟩ := (R.homotopy (P.derivedSmash X Y) d).surjective x
    obtain ⟨b,rfl⟩ := (R.homotopy (P.derivedSmash X Y) d).surjective y
    apply congrArg (R.homotopy (P.derivedSmash X Y) d)
    apply (cancel_mono k).mp
    apply (R.homotopy (P.derivedSmash X' Y') d).injective
    simpa only [k, R.homotopy_natural] using h
  · intro y
    let b := (R.homotopy (P.derivedSmash X' Y') d).symm y
    refine ⟨R.homotopy (P.derivedSmash X Y) d (b ≫ inv k), ?_⟩
    rw [← R.homotopy_natural]
    change R.homotopy (P.derivedSmash X' Y') d ((b ≫ inv k) ≫ k) = y
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, b, Equiv.apply_symm_apply]

/-- The prescribed diagonal smash preserves stable equivalences
after the selected replacement. -/
public theorem sourceReplacement_flat : ClassicalSourceReplacementFlatness sourceReplacement :=
  sourceReplacementFlatness_of_recognition sourceComparison sourceReplacement
    sourceDerivedSmashRecognition

end
end KIP126.AdamsSynthetic.Ordinary
