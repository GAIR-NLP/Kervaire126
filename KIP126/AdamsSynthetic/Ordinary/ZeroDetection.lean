module

public import KIP126.AdamsSynthetic.Ordinary.Background
public import KIP126.AdamsSynthetic.AdamsFiltration
import all KIP126.AdamsSynthetic.Ordinary.TopologicalComparison
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Recognition
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.ZeroPrespectrum

/-! Direct acyclic-tower vanishing for the actual ordinary Adams system.
No UCT, synthetic object, first quotient, normalized map, tensor exactness or
HF₂-localized Adams comparison is used. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Ordinary
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open scoped ZeroObject
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

/-- Ordinary Whitehead for zero objects, using the actual stable source.
The source representative of the target zero object need not be a point spectrum. -/
private theorem ordinary_isZero_of_homotopy_zero (X : Spectrum)
    (hπ : ∀ d : ℤ, Subsingleton (HomotopyGroup d X)) : IsZero X := by
  let R : Source.SourceRecognition Spectrum coefficients := sourceComparison
  let Q := Source.sourceLocalization.{0}
  let F := R.equivalence.functor
  let G := Q ⋙ F
  let P := G.objPreimage X
  let O := G.objPreimage (0 : Spectrum)
  let e : G.obj P ≅ X := G.objObjPreimageIso X
  let e0 : G.obj O ≅ (0 : Spectrum) := G.objObjPreimageIso (0 : Spectrum)
  have h0 : IsZero (G.obj O) := (isZero_zero Spectrum).of_iso e0
  let f : P ⟶ O := Source.Prespectrum.zeroHom P O
  have hf : Source.Prespectrum.stableEquivalences f := by
    intro d
    letI := hπ d
    letI : Subsingleton (HomotopyGroup d (R.equivalence.functor.obj
        (Source.sourceLocalization.obj P))) :=
      (Iso.homCongr (Iso.refl (Sphere (C := Spectrum) d)) e).injective.subsingleton
    letI : Subsingleton (HomotopyGroup d (R.equivalence.functor.obj
        (Source.sourceLocalization.obj O))) := ⟨fun a b => h0.eq_of_tgt a b⟩
    letI : Subsingleton (Source.Prespectrum.StableHomotopy P d) :=
      (R.homotopy P d).symm.injective.subsingleton
    letI : Subsingleton (Source.Prespectrum.StableHomotopy O d) :=
      (R.homotopy O d).symm.injective.subsingleton
    exact ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun b => ⟨R.homotopy P d 0, Subsingleton.elim _ _⟩⟩
  letI : IsIso (Q.map f) := Source.Prespectrum.stableEquivalences.Q_inverts f hf
  letI : IsIso (G.map f) := inferInstanceAs (IsIso (F.map (Q.map f)))
  exact h0.of_iso (e.symm ≪≫ asIso (G.map f))

end
end KIP126.AdamsSynthetic.Ordinary
