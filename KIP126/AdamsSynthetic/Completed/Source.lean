





module

public import KIP126.AdamsSynthetic.Completed
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
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.Classical.Adams
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The recursive fiber tower of the specified coefficient unit. -/
@[no_expose] public def canonicalAdamsTower (X : Spectrum) :
    AbstractAdamsTower coefficients.unit X := Internal.Source.canonicalTower coefficients.unit X

/-- Its nested-subobject spectral sequence, with actual finite cycles and
boundaries and their intersection/union at infinity. -/
@[no_expose] public def canonicalAdamsSequence (X : Spectrum) :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  Internal.Source.canonicalSequence coefficients.unit X

/-- Actual connecting-map/cofiber first differential, in nonnegative
Adams coordinates. No first differential is chosen as extra input. -/
@[no_expose] public def canonicalFirstDifferential (s t : ℕ) :
    (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage ((s : ℤ), (t : ℤ)) →ₗ[ℤ]
      (canonicalAdamsTower (SphereSpectrum : Spectrum)).FirstPage
        (((s + 1 : ℕ) : ℤ), (t : ℤ)) :=
  Internal.Source.towerFirstDifferentialNat (canonicalAdamsTower SphereSpectrum) s t

/-- The actual fixed classical functor on the ordinary concrete source. -/
public def sourceClassical : ClassicalSource ⥤
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  Ordinary.sourceComparison.equivalence.functor ⋙ completion ⋙ classical.functor

/-- Descent requires the whole spectral sequence, including its infinite
representatives, to invert these precise HF₂ cohomology equivalences. -/
public theorem sourceClassical_inverts_hf2 :
    (classicalHF2Equivalences Ordinary.sourceComparison).IsInvertedBy sourceClassical := by
  intro X Y f hf
  let E := Ordinary.sourceComparison.equivalence
  let Q := classicalHF2Localization Ordinary.sourceComparison
  haveI : IsIso (Q.map f) :=
    (classicalHF2Equivalences Ordinary.sourceComparison).Q_inverts f hf
  have heq : E.inverse.map (E.functor.map f) =
      E.unitIso.inv.app X ≫ f ≫ E.unitIso.hom.app Y := by
    have h := E.unitIso.hom.naturality f
    simpa only [Functor.id_map, Functor.comp_map, Category.assoc,
      Iso.inv_hom_id_app_assoc] using
      congrArg (fun z => E.unitIso.inv.app X ≫ z) h.symm
  dsimp only [sourceClassical, completion, Functor.comp_map]
  change IsIso (classical.functor.map (spectrumSourceEquivalence.functor.map
    (Q.map (E.inverse.map (E.functor.map f)))))
  rw [heq]
  simp only [Functor.map_comp]
  infer_instance

/-- The classical functor on the HF₂-localized source induced by the localization
universal property. -/
public def localizedClassical : ClassicalHF2LocalizedSource Ordinary.sourceComparison ⥤
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) := by
  letI := classicalHF2Localization_isLocalization Ordinary.sourceComparison
  exact CategoryTheory.Localization.lift sourceClassical sourceClassical_inverts_hf2
    (classicalHF2Localization Ordinary.sourceComparison)

public def sourceLocalizationAdamsIso :
    classicalHF2Localization Ordinary.sourceComparison ⋙ localizedClassical ≅ sourceClassical := by
  letI := classicalHF2Localization_isLocalization Ordinary.sourceComparison
  exact CategoryTheory.Localization.fac sourceClassical sourceClassical_inverts_hf2
    (classicalHF2Localization Ordinary.sourceComparison)

public def localizedSphereSequence :
    KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ) :=
  localizedClassical.obj (classicalHF2LocalizedSphere Ordinary.sourceComparison)

public def localizedSphere_classicalIso : localizedSphereSequence ≅ classical.sphere :=
  sourceLocalizationAdamsIso.app classicalSourceSphere ≪≫
    classical.functor.mapIso (completion.mapIso Ordinary.sourceComparison.sphereIso ≪≫ completionSphereIso)

public def localizedH6Square : localizedSphereSequence.Page 2 (2,128) :=
  localizedSphere_classicalIso.inv.pageMap 2 (2,128) standardH6Square

/-- Nonzero survival transports along the specified source and sphere comparisons. -/
public theorem nonzeroSurvival_localized_iff :
    NonzeroSurvival localizedSphereSequence (2,128) localizedH6Square ↔
      NonzeroSurvival classical.sphere (2,128) standardH6Square :=
  Internal.Source.nonzeroSurvival_iso_iff localizedSphere_classicalIso.symm
    (2,128) standardH6Square

end
end KIP126.AdamsSynthetic.Completed
