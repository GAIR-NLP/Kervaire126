module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Spectrification.Step.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingCylinder.Homotopy.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.SequentialColimit.Data
import Mathlib.CategoryTheory.Functor.OfSequence

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

/-- Factor the actual adjoint-bond unit by its actual reduced mapping cylinder. -/
noncomputable def spectrificationCylinderStep (X : Prespectrum.{u}) : Prespectrum.{u} :=
  mappingCylinder (spectrificationStepUnit X)

/-- The actual source inclusion into the cylinder of the adjoint-bond unit. -/
noncomputable def spectrificationCylinderUnit (X : Prespectrum.{u}) :
    X ⟶ spectrificationCylinderStep X := mappingCylinderInclusion (spectrificationStepUnit X)

/-- Repeated actual closed-cylinder steps, starting from the given prespectrum. -/
noncomputable def spectrificationStages (X : Prespectrum.{u}) : ℕ → Prespectrum.{u}
  | 0 => X
  | k+1 => spectrificationCylinderStep (spectrificationStages X k)

/-- The actual sequential diagram with the displayed cylinder inclusions. -/
noncomputable def spectrificationDiagram (X : Prespectrum.{u}) : ℕ ⥤ Prespectrum.{u} :=
  Functor.ofSequence (fun k => spectrificationCylinderUnit (spectrificationStages X k))

/-- The actual levelwise topological colimit of the iterated cylinder steps. -/
noncomputable def spectrificationTelescope (X : Prespectrum.{u}) : Prespectrum.{u} :=
  sequentialColimit (spectrificationDiagram X)

/-- The actual map from the original prespectrum into its constructed telescope. -/
noncomputable def spectrificationTelescopeUnit (X : Prespectrum.{u}) :
    X ⟶ spectrificationTelescope X := sequentialColimitInclusion (spectrificationDiagram X) 0

end KIP126.AdamsSynthetic.Source.Prespectrum
