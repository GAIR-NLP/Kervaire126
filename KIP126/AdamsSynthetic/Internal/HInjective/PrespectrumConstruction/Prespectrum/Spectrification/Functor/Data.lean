module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Spectrification.Functor.Map

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

/-- The actual mapping-cylinder telescope as a functor of strict prespectra. -/
noncomputable def spectrificationTelescopeFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj := spectrificationTelescope
  map := spectrificationTelescopeMap
  map_id := spectrificationTelescopeMap_id
  map_comp := spectrificationTelescopeMap_comp

end KIP126.AdamsSynthetic.Source.Prespectrum
