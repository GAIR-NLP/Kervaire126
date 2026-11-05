module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingPath.Retained.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingPath.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.MappingPath.Lifting.Equivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Path.Endpoint.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyCategory.Quotient

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingPathInclusion_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathInclusion f ≫ mappingPathProjection f = f := rfl

@[simp] theorem mappingPathInclusion_retraction {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathInclusion f ≫ mappingPathRetraction f = 𝟙 X := rfl


/-- Actual maps out of the cubical replacement lift up to strict
homotopy through every actual level weak equivalence. -/
theorem cubicalReplacement_exists_pathHomotopic_lift (X : Prespectrum.{u})
    {E B : Prespectrum.{u}} (f : E ⟶ B)
    (hf : ∀ n (x : E.level n) r, Function.Bijective
      (KIP126.Topology.continuousHomotopyMap (f.level n) x (f.level n x) rfl r))
    (b : cubicalReplacementFunctor.obj X ⟶ B) :
    ∃ a : cubicalReplacementFunctor.obj X ⟶ E, pathHomotopic (a ≫ f) b := by
  obtain ⟨l,hl⟩ := cubicalReplacement_lift_of_level_cubeBoundary X (mappingPathProjection f)
    (mappingPathProjection_level_hasCubeBoundaryLifting f hf) b
  refine ⟨l ≫ mappingPathRetraction f,?_⟩
  have H := pathHomotopic_precomp l (show pathHomotopic (mappingPathRetraction f ≫ f)
    (mappingPathProjection f) from ⟨mappingPathRetainedHomotopy f⟩)
  simpa only [← Category.assoc,hl] using H

/-- Actual level weak equivalences reflect strict homotopy classes of
maps out of the genuine free-cubical replacement. -/
theorem cubicalReplacement_pathHomotopic_of_level_homotopy_bijective
    (X : Prespectrum.{u}) {E B : Prespectrum.{u}} (f : E ⟶ B)
    (hf : ∀ n (x : E.level n) r, Function.Bijective
      (KIP126.Topology.continuousHomotopyMap (f.level n) x (f.level n x) rfl r))
    {a b : cubicalReplacementFunctor.obj X ⟶ E}
    (H : pathHomotopic (a ≫ f) (b ≫ f)) : pathHomotopic a b := by
  have h' : pathHomotopic ((a ≫ mappingPathInclusion f) ≫ mappingPathProjection f)
      ((b ≫ mappingPathInclusion f) ≫ mappingPathProjection f) := by
    simpa only [Category.assoc,mappingPathInclusion_projection] using H
  have h'' := cubicalReplacement_pathHomotopic_of_postcomp X (mappingPathProjection f)
    (mappingPathProjection_level_hasCubeBoundaryLifting f hf) h'
  have h''' := pathHomotopic_postcomp h'' (mappingPathRetraction f)
  simpa only [Category.assoc,mappingPathInclusion_retraction,Category.comp_id] using h'''

end KIP126.AdamsSynthetic.Source.Prespectrum
