module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyPullback.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Fiber.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum

open CategoryTheory

universe u

/-- The actual fiber is the path homotopy pullback over the point prespectrum. -/
def fiberToHomotopyPullback {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber f ⟶ homotopyPullback f (zeroMap zeroPrespectrum Y) where
  level _ :=
    { toFun := fun p => ⟨(⟨p.val,p.property.1⟩,PUnit.unit),p.property.2⟩
      continuous_toFun := ((continuous_subtype_val.subtype_mk _).prodMk
        continuous_const).subtype_mk _ }
  point _ := rfl
  bond _ _ _ := rfl

def homotopyPullbackToFiber {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    homotopyPullback f (zeroMap zeroPrespectrum Y) ⟶ fiber f where
  level _ :=
    { toFun := fun p => ⟨p.val.1.val,⟨p.val.1.property,p.property⟩⟩
      continuous_toFun := continuous_subtype_val.fst.subtype_val.subtype_mk _ }
  point _ := rfl
  bond _ _ _ := rfl

/-- An actual strict isomorphism identifies the constructed fiber with
the mapping-path pullback over zero, before any localization. -/
def fiberHomotopyPullbackIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    fiber f ≅ homotopyPullback f (zeroMap zeroPrespectrum Y) where
  hom := fiberToHomotopyPullback f
  inv := homotopyPullbackToFiber f
  hom_inv_id := rfl
  inv_hom_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact @Subsingleton.elim PUnit _ _ _

end KIP126.AdamsSynthetic.Source.Prespectrum
