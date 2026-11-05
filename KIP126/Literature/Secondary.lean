module

public import KIP126.Literature.Classical
import all KIP126.Literature.Classical
public import KIP126.Literature.Toda
import all KIP126.Literature.Toda
public import KIP126.Literature.May
import all KIP126.Literature.May
public import KIP126.Literature.Moss
import all KIP126.Literature.Moss

/-! Secondary operations on one specified model, with the actual sphere,
its chosen sphere E₂ algebra and the corresponding mapping composition.
The Hopf class η and object range are those of this same model. -/

@[expose] section
namespace KIP126.Literature
open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : AdamsSyntheticBackground C Syn)

/-- Model-side mapping, tensor and Toda data. The sphere mapping spectrum
uses D's actual tower; its E₂ product and unit agree with D's existing algebra. -/
private structure SecondaryBindings where
  closed : ClosedSymmetricTensorTriangulated C
  mapping : MappingSpectrumSystem closed D.classicalTower
    (fun X : C => X = SphereSpectrum)
  moss : Moss.Context mapping
  sphereComposition : MappingSphereCompatibility moss.composition D.sphereAlgebra rfl
  may : Route.MayContext Syn
  toda : Route.TodaSourceData (Syn := Syn)

/-- Source results are separate from construction of the bound model data.
The Toda statements use precisely the η in the existing classical binding. -/
private structure SecondaryResults (B : ClassicalBindings D) (Q : SecondaryBindings D) : Prop where
  moss : Moss.SourceResults Q.mapping Q.moss
  may : Route.MaySourceResults Syn Q.may
  toda : Route.TodaSourceResults D B.eta Q.toda

end KIP126.Literature
