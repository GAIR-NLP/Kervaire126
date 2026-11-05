module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.StrictWedge
import all KIP126.AdamsSynthetic.Internal.HInjective.LocalizedStrictWedge
import all KIP126.AdamsSynthetic.Internal.HInjective.SphereCofibrant

/-! The strict wedge of the sphere is a coproduct in the stable localization, with
the strict wedge inclusions. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory CategoryTheory.Limits
noncomputable section

private def actual_sphere_source_coproduct (J : Type) :
    IsColimit (Cofan.mk (sourceLocalization.obj (strictWedge (fun _ : J => sphere)))
      (fun j => sourceLocalization.map (strictWedgeι (fun _ : J => sphere) j))) :=
  source_strictWedge_isColimit (fun _ : J => sphere)
    (fun _ => actual_sphere_isCubicallyCofibrant)

end
end KIP126.AdamsSynthetic.Source.Prespectrum
end
