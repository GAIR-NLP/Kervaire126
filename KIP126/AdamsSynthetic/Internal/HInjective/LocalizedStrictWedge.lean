module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.HInjective.StrictWedge
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Colimit.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Replacement.Cubical.Cofibrant.Coproduct

/-! Transport the localized coproduct along the canonical strict
coproduct isomorphism, retaining the explicit wedge and its original inclusions. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def source_strictWedge_isColimit {J : Type u} (X : J → Prespectrum.{u})
    (hX : ∀ j, IsCubicallyCofibrant (X j)) :
    IsColimit (Cofan.mk (sourceLocalization.obj (strictWedge X))
      (fun j => sourceLocalization.map (strictWedgeι X j))) := by
  let e : strictWedge X ≅ ∐ X :=
    (strictWedgeIsColimit X).coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor X))
  have he (j : J) : strictWedgeι X j ≫ e.hom = Sigma.ι X j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (strictWedgeIsColimit X)
      (colimit.isColimit (Discrete.functor X)) ⟨j⟩
  let ec : Cofan.mk (sourceLocalization.obj (strictWedge X))
      (fun j => sourceLocalization.map (strictWedgeι X j)) ≅ sourceStrictSigmaCofan X :=
    Cocone.ext (sourceLocalization.mapIso e) (by
      rintro ⟨j⟩
      change sourceLocalization.map (strictWedgeι X j) ≫ sourceLocalization.map e.hom = _
      rw [← Functor.map_comp, he]
      rfl)
  exact (sourceStrictSigmaCofan_isColimit X hX).ofIsoColimit ec.symm

end
end KIP126.AdamsSynthetic.Source.Prespectrum
end
