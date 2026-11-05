module
import all KIP126.AdamsSynthetic.Internal.HInjective.SphereWedgeSupport
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Recognition
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] section
namespace KIP126.AdamsSynthetic.Source
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [StableHomotopyCategory.{u,v} C]

private def sourceConnective (X : C) : Prop :=
  ∀ n : ℤ, n ≤ -1 → Subsingleton (HomotopyGroup n X)

/-- The actual finite colimit point is connective because its canonical
    preadditive bicone is also a limit cone. -/
private theorem finiteCofan_connected {J : Type} [Finite J] (A : J → C)
    (c : Cofan A) (hc : IsColimit c) (hA : ∀ j, sourceConnective (A j)) :
    sourceConnective c.pt := by
  classical
  letI := Fintype.ofFinite J
  let b := Bicone.ofColimitCocone hc
  have hb := biconeIsBilimitOfColimitCoconeOfIsColimit hc
  intro n hn
  refine ⟨fun f g => ?_⟩
  apply hb.isLimit.hom_ext
  intro j
  exact (hA j.as n hn).elim _ _

private def strictSphereCofan (J : Type) :
    Cofan (fun _ : J => sourceLocalization.obj Prespectrum.sphere) :=
  Cofan.mk (sourceLocalization.obj (Prespectrum.strictWedge (fun _ : J => Prespectrum.sphere)))
    (fun j => sourceLocalization.map (Prespectrum.strictWedgeι (fun _ : J => Prespectrum.sphere) j))

private def recognizedSphereCofan {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (J : Type) :
    Cofan (fun _ : J => R.equivalence.functor.obj (sourceLocalization.obj Prespectrum.sphere)) :=
  Cofan.mk (R.equivalence.functor.obj (strictSphereCofan J).pt)
    (fun j => R.equivalence.functor.map ((strictSphereCofan J).inj j))

private def recognizedSphereCofan_isColimit {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (J : Type) (h : IsColimit (strictSphereCofan J)) :
    IsColimit (recognizedSphereCofan R J) :=
  (Cofan.isColimitMapCoconeEquiv R.equivalence.functor _ (strictSphereCofan J))
    (isColimitOfPreserves R.equivalence.functor h)

private theorem recognized_sphere_connected {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (hs : sourceConnective (SphereSpectrum (C := C))) :
    sourceConnective (R.equivalence.functor.obj (sourceLocalization.obj Prespectrum.sphere)) := by
  intro n hn
  refine ⟨fun a b => ?_⟩
  apply (cancel_mono R.sphereIso.hom).mp
  exact (hs n hn).elim _ _

private theorem finite_strict_sphere_wedge_homotopy_subsingleton
    {H : ModTwoCoefficients C} (R : SourceRecognition C H)
    (hs : sourceConnective (SphereSpectrum (C := C)))
    {J : Type} [Finite J] (h : IsColimit (strictSphereCofan J))
    (d : ℤ) (hd : d ≤ -1) :
    Subsingleton (Prespectrum.StableHomotopy
      (Prespectrum.strictWedge (fun _ : J => Prespectrum.sphere)) d) := by
  letI : Subsingleton (HomotopyGroup d (R.equivalence.functor.obj
      (sourceLocalization.obj (Prespectrum.strictWedge (fun _ : J => Prespectrum.sphere))))) :=
    finiteCofan_connected _ (recognizedSphereCofan R J)
    (recognizedSphereCofan_isColimit R J h) (fun _ => recognized_sphere_connected R hs) d hd
  exact (R.homotopy _ d).symm.injective.subsingleton

/-- Finite support transfers connectivity for the same strict source object
under the stated finite strict-sphere-cofan colimit hypotheses,
using the actual subfamily maps. -/
private theorem recognized_strict_sphere_wedge_connected
    {H : ModTwoCoefficients C} (R : SourceRecognition C H)
    (hs : sourceConnective (SphereSpectrum (C := C)))
    (hfinite : ∀ (J : Type) [Finite J], IsColimit (strictSphereCofan J))
    (J : Type) : sourceConnective (recognizedSphereCofan R J).pt := by
  intro d hd
  have hz (a : HomotopyGroup d (recognizedSphereCofan R J).pt) : a = 0 := by
    obtain ⟨s,b,hb⟩ := Prespectrum.actual_sphere_strict_wedge_finite_support J d (R.homotopy _ d a)
    have hsub := finite_strict_sphere_wedge_homotopy_subsingleton R hs (hfinite (s : Set J)) d hd
    have hb0 := hsub.elim b (R.homotopy _ d 0)
    apply (R.homotopy _ d).injective
    rw [← hb, hb0]
    have hn := R.homotopy_natural
      (Prespectrum.strictWedgeSubfamily (fun _ : J => Prespectrum.sphere) (s : Set J)) d 0
    simpa only [zero_comp] using hn.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

private def cofanTransportInputs {J : Type} {A B : J → C}
    (c : Cofan A) (e : ∀ j, A j ≅ B j) : Cofan B :=
  Cofan.mk c.pt (fun j => (e j).inv ≫ c.inj j)

private def cofanTransportInputs_isColimit {J : Type} {A B : J → C}
    (c : Cofan A) (hc : IsColimit c) (e : ∀ j, A j ≅ B j) :
    IsColimit (cofanTransportInputs c e) := by
  refine Cofan.IsColimit.mk _
    (fun t => hc.desc (Cofan.mk t.pt (fun j => (e j).hom ≫ t.inj j))) ?_ ?_
  · intro t j
    change ((e j).inv ≫ c.inj j) ≫
      hc.desc (Cofan.mk t.pt (fun j => (e j).hom ≫ t.inj j)) = t.inj j
    erw [Category.assoc, hc.fac (Cofan.mk t.pt (fun j => (e j).hom ≫ t.inj j)) ⟨j⟩]
    exact Iso.inv_hom_id_assoc (e j) (t.inj j)
  · intro t m hm
    apply hc.hom_ext
    intro j
    change c.inj j.as ≫ m = c.inj j.as ≫
      hc.desc (Cofan.mk t.pt (fun j => (e j).hom ≫ t.inj j))
    erw [hc.fac (Cofan.mk t.pt (fun j => (e j).hom ≫ t.inj j)) j]
    have h := congrArg (fun f => (e j.as).hom ≫ f) (hm j.as)
    simpa only [cofanTransportInputs, cofan_mk_inj, Cofan.mk_ι_app, Category.assoc,
      Iso.hom_inv_id_assoc] using h

private def recognizedSphereZeroCofan {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (J : Type) : Cofan (fun _ : J => Sphere (C := C) 0) :=
  cofanTransportInputs (recognizedSphereCofan R J)
    (fun _ => R.sphereIso ≪≫ ((shiftFunctorZero C ℤ).app SphereSpectrum).symm)

private def recognizedSphereZeroCofan_isColimit {H : ModTwoCoefficients C}
    (R : SourceRecognition C H) (J : Type) (h : IsColimit (strictSphereCofan J)) :
    IsColimit (recognizedSphereZeroCofan R J) :=
  cofanTransportInputs_isColimit _ (recognizedSphereCofan_isColimit R J h) _

/-- The localized strict-source colimit comparison transfers connectivity to small
coproducts of Sphere 0. -/
private theorem sphereCoproduct_connected_of_localized_strict_colimits
    {H : ModTwoCoefficients C} (R : SourceRecognition C H)
    (hs : sourceConnective (SphereSpectrum (C := C)))
    (hcolim : ∀ J : Type, IsColimit (strictSphereCofan J))
    (J : Type) [HasCoproduct (fun _ : J => Sphere (C := C) 0)] :
    sourceConnective (∐ fun _ : J => Sphere (C := C) 0) := by
  let c := recognizedSphereZeroCofan R J
  let hc := recognizedSphereZeroCofan_isColimit R J (hcolim J)
  let e := hc.coconePointUniqueUpToIso
    (colimit.isColimit (Discrete.functor (fun _ : J => Sphere (C := C) 0)))
  have hconn := recognized_strict_sphere_wedge_connected R hs (fun J _ => hcolim J) J
  intro d hd
  refine ⟨fun a b => ?_⟩
  apply (cancel_mono e.inv).mp
  exact (hconn d hd).elim _ _

end
end KIP126.AdamsSynthetic.Source
end
