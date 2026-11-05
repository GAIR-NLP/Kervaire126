module
import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeLabels
import all KIP126.ProofTools.GeneralizedMahowald.CofiberIdentification
import all KIP126.ProofTools.GeneralizedMahowald.QuotientShift

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/- Cofiber coordinates use the quotient comparison of cNu; their common
desuspension agrees with cNu on representatives. -/
private def commonCofiberTargetIso
    {C V : SyntheticSpectrum} (e : ℤ) (e₀ : C ≅ (SyntheticCategory.biShift (1,e)).obj V)
    (i r : ℕ)
    (eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj V) r ≅
      (SyntheticCategory.biShift (1,e)).obj (XModLambdaN V r)) :
    XModLambdaN C r ≅ (SyntheticCategory.biShift (1,-(i:ℤ))).obj
      ((SyntheticCategory.biShift (0,(i:ℤ)+e)).obj (XModLambdaN V r)) :=
  (background.quotients.functoriality.functor r).mapIso e₀ ≪≫ eQ ≪≫
    (biShiftAddIso (0,(i:ℤ)+e) (1,-(i:ℤ)) (1,e)
      (by ext <;> dsimp; all_goals omega)).symm.app _

private theorem common_cofiber_target_inclusion
    {C V : SyntheticSpectrum} (e : ℤ) (e₀ : C ≅ (SyntheticCategory.biShift (1,e)).obj V)
    (i r : ℕ)
    (eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj V) r ≅
      (SyntheticCategory.biShift (1,e)).obj (XModLambdaN V r))
    (heQ : XModLambdaN.incl _ r ≫ eQ.hom =
      (SyntheticCategory.biShift (1,e)).map (XModLambdaN.incl V r)) :
    XModLambdaN.incl C r ≫ (commonCofiberTargetIso e e₀ i r eQ).hom =
      e₀.hom ≫ (SyntheticCategory.biShift (1,e)).map (XModLambdaN.incl V r) ≫
        (biShiftAddIso (0,(i:ℤ)+e) (1,-(i:ℤ)) (1,e)
          (by ext <;> dsimp; all_goals omega)).inv.app (XModLambdaN V r) := by
  change XModLambdaN.incl C r ≫ XModLambdaN.map e₀.hom r ≫ eQ.hom ≫ _ = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,
    ←Category.assoc (XModLambdaN.incl _ r),heQ]
  rfl

/- Cofiber and common-shift coordinates from T, using its exact
quotient-shift comparison. -/
private theorem normalized_common_cofiber_coordinates_exists
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he) (i r : ℕ) :
    let e : ℤ := normalizedExponent background.classicalTower T.f + normalizedExponent background.classicalTower T.g
    let V := background.nu.functor.obj (T.X.obj background.auxiliary)
    ∃ eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj V) r ≅
        (SyntheticCategory.biShift (1,e)).obj (XModLambdaN V r),
      XModLambdaN.incl _ r ≫ eQ.hom =
        (SyntheticCategory.biShift (1,e)).map (XModLambdaN.incl V r) ∧
      Nonempty (XModLambdaN (HasFunctorialCofiber.cofib (background.normalizedMap T.Y T.Z T.g).map) r ≅
        (SyntheticCategory.biShift (1,-(i:ℤ))).obj
          ((SyntheticCategory.biShift (0,(i:ℤ)+e)).obj (XModLambdaN V r))) := by
  dsimp only
  let e : ℤ := normalizedExponent background.classicalTower T.f + normalizedExponent background.classicalTower T.g
  letI := background.exactness.shiftCommShift (1,e)
  letI := background.exactness.shiftExact (1,e)
  obtain ⟨eQ,heQ,_⟩ := quotient_shift_exists background.quotients.coherence (1,e) r
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  exact ⟨eQ,heQ,⟨commonCofiberTargetIso e (normalized_g_cofiber_iso T he hT) i r eQ⟩⟩

/- The common-shift lift is the positive vertical shift of the
native cNu lift, as an equality of sphere representatives. -/
private theorem common_cofiber_desuspend_eq_shift_cNu
    (X : AdamsObject (coefficients := background.coefficients)) {C : SyntheticSpectrum} (e : ℤ)
    (e₀ : C ≅ (SyntheticCategory.biShift (1,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))
    (i r : ℕ)
    (eQ : XModLambdaN ((SyntheticCategory.biShift (1,e)).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) r ≅
      (SyntheticCategory.biShift (1,e)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) r))
    (m w : ℤ) (c : BiHom m w (XModLambdaN C r)) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    ff.preimage ((biShiftAddIso (m-1,w+i) (1,-(i:ℤ)) (m,w)
        (by ext <;> dsimp; all_goals omega)).hom.app S_0_0 ≫ c ≫
      (commonCofiberTargetIso e e₀ i r eQ).hom) =
    homotopyRegrade (by simp) (by dsimp; omega)
      (shiftHomotopyClass (0,(i:ℤ)+e) (m-1,w-e)
        (quotientShiftDesuspend X (1,e) r eQ m w (c ≫ XModLambdaN.map e₀.hom r))) := by
  dsimp only
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
  apply ff.map_injective
  rw [shift_regrade]
  simp only [Functor.map_comp,Functor.FullyFaithful.map_preimage]
  apply (cancel_epi ((biShiftAddIso (m-1,w+i) (1,-(i:ℤ)) (m,w)
    (by ext <;> dsimp; all_goals omega)).inv.app (S_0_0 : SyntheticSpectrum))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  have hassoc := shift_hom_associativity background.quotients.coherence
    (m-1,w-e) (0,(i:ℤ)+e) (1,-(i:ℤ)) (m-1,w+i) (1,e) (m,w)
    (by ext <;> dsimp; all_goals omega) (by ext <;> dsimp; all_goals omega)
    (by ext <;> dsimp; all_goals omega) (by ext <;> dsimp; all_goals omega)
    (quotientShiftDesuspend X (1,e) r eQ m w (c ≫ XModLambdaN.map e₀.hom r))
  rw [←Functor.map_comp,←hassoc]
  simp only [quotientShiftDesuspend,Functor.FullyFaithful.map_preimage,
    commonCofiberTargetIso,Iso.trans_hom,Iso.symm_hom,Iso.app_hom,Category.assoc,
    Iso.inv_hom_id_app_assoc,Functor.mapIso_hom,LambdaQuotientFunctoriality.functor]


/- Flatten the normalization in A only after the raw common target has been
fixed. Both target forms are used by the finite edge and sphere-source
extension lemmas; this is an actual isomorphism between them. -/
private def commonEdgeFlattenIso (V : SyntheticSpectrum) (a : ℤ) (i r : ℕ)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) r ≅
      (SyntheticCategory.biShift (0,a)).obj (XModLambdaN V r)) :
    (SyntheticCategory.biShift (0,(i:ℤ))).obj
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) r) ≅
      (SyntheticCategory.biShift (0,(i:ℤ)+a)).obj (XModLambdaN V r) :=
  (SyntheticCategory.biShift (0,(i:ℤ))).mapIso eA ≪≫
    (biShiftAddIso (0,a) (0,(i:ℤ)) (0,(i:ℤ)+a) (by ext <;> dsimp; all_goals omega)).app _

private def commonEdgeTargetFlatIso (V : SyntheticSpectrum) (a : ℤ) (i q : ℕ)
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,a)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (0,a)).obj (XModLambdaN V (i+q))) :
    XModLambdaN (((SyntheticCategory.biShift (0,a)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (SyntheticCategory.biShift (1,-(i:ℤ))).obj
        ((SyntheticCategory.biShift (0,(i:ℤ)+a)).obj (XModLambdaN V (i+q))) :=
  commonEdgeTargetIso ((SyntheticCategory.biShift (0,a)).obj V) i q esusp ≪≫
    (SyntheticCategory.biShift (1,-(i:ℤ))).mapIso (commonEdgeFlattenIso V a i (i+q) eA)

/- Flattening preserves the K, Jedge, or residual t₀ preimage
of the specified May representative. -/
private theorem common_edge_flatten_preimage
    (V U : SyntheticSpectrum) (a : ℤ) (i q : ℕ)
    (esusp : XModLambdaN (((SyntheticCategory.biShift (0,a)).obj V)⟦(1:ℤ)⟧) (i+q) ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q))⟦(1:ℤ)⟧)
    (eA : XModLambdaN ((SyntheticCategory.biShift (0,a)).obj V) (i+q) ≅
      (SyntheticCategory.biShift (0,a)).obj (XModLambdaN V (i+q)))
    (p : (SyntheticCategory.biShift (1,-(i:ℤ))).obj U ⟶
      XModLambdaN (((SyntheticCategory.biShift (0,a)).obj V)⟦(1:ℤ)⟧) (i+q)) :
    let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))
    ff.preimage (p ≫ (commonEdgeTargetFlatIso V a i q esusp eA).hom) =
      ff.preimage (p ≫ (commonEdgeTargetIso ((SyntheticCategory.biShift (0,a)).obj V) i q esusp).hom) ≫
        (commonEdgeFlattenIso V a i (i+q) eA).hom := by
  dsimp only
  apply (SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (1,-(i:ℤ))).map_injective
  simp only [Functor.map_comp,Functor.FullyFaithful.map_preimage,
    commonEdgeTargetFlatIso,Iso.trans_hom,Functor.mapIso_hom,Category.assoc]

end
end KIP126.ProofTools.Internal.Mahowald
