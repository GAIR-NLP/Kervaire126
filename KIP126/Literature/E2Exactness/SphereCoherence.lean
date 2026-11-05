module
import all KIP126.Literature.E2Exactness.Coordinates
import all KIP126.Literature.Standard.FiniteQuotientNoReturn
@[expose] section
namespace KIP126.Literature.Standard.E2Exactness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.Literature.Standard.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000
private theorem normalized_quotient_maps_equal_on_spheres
    (X Y : AdamsObject (coefficients := background.coefficients)) (k : ℕ) (hk : k ≤ 1) (j : ℕ) (hj : 0 < j)
    (a b : XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) j ⟶
      XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) j)
    (hab : XModLambdaN.incl _ j ≫ a = XModLambdaN.incl _ j ≫ b) :
    ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) j)), c ≫ a = c ≫ b := by
  apply quotient_maps_equal_on_spheres_of_no_return j a b hab
  intro m w c z
  let V := background.nu.functor.obj (X.obj background.auxiliary)
  let ε : (((SyntheticCategory.biShift (0,-(j:ℤ))).obj
      ((SyntheticCategory.biShift (0,(k:ℤ))).obj V)))⟦(1:ℤ)⟧ ≅
      (SyntheticCategory.biShift (0,(k:ℤ)-(j:ℤ)-1)).obj
        (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) :=
    (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((SyntheticCategory.biShift_comp (0,(k:ℤ)) (0,-(j:ℤ))).app V) ≪≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
      (SyntheticCategory.biShift_comp ((0,(k:ℤ))+(0,-(j:ℤ))) (1,0)).app V ≪≫
      eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
        (show ((0,(k:ℤ))+(0,-(j:ℤ)))+(1,0)=(1,1)+(0,(k:ℤ)-(j:ℤ)-1)
          by ext <;> simp; omega)) ≪≫
      (SyntheticCategory.biShift_comp (1,1) (0,(k:ℤ)-(j:ℤ)-1)).symm.app V ≪≫
      (SyntheticCategory.biShift (0,(k:ℤ)-(j:ℤ)-1)).mapIso (background.nu.suspensionIso _).symm
  have hzero (c' : BiHom m w ((SyntheticCategory.biShift (0,(k:ℤ)-(j:ℤ)-1)).obj
        (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary))))
      (z' : (SyntheticCategory.biShift (0,(k:ℤ)-(j:ℤ)-1)).obj
        (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) ⟶
          XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) j) : c' ≫ z' = 0 :=
    nonreturn_at_window_end (.shift 1 X) Y j hj ((k:ℤ)-(j:ℤ)-1) (by omega) m w c' z'

  have h := hzero (c ≫ ε.hom) (ε.inv ≫ z)
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h
private theorem shift_preserves_sphere_congruence (A B : SyntheticSpectrum)
    (δ : ℤ × ℤ) (f g : A ⟶ B)
    (hfg : ∀ (m w : ℤ) (c : BiHom m w A), c ≫ f = c ≫ g)
    (m w : ℤ) (c : BiHom m w ((SyntheticCategory.biShift δ).obj A)) :
    c ≫ (SyntheticCategory.biShift δ).map f =
      c ≫ (SyntheticCategory.biShift δ).map g := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) δ
  let ε : F.obj (Smn (m-δ.1) (w-δ.2)) ≅ Smn m w :=
    (biShiftAddIso (m-δ.1,w-δ.2) δ (m,w) (by ext <;> simp)).app S_0_0
  let c₀ := ff.preimage (ε.hom ≫ c)
  have h := congrArg F.map (hfg (m-δ.1) (w-δ.2) c₀)
  have hc : F.map c₀ = ε.hom ≫ c := ff.map_preimage _
  rw [Functor.map_comp,Functor.map_comp,hc] at h
  apply (cancel_epi ε.hom).mp
  simpa only [Category.assoc] using h

private theorem suspension_preserves_sphere_congruence
    (U V : SyntheticSpectrum) (f g : U ⟶ V)
    (hfg : ∀ (m w : ℤ) (c : BiHom m w U), c ≫ f = c ≫ g)
    (m w : ℤ) (c : BiHom m w (U⟦(1:ℤ)⟧)) :
    c ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map f =
      c ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map g := by
  let κ := SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1
  have h := shift_preserves_sphere_congruence U V (1,0) f g hfg m w
    (c ≫ κ.inv.app U)
  have h' := congrArg (fun z => z ≫ κ.hom.app V) h
  simp only [Category.assoc] at h'
  rw [κ.hom.naturality f,κ.hom.naturality g] at h'
  simpa only [Iso.inv_hom_id_app_assoc] using h'

/-- Spherewise uniqueness for maps out of a finite quotient passes to
ordinary suspension through any inclusion-compatible source comparison. -/
private theorem suspension_quotient_sphere_congruence
    (U V : SyntheticSpectrum) (q i : ℕ)
    (e : XModLambdaN (U⟦(1:ℤ)⟧) q ≅ (XModLambdaN U q)⟦(1:ℤ)⟧)
    (he : XModLambdaN.incl _ q ≫ e.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl U q))
    (huniq : ∀ (f g : XModLambdaN U q ⟶ XModLambdaN V i),
      XModLambdaN.incl U q ≫ f = XModLambdaN.incl U q ≫ g →
      ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN U q)), c ≫ f = c ≫ g)
    (f g : XModLambdaN (U⟦(1:ℤ)⟧) q ⟶ (XModLambdaN V i)⟦(1:ℤ)⟧)
    (hfg : XModLambdaN.incl _ q ≫ f = XModLambdaN.incl _ q ≫ g)
    (m w : ℤ) (c : BiHom m w (XModLambdaN (U⟦(1:ℤ)⟧) q)) :
    c ≫ f = c ≫ g := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let f₀ := ff.preimage (e.inv ≫ f)
  let g₀ := ff.preimage (e.inv ≫ g)
  have hf : S.map f₀ = e.inv ≫ f := ff.map_preimage _
  have hg : S.map g₀ = e.inv ≫ g := ff.map_preimage _
  have h₀ : XModLambdaN.incl U q ≫ f₀ = XModLambdaN.incl U q ≫ g₀ := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hf,hg,←he]
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hfg
  have h := suspension_preserves_sphere_congruence _ _ f₀ g₀
    (huniq f₀ g₀ h₀) m w (c ≫ e.hom)
  rw [hf,hg] at h
  simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

private theorem finite_suspension_normalized_map_on_spheres
    (X Y : AdamsObject (coefficients := background.coefficients)) (k : ℕ) (hk : k ≤ 1) (q : ℕ) (hq : 0 < q)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,(k:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) q ≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ q ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (hey : XModLambdaN.incl _ q ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (m w : ℤ) (c : BiHom m w (XModLambdaN
      (((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) q)) :
    c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) q ≫ ey.hom =
      c ≫ ex.hom ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q) := by
  apply suspension_quotient_sphere_congruence _ _ q q ex hex
    (fun a b hab m w c => normalized_quotient_maps_equal_on_spheres X Y k hk q hq
      a b hab m w c)
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,hey,
    ←Category.assoc,hex,←Functor.map_comp,←Functor.map_comp,XModLambdaN.incl_naturality]


end
end KIP126.Literature.Standard.E2Exactness
