module

import all KIP126.Main.Internal.NuThree.Shift
import all KIP126.Main.Internal.ChoiceIndependence.LambdaInjectivity
import all KIP126.Main.Internal.Moore.ConstructionBoundary
import all KIP126.Main.Internal.Moore.ConstructionMayMap

/-! Fixed object and quotient transports for the twice-rotated Moore triangle.
These comparisons use the supplied nu suspension and unit isomorphisms. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum Spectrum)
open KIP126.Main.Internal.AlphaOne
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private def mooreNuSuspensionIso :
    background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum) ≅
      Smn (Syn:=SyntheticSpectrum) 1 1 :=
  background.nu.suspensionIso SphereSpectrum ≪≫
    (SyntheticCategory.biShift (1,1)).mapIso background.nu.unitIso

private def mooreNuDeshiftedSuspensionIso :
    (SyntheticCategory.biShift (0,-1)).obj
        (background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum)) ≅
      Smn (Syn:=SyntheticSpectrum) 1 0 :=
  (SyntheticCategory.biShift (0,-1)).mapIso mooreNuSuspensionIso ≪≫
    (SyntheticCategory.biShift_comp (1,1) (0,-1)).app (S_0_0 : SyntheticSpectrum)

private theorem sphere_quotient_shift_full (p : ℤ × ℤ) (q : ℕ) :
    letI := background.exactness.shiftCommShift p
    ∃ e : (SyntheticCategory.biShift p).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) q) ≅
        XModLambdaN ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q,
      (SyntheticCategory.biShift p).map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) ≫
        e.hom = XModLambdaN.incl ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q ∧
      e.hom ≫ XModLambdaN.proj ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q =
        (SyntheticCategory.biShift p).map (XModLambdaN.proj (S_0_0 : SyntheticSpectrum) q) ≫
          ((SyntheticCategory.biShift p).commShiftIso (1:ℤ)).hom.app
            ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree q)).obj (S_0_0 : SyntheticSpectrum)) ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            (shiftSwap p (KIP126.Synthetic.Context.lambdaDegree q) (S_0_0 : SyntheticSpectrum)).inv := by
  letI := background.exactness.shiftCommShift p
  letI := background.exactness.shiftExact p
  let A := (S_0_0 : SyntheticSpectrum)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p
  let T := XModLambdaN.cofiberTriangle A q
  let U := XModLambdaN.cofiberTriangle (F.obj A) q
  let c : (F.mapTriangle.obj T).obj₁ ≅ U.obj₁ :=
    (shiftSwap p (KIP126.Synthetic.Context.lambdaDegree q) A).symm
  have hc : (F.mapTriangle.obj T).mor₁ ≫ (Iso.refl _).hom = c.hom ≫ U.mor₁ := by
    change F.map (lambdaPow q A) ≫ 𝟙 _ =
      (shiftSwap p (KIP126.Synthetic.Context.lambdaDegree q) A).inv ≫ lambdaPow q (F.obj A)
    rw [lambda_pow_shift background.quotients.coherence]
    simp only [Iso.inv_hom_id_assoc,Category.comp_id]
    rfl
  let E := isoTriangleOfIso₁₂ (F.mapTriangle.obj T) U
    (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished A q))
    (XModLambdaN.cofiberTriangle_distinguished (F.obj A) q) c (Iso.refl _) hc
  refine ⟨Triangle.π₃.mapIso E,?_,?_⟩
  · have h := E.hom.comm₂
    have he₂ : E.hom.hom₂ = 𝟙 _ := isoTriangleOfIso₁₂_hom_hom₂ _ _ _ _ _ _ _
    rw [he₂,Category.id_comp] at h
    exact h
  · have h := E.hom.comm₃
    have he₁ : E.hom.hom₁ = c.hom := isoTriangleOfIso₁₂_hom_hom₁ _ _ _ _ _ _ _
    rw [he₁] at h
    change (F.map (XModLambdaN.proj A q) ≫
      (F.commShiftIso (1:ℤ)).hom.app _) ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map c.hom =
      E.hom.hom₃ ≫ XModLambdaN.proj (F.obj A) q at h
    simpa only [F,c,A,U,XModLambdaN.cofiberTriangle,KIP126.Synthetic.Context.lambdaDegree,
      Functor.mapIso_hom,Triangle.π₃_map,Iso.symm_hom,
      Category.assoc] using h.symm

private def sphereQuotientShiftIso (p : ℤ × ℤ) (q : ℕ) :
    (SyntheticCategory.biShift p).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) q) ≅
      XModLambdaN ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q :=
  (sphere_quotient_shift_full p q).choose

private theorem sphere_quotient_shift_inclusion (p : ℤ × ℤ) (q : ℕ) :
    (SyntheticCategory.biShift p).map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) ≫
      (sphereQuotientShiftIso p q).hom =
      XModLambdaN.incl ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q :=
  (sphere_quotient_shift_full p q).choose_spec.1

private theorem sphere_quotient_shift_projection (p : ℤ × ℤ) (q : ℕ) :
    letI := background.exactness.shiftCommShift p
    (sphereQuotientShiftIso p q).hom ≫
      XModLambdaN.proj ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q =
      (SyntheticCategory.biShift p).map (XModLambdaN.proj (S_0_0 : SyntheticSpectrum) q) ≫
        ((SyntheticCategory.biShift p).commShiftIso (1:ℤ)).hom.app
          ((SyntheticCategory.biShift (KIP126.Synthetic.Context.lambdaDegree q)).obj (S_0_0 : SyntheticSpectrum)) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (shiftSwap p (KIP126.Synthetic.Context.lambdaDegree q) (S_0_0 : SyntheticSpectrum)).inv :=
  (sphere_quotient_shift_full p q).choose_spec.2

private def quotientAlongSphereShift (p : ℤ × ℤ) (q : ℕ)
    {A : SyntheticSpectrum} (e : A ≅ (SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) :
    XModLambdaN A q ≅ (SyntheticCategory.biShift p).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) q) :=
  (background.quotients.functoriality.functor q).mapIso e ≪≫
    (sphereQuotientShiftIso p q).symm

private theorem quotient_along_sphere_shift_inclusion (p : ℤ × ℤ) (q : ℕ)
    {A : SyntheticSpectrum} (e : A ≅ (SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) :
    XModLambdaN.incl A q ≫ (quotientAlongSphereShift p q e).hom =
      e.hom ≫ (SyntheticCategory.biShift p).map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) := by
  have h := congrArg (fun z => z ≫ (sphereQuotientShiftIso p q).inv)
    (sphere_quotient_shift_inclusion p q)
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id] at h
  simp only [quotientAlongSphereShift,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom]
  change XModLambdaN.incl A q ≫ XModLambdaN.map e.hom q ≫
    (sphereQuotientShiftIso p q).inv = _
  rw [←Category.assoc,←XModLambdaN.incl_naturality,Category.assoc,←h]

private def mooreNuSuspensionQuotientIso (q : ℕ) :
    XModLambdaN
      (background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum)) q ≅
      (SyntheticCategory.biShift (1,1)).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) q) :=
  quotientAlongSphereShift (1,1) q mooreNuSuspensionIso

private def mooreNuDeshiftedSuspensionQuotientIso (q : ℕ) :
    XModLambdaN ((SyntheticCategory.biShift (0,-1)).obj
      (background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum))) q ≅
      (SyntheticCategory.biShift (1,0)).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) q) :=
  quotientAlongSphereShift (1,0) q mooreNuDeshiftedSuspensionIso

private theorem moore_nu_suspension_quotient_inclusion (q : ℕ) :
    XModLambdaN.incl
      (background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum)) q ≫
        (mooreNuSuspensionQuotientIso q).hom =
      mooreNuSuspensionIso.hom ≫
        (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) :=
  quotient_along_sphere_shift_inclusion (1,1) q mooreNuSuspensionIso

private theorem moore_nu_deshifted_suspension_quotient_inclusion (q : ℕ) :
    XModLambdaN.incl ((SyntheticCategory.biShift (0,-1)).obj
      (background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum))) q ≫
        (mooreNuDeshiftedSuspensionQuotientIso q).hom =
      mooreNuDeshiftedSuspensionIso.hom ≫
        (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) :=
  quotient_along_sphere_shift_inclusion (1,0) q mooreNuDeshiftedSuspensionIso

private theorem moore_deshifted_suspension_delta_naturality :
    XModLambdaN.map mooreNuDeshiftedSuspensionIso.hom 1 ≫
      ((background.quotients.tower (Smn (Syn:=SyntheticSpectrum) 1 0)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta =
    ((background.quotients.tower ((SyntheticCategory.biShift (0,-1)).obj
      (background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum)))).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.map mooreNuDeshiftedSuspensionIso.hom 1)) :=
  (background.quotients.natural mooreNuDeshiftedSuspensionIso.hom).delta_naturality
    (i:=1) (j:=2) (by decide) (by decide)

private theorem moore_suspension_quotient_map (q : ℕ)
    (f : background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum) ⟶
      (SyntheticCategory.biShift (0,-1)).obj
        (background.nu.functor.obj ((shiftFunctor Spectrum (1:ℤ)).obj SphereSpectrum))) :
    XModLambdaN.map f q ≫ XModLambdaN.map mooreNuDeshiftedSuspensionIso.hom q =
      XModLambdaN.map mooreNuSuspensionIso.hom q ≫
        XModLambdaN.map
          (mooreNuSuspensionIso.inv ≫ f ≫ mooreNuDeshiftedSuspensionIso.hom) q := by
  rw [←background.quotients.functoriality.map_comp,
    ←background.quotients.functoriality.map_comp,Iso.hom_inv_id_assoc]

private theorem sphere_quotient_endomorphism_congruence (q : ℕ) (hq : 0<q)
    (f g : XModLambdaN (S_0_0 : SyntheticSpectrum) q ⟶ XModLambdaN (S_0_0 : SyntheticSpectrum) q)
    (hfg : XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q ≫ f =
      XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q ≫ g)
    (m w : ℤ) (a : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) q)) :
    a ≫ f = a ≫ g := by
  let e := (background.quotients.functoriality.functor q).mapIso background.nu.unitIso
  have he : XModLambdaN.incl (background.nu.functor.obj SphereSpectrum) q ≫ e.hom =
      background.nu.unitIso.hom ≫ XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q :=
    (XModLambdaN.incl_naturality background.nu.unitIso.hom q).symm
  have h := KIP126.Main.Internal.Choice.lambda_quotient_maps_equal_on_spheres
    .sphere q hq (e.hom ≫ f ≫ e.inv) (e.hom ≫ g ≫ e.inv) (by
      change XModLambdaN.incl (background.nu.functor.obj SphereSpectrum) q ≫
          (e.hom ≫ f ≫ e.inv) =
        XModLambdaN.incl (background.nu.functor.obj SphereSpectrum) q ≫
          (e.hom ≫ g ≫ e.inv)
      erw [←Category.assoc,←Category.assoc,he,
        ←Category.assoc,←Category.assoc,he]
      simp only [Category.assoc]
      rw [←Category.assoc _ f,←Category.assoc _ g,hfg])
    m w (a ≫ e.inv)
  have hh := congrArg (fun z => z ≫ e.hom) h
  simpa only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id] using hh

private theorem shift_preserves_homotopy_congruence {A B : SyntheticSpectrum}
    (p : ℤ × ℤ) (f g : A ⟶ B)
    (hfg : ∀ (m w : ℤ) (a : BiHom m w A), a ≫ f = a ≫ g)
    (m w : ℤ) (a : BiHom m w ((SyntheticCategory.biShift p).obj A)) :
    a ≫ (SyntheticCategory.biShift p).map f = a ≫ (SyntheticCategory.biShift p).map g := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) p
  let e : F.obj (Smn (m-p.1) (w-p.2)) ≅ Smn m w :=
    (biShiftAddIso (m-p.1,w-p.2) p (m,w) (by ext <;> simp)).app S_0_0
  let a₀ := ff.preimage (e.hom ≫ a)
  have h := congrArg F.map (hfg (m-p.1) (w-p.2) a₀)
  have ha : F.map a₀ = e.hom ≫ a := ff.map_preimage _
  rw [Functor.map_comp,Functor.map_comp,ha] at h
  apply (cancel_epi e.hom).mp
  simpa only [Category.assoc] using h

private theorem shifted_sphere_quotient_endomorphism_congruence
    (p : ℤ × ℤ) (q : ℕ) (hq : 0<q)
    (f g : XModLambdaN ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q ⟶
      XModLambdaN ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q)
    (hfg : XModLambdaN.incl ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q ≫ f =
      XModLambdaN.incl ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q ≫ g)
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) q)) :
    a ≫ f = a ≫ g := by
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p
  let ff := SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) p
  let e := sphereQuotientShiftIso p q
  let f₀ := ff.preimage (e.hom ≫ f ≫ e.inv)
  let g₀ := ff.preimage (e.hom ≫ g ≫ e.inv)
  have hf : F.map f₀ = e.hom ≫ f ≫ e.inv := ff.map_preimage _
  have hg : F.map g₀ = e.hom ≫ g ≫ e.inv := ff.map_preimage _
  have he : F.map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q) ≫ e.hom =
      XModLambdaN.incl (F.obj (S_0_0 : SyntheticSpectrum)) q :=
    sphere_quotient_shift_inclusion p q
  dsimp only [F] at he
  have h₀ : XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q ≫ f₀ =
      XModLambdaN.incl (S_0_0 : SyntheticSpectrum) q ≫ g₀ := by
    apply ff.map_injective
    rw [Functor.map_comp,Functor.map_comp,hf,hg]
    simp only [←Category.assoc]
    rw [he,hfg]
  have h := shift_preserves_homotopy_congruence p f₀ g₀
    (sphere_quotient_endomorphism_congruence q hq f₀ g₀ h₀) m w (a ≫ e.inv)
  rw [hf,hg] at h
  have hh := congrArg (fun z => z ≫ e.hom) h
  simpa only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id] using hh

private theorem shifted_sphere_delta_evaluation
    (p : ℤ × ℤ) (i j : ℕ)
    (T : LambdaRhoDeltaTriangle ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) i j)
    (m w : ℤ) (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) i)) :
    a ≫ T.delta = a ≫ XModLambdaN.proj ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) i ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.incl ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) (j-i))) := by
  let A := (SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)
  obtain ⟨c,hc,hδ⟩ := complete_distinguished_triangle_morphism
    (XModLambdaN.cofiberTriangle A i) (Triangle.mk T.lambdaMap T.rho T.delta)
    (XModLambdaN.cofiberTriangle_distinguished A i) T.distinguished
    ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i)))
    (XModLambdaN.incl A j) T.lambda_quotient.symm
  change XModLambdaN A i ⟶ XModLambdaN A i at c
  change XModLambdaN.incl A i ≫ c = XModLambdaN.incl A j ≫ T.rho at hc
  have hc' : XModLambdaN.incl A i ≫ c = XModLambdaN.incl A i ≫ 𝟙 _ := by
    rw [hc,T.rho_quotient,Category.comp_id]
  have hac : a ≫ c = a := by
    simpa only [Category.comp_id] using
      shifted_sphere_quotient_endomorphism_congruence p i T.i_pos c (𝟙 _) hc' m w a
  change XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) = c ≫ T.delta at hδ
  calc
    a ≫ T.delta = (a ≫ c) ≫ T.delta := by rw [hac]
    _ = _ := by rw [Category.assoc,←hδ]

private theorem sphere_delta_evaluation
    (i j : ℕ) (T : LambdaRhoDeltaTriangle (S_0_0 : SyntheticSpectrum) i j)
    (m w : ℤ) (a : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) i)) :
    a ≫ T.delta = a ≫ XModLambdaN.proj (S_0_0 : SyntheticSpectrum) i ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map
          (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) (j-i))) := by
  let A := (S_0_0 : SyntheticSpectrum)
  obtain ⟨c,hc,hδ⟩ := complete_distinguished_triangle_morphism
    (XModLambdaN.cofiberTriangle A i) (Triangle.mk T.lambdaMap T.rho T.delta)
    (XModLambdaN.cofiberTriangle_distinguished A i) T.distinguished
    ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i)))
    (XModLambdaN.incl A j) T.lambda_quotient.symm
  change XModLambdaN A i ⟶ XModLambdaN A i at c
  change XModLambdaN.incl A i ≫ c = XModLambdaN.incl A j ≫ T.rho at hc
  have hc' : XModLambdaN.incl A i ≫ c = XModLambdaN.incl A i ≫ 𝟙 _ := by
    rw [hc,T.rho_quotient,Category.comp_id]
  have hac : a ≫ c = a := by
    simpa only [Category.comp_id] using
      sphere_quotient_endomorphism_congruence i T.i_pos c (𝟙 _) hc' m w a
  change XModLambdaN.proj A i ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.incl A (j-i))) = c ≫ T.delta at hδ
  calc
    a ≫ T.delta = (a ≫ c) ≫ T.delta := by rw [hac]
    _ = _ := by rw [Category.assoc,←hδ]

private theorem first_quotient_shift_boundary_square (p : ℤ × ℤ) :
    letI := background.exactness.shiftCommShift p
    (sphereQuotientShiftIso p 1).hom ≫
        XModLambdaN.proj ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) 1 ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-1)).map
            (XModLambdaN.incl ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) 1)) =
      (SyntheticCategory.biShift p).map
        (XModLambdaN.proj (S_0_0 : SyntheticSpectrum) 1 ≫
          (shiftFunctor SyntheticSpectrum (1:ℤ)).map
            ((SyntheticCategory.biShift (0,-1)).map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1))) ≫
      ((SyntheticCategory.biShift p).commShiftIso (1:ℤ)).hom.app
        ((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)) ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (shiftSwap p (0,-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)).inv ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map (sphereQuotientShiftIso p 1).hom) := by
  letI := background.exactness.shiftCommShift p
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p
  let G := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
  let H := shiftFunctor SyntheticSpectrum (1:ℤ)
  let A := (S_0_0 : SyntheticSpectrum)
  let Q := XModLambdaN A 1
  let incl := XModLambdaN.incl A 1
  have hs : F.map (G.map incl) ≫ (shiftSwap p (0,-1) Q).inv =
      (shiftSwap p (0,-1) A).inv ≫ G.map (F.map incl) := by
    apply (cancel_mono (shiftSwap p (0,-1) Q).hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [shiftSwap_natural]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  rw [←Category.assoc,sphere_quotient_shift_projection]
  simp only [Functor.map_comp,Category.assoc]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  have hsH := congrArg H.map hs
  simp only [Functor.map_comp] at hsH
  dsimp only [F,G,H,A,Q,incl] at hsH
  erw [reassoc_of% hsH]
  have hIncl := congrArg (fun f => H.map (G.map f)) (sphere_quotient_shift_inclusion p 1)
  simp only [Functor.map_comp] at hIncl
  dsimp only [G,H] at hIncl
  erw [hIncl]
  rfl

private def firstBoundaryShiftComparison (p : ℤ × ℤ) :
    (SyntheticCategory.biShift p).obj
        (((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))⟦(1:ℤ)⟧) ⟶
      (((SyntheticCategory.biShift (0,-1)).obj
        (XModLambdaN ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) 1))⟦(1:ℤ)⟧) := by
  letI := background.exactness.shiftCommShift p
  exact ((SyntheticCategory.biShift p).commShiftIso (1:ℤ)).hom.app _ ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (shiftSwap p (0,-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)).inv ≫
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      ((SyntheticCategory.biShift (0,-1)).map (sphereQuotientShiftIso p 1).hom)

private theorem first_delta_shift_compatibility (p : ℤ × ℤ) (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift p).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))) :
    (a ≫ (sphereQuotientShiftIso p 1).hom) ≫
      ((background.quotients.tower ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum))).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta =
    (a ≫ (SyntheticCategory.biShift p).map
      ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta) ≫ firstBoundaryShiftComparison p := by
  rw [shifted_sphere_delta_evaluation p 1 2 _ m w]
  have hbase := shift_preserves_homotopy_congruence p
    ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
      (i:=1) (j:=2) (by decide) (by decide)).delta
    (XModLambdaN.proj (S_0_0 : SyntheticSpectrum) 1 ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 1)))
    (fun m w a => sphere_delta_evaluation 1 2 _ m w a) m w a
  rw [hbase]
  change (a ≫ (sphereQuotientShiftIso p 1).hom) ≫
      XModLambdaN.proj ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) 1 ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.incl ((SyntheticCategory.biShift p).obj (S_0_0 : SyntheticSpectrum)) 1)) = _
  have h := congrArg (fun f => a ≫ f) (first_quotient_shift_boundary_square p)
  simpa only [firstBoundaryShiftComparison,Category.assoc] using h

private theorem susp_invariance_postcompose (m n k l : ℤ) {A B : SyntheticSpectrum}
    (a : BiHom m n A) (f : A ⟶ B) :
    susp_invariance m n k l A a ≫ (SyntheticCategory.biShift (k,l)).map f =
      susp_invariance m n k l B (a ≫ f) := by
  change ((SyntheticCategory.biShift_comp (m,n) (k,l)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (k,l)).map a ≫ 𝟙 _) ≫ _ =
    _ ≫ (SyntheticCategory.biShift (k,l)).map (a ≫ f) ≫ 𝟙 _
  simp only [Functor.map_comp,Category.comp_id,Category.assoc,Iso.app_inv]

private def mooreShiftedFirstSource :
    BiHom 125 132 (XModLambdaN (Smn (Syn:=SyntheticSpectrum) 1 0) 1) :=
  susp_invariance 124 132 1 0 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)
    ((KIP126.Literature.sphereFirstQuotient background 8 132).symm
      (KIP126.Computation.Standard.atom .x_124_8)) ≫
    (sphereQuotientShiftIso (1,0) 1).hom

private theorem moore_shifted_first_source_boundary :
    mooreShiftedFirstSource ≫
      ((background.quotients.tower (Smn (Syn:=SyntheticSpectrum) 1 0)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta =
    susp_invariance 124 132 1 0
      (((SyntheticCategory.biShift (0,-1)).obj (XModLambdaN (S_0_0 : SyntheticSpectrum) 1))⟦(1:ℤ)⟧)
      ((susp_invariance 123 133 1 (-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)
        (sphereAction KIP126.Literature.Standard.syntheticH0
          ((KIP126.Literature.sphereFirstQuotient background 9 132).symm
            (KIP126.Computation.Standard.atom .x_123_9)))) ≫
          (KIP126.ProofTools.Internal.Mahowald.biSuspensionIso 1
            (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)).hom) ≫
      firstBoundaryShiftComparison (1,0) := by
  dsimp only [mooreShiftedFirstSource]
  erw [first_delta_shift_compatibility (1,0) 125 132,susp_invariance_postcompose,
    moore_source_actual_boundary]
  rfl

private def mooreMayThirdSphereIso : mooreMayTriangle.obj₃ ≅ Smn (Syn:=SyntheticSpectrum) 1 0 :=
  eqToIso (congrArg (fun e : ℕ => (SyntheticCategory.biShift (0,-(e:ℤ))).obj
    mooreSuspendedSphere) moore_may_middle_exponent) ≪≫ mooreNuDeshiftedSuspensionIso

private def mooreFirstCommonSource : BiHom 125 132 (XModLambdaN mooreMayTriangle.obj₃ 1) :=
  mooreShiftedFirstSource ≫ XModLambdaN.map mooreMayThirdSphereIso.inv 1

private theorem moore_first_common_source_boundary_transport :
    mooreFirstCommonSource ≫
      ((background.quotients.tower mooreMayTriangle.obj₃).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-1)).map
          (XModLambdaN.map mooreMayThirdSphereIso.hom 1)) =
    mooreShiftedFirstSource ≫
      ((background.quotients.tower (Smn (Syn:=SyntheticSpectrum) 1 0)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta := by
  have hn := (background.quotients.natural mooreMayThirdSphereIso.hom).delta_naturality
    (i:=1) (j:=2) (by decide) (by decide)
  dsimp only [mooreFirstCommonSource]
  have hi : XModLambdaN.map mooreMayThirdSphereIso.inv 1 ≫
      XModLambdaN.map mooreMayThirdSphereIso.hom 1 = 𝟙 _ := by
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id]
  simp only [Category.assoc]
  erw [←hn,reassoc_of% hi]

end
end KIP126.Main.Internal.Moore
