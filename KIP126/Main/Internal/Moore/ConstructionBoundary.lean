module

import KIP126.ProofTools.Operations
import KIP126.SSComputation.Table
import KIP126.AdamsComputation.Table.Values

/-! Exact first-quotient boundary coordinates used in the Moore construction.
These lemmas retain the actual Bockstein arrow and the fixed first-quotient
comparison. A classical differential supplies the boundary of that same
first-quotient representative. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

private theorem first_bockstein_label_of_d2
    (x : background.classical.sphere.Page 2 (8,132))
    (y : background.classical.sphere.Page 2 (10,133))
    (hd : HasDifferential background.classical.sphere 2 (8,132) (10,133) x y) :
    bocksteinLabel background .sphere 1 (by decide) 8 132
      (firstLabel background .sphere 8 132 x) = y := by
  obtain ⟨a,ha,hd'⟩ := KIP126.Literature.Standard.bockstein_differential
    .sphere 1 (by decide) 8 132 x ⟨x,RepresentsOnPage.self_two x⟩
  have ha' : a = firstLabel background .sphere 8 132 x := by
    simpa only [(background.quotients.tower (nuZero background .sphere)).rho_id,
      Category.comp_id] using ha
  subst a
  exact hd'.eq_on_page_two.2.symm.trans hd.eq_on_page_two.2

private theorem first_boundary_coordinate_of_d2
    (x : background.classical.sphere.Page 2 (8,132))
    (y : background.classical.sphere.Page 2 (10,133))
    (hd : HasDifferential background.classical.sphere 2 (8,132) (10,133) x y) :
    (susp_invariance 123 133 1 (-1)
      (XModLambdaN (nuZero background .sphere) 1)).symm
      (firstLabel background .sphere 8 132 x ≫
        bocksteinArrow background .sphere 1 (by decide)) =
      firstLabel background .sphere 10 133 y := by
  rw [← first_bockstein_label_of_d2 x y hd]
  let z := (susp_invariance 123 133 1 (-1)
      (XModLambdaN (nuZero background .sphere) 1)).symm
      (firstLabel background .sphere 8 132 x ≫
        bocksteinArrow background .sphere 1 (by decide))
  change z = (background.firstQuotient .sphere 0 10 133).symm
    ((background.firstQuotient .sphere 0 10 133) z)
  exact ((background.firstQuotient .sphere 0 10 133).symm_apply_apply z).symm

private theorem first_label_sphere_transport (s t : ℤ)
    (x : background.classical.sphere.Page 2 (s,t)) :
    firstLabel background .sphere s t x ≫ XModLambdaN.map
      (SyntheticCategory.biShift_zero.hom.app _ ≫ background.nu.unitIso.hom) 1 =
      (KIP126.Literature.sphereFirstQuotient background s t).symm x := by
  apply (KIP126.Literature.sphereFirstQuotient background s t).injective
  rw [LinearEquiv.apply_symm_apply]
  exact sphere_first_quotient_label s t x

private theorem first_quotient_h0_product
    (v : background.classical.sphere.Page 2 (9,132)) :
    (KIP126.Literature.sphereFirstQuotient background 10 133).symm
      (background.sphereAlgebra.product (1,1) (9,132)
        (background.standardClasses.standardHi 0) v) =
      sphereAction KIP126.Literature.Standard.syntheticH0
        ((KIP126.Literature.sphereFirstQuotient background 9 132).symm v) := by
  apply (KIP126.Literature.sphereFirstQuotient background 10 133).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := KIP126.Literature.Standard.first_quotient_action 1 1 9 132
    KIP126.Literature.Standard.syntheticH0
    ((KIP126.Literature.sphereFirstQuotient background 9 132).symm v)
  change KIP126.Literature.sphereFirstQuotient background 10 133
      (sphereAction KIP126.Literature.Standard.syntheticH0
        ((KIP126.Literature.sphereFirstQuotient background 9 132).symm v)) =
      background.sphereAlgebra.product (1,1) (9,132)
        (KIP126.Literature.sphereFirstQuotient background 1 1
          (quotientClass 1 KIP126.Literature.Standard.syntheticH0))
        (KIP126.Literature.sphereFirstQuotient background 9 132
          ((KIP126.Literature.sphereFirstQuotient background 9 132).symm v)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change _ = background.sphereAlgebra.product (1,1) (9,132)
    (KIP126.AdamsSynthetic.sphereFirstQuotient background.nu
      background.quotients.functoriality background.firstQuotient 1 1
        (quotientClass 1 KIP126.Literature.Standard.syntheticH0)) v at h
  rw [KIP126.Literature.Standard.syntheticH0_first_quotient_label] at h
  exact h.symm

private theorem first_boundary_h0_coordinate_of_d2
    (x : background.classical.sphere.Page 2 (8,132))
    (v : background.classical.sphere.Page 2 (9,132))
    (hd : HasDifferential background.classical.sphere 2 (8,132) (10,133) x
      (background.sphereAlgebra.product (1,1) (9,132)
        (background.standardClasses.standardHi 0) v)) :
    ((susp_invariance 123 133 1 (-1)
      (XModLambdaN (nuZero background .sphere) 1)).symm
      (firstLabel background .sphere 8 132 x ≫
        bocksteinArrow background .sphere 1 (by decide))) ≫
      XModLambdaN.map
        (SyntheticCategory.biShift_zero.hom.app _ ≫ background.nu.unitIso.hom) 1 =
      sphereAction KIP126.Literature.Standard.syntheticH0
        ((KIP126.Literature.sphereFirstQuotient background 9 132).symm v) := by
  rw [first_boundary_coordinate_of_d2 x _ hd,first_label_sphere_transport,
    first_quotient_h0_product]

private theorem first_actual_boundary_of_d2
    (x : background.classical.sphere.Page 2 (8,132))
    (y : background.classical.sphere.Page 2 (10,133))
    (hd : HasDifferential background.classical.sphere 2 (8,132) (10,133) x y) :
    firstLabel background .sphere 8 132 x ≫
      ((background.quotients.tower (nuZero background .sphere)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta =
    susp_invariance 123 133 1 (-1) (XModLambdaN (nuZero background .sphere) 1)
      (firstLabel background .sphere 10 133 y) ≫
        (biSuspensionIso 1 (XModLambdaN (nuZero background .sphere) 1)).hom := by
  have h := congrArg (susp_invariance 123 133 1 (-1)
    (XModLambdaN (nuZero background .sphere) 1))
    (first_boundary_coordinate_of_d2 x y hd)
  rw [Equiv.apply_symm_apply] at h
  have harrow : bocksteinArrow background .sphere 1 (by decide) =
      ((background.quotients.tower (nuZero background .sphere)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta ≫
        (biSuspensionIso 1 (XModLambdaN (nuZero background .sphere) 1)).inv := by
    have hcast {A A' B : SyntheticSpectrum} (h : A=A') (e : A ≅ B)
        (he : (A ≅ B) = (A' ≅ B)) :
        (he.mp e).inv = e.inv ≫ eqToHom h := by
      subst A'
      change e.inv = e.inv ≫ 𝟙 A
      exact (Category.comp_id _).symm
    simp only [bocksteinArrow,biSuspensionIso]
    rw [hcast (congrArg (fun p : ℤ × ℤ => (SyntheticCategory.biShift p).obj
      (XModLambdaN (nuZero background .sphere) 1)) (by ext <;> simp))]
    simp only [Iso.trans_inv,Iso.app_inv,Iso.symm_inv,
      eqToHom_refl,Category.comp_id]
    rfl
  apply (cancel_mono
    (biSuspensionIso 1 (XModLambdaN (nuZero background .sphere) 1)).inv).mp
  simpa only [harrow,Category.assoc,Iso.hom_inv_id,Category.comp_id] using h

private theorem first_bi_suspension_natural {A B : SyntheticSpectrum} (f : A ⟶ B) :
    (SyntheticCategory.biShift (1,-1)).map f ≫ (biSuspensionIso 1 B).hom =
      (biSuspensionIso 1 A).hom ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-1)).map f) := by
  let e : (SyntheticCategory.biShift ((0,-1)+(1,0)) : SyntheticSpectrum ⥤ _) ≅
      SyntheticCategory.biShift (0,-1) ⋙ shiftFunctor SyntheticSpectrum (1:ℤ) :=
    (SyntheticCategory.biShift_comp (0,-1) (1,0)).symm ≪≫
      Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-1))
        (SyntheticCategory.biShift_compat 1)
  exact e.hom.naturality f

private theorem first_suspension_natural {A B : SyntheticSpectrum} (f : A ⟶ B)
    (a : BiHom 123 133 A) :
    susp_invariance 123 133 1 (-1) A a ≫ (SyntheticCategory.biShift (1,-1)).map f =
      susp_invariance 123 133 1 (-1) B (a ≫ f) := by
  change ((SyntheticCategory.biShift_comp (123,133) (1,-1)).inv.app S_0_0 ≫
      (SyntheticCategory.biShift (1,-1)).map a ≫ 𝟙 _) ≫ _ =
    _ ≫ (SyntheticCategory.biShift (1,-1)).map (a ≫ f) ≫ 𝟙 _
  simp only [Functor.map_comp,Category.comp_id,Category.assoc,Iso.app_inv]

private theorem sphere_first_actual_boundary_of_d2
    (x : background.classical.sphere.Page 2 (8,132))
    (y : background.classical.sphere.Page 2 (10,133))
    (hd : HasDifferential background.classical.sphere 2 (8,132) (10,133) x y) :
    (KIP126.Literature.sphereFirstQuotient background 8 132).symm x ≫
      ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta =
    susp_invariance 123 133 1 (-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)
      ((KIP126.Literature.sphereFirstQuotient background 10 133).symm y) ≫
        (biSuspensionIso 1 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)).hom := by
  let f : nuZero background .sphere ⟶ (S_0_0 : SyntheticSpectrum) :=
    SyntheticCategory.biShift_zero.hom.app _ ≫ background.nu.unitIso.hom
  have hn := (background.quotients.natural f).delta_naturality
    (i:=1) (j:=2) (by decide) (by decide)
  dsimp only [f] at hn
  rw [← first_label_sphere_transport 8 132 x,Category.assoc]
  erw [hn,
    ← Category.assoc,first_actual_boundary_of_d2 x y hd]
  erw [Category.assoc,← first_bi_suspension_natural,← Category.assoc,
    first_suspension_natural]
  erw [first_label_sphere_transport]

private theorem sphere_first_actual_h0_boundary_of_d2
    (x : background.classical.sphere.Page 2 (8,132))
    (v : background.classical.sphere.Page 2 (9,132))
    (hd : HasDifferential background.classical.sphere 2 (8,132) (10,133) x
      (background.sphereAlgebra.product (1,1) (9,132)
        (background.standardClasses.standardHi 0) v)) :
    (KIP126.Literature.sphereFirstQuotient background 8 132).symm x ≫
      ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta =
    susp_invariance 123 133 1 (-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)
      (sphereAction KIP126.Literature.Standard.syntheticH0
        ((KIP126.Literature.sphereFirstQuotient background 9 132).symm v)) ≫
        (biSuspensionIso 1 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)).hom := by
  rw [sphere_first_actual_boundary_of_d2 x _ hd,first_quotient_h0_product]

private theorem moore_source_d2 :
    HasDifferential background.classical.sphere 2 (8,132) (10,133)
      (KIP126.Computation.Standard.atom .x_124_8)
      (background.sphereAlgebra.product (1,1) (9,132)
        (background.standardClasses.standardHi 0)
        (KIP126.Computation.Standard.atom .x_123_9)) := by
  have hrow := KIP126.Computation.Table.result
    ⟨.sphere,.equation,2,8,132,[0],10,133,[2]⟩ (by
      exact List.mem_of_getElem? (i:=51) (by rfl))
  dsimp only [KIP126.Computation.Table.Statement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  have vx : KIP126.Computation.Table.Raw.coordinatesValid
    KIP126.Computation.Table.Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : KIP126.Computation.Table.Raw.coordinatesValid
    KIP126.Computation.Table.Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [KIP126.Computation.Table.decode,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  have hbX : KIP126.Computation.Table.basis .sphere 8 132 0 =
      KIP126.Computation.Standard.atom .x_124_8 := by
    exact KIP126.Computation.Table.basis_value ⟨.named .x_124_8,0⟩ (by decide)
  have hbY : KIP126.Computation.Table.basis .sphere 10 133 2 =
      background.sphereAlgebra.product (1,1) (9,132)
        (background.standardClasses.standardHi 0)
        (KIP126.Computation.Standard.atom .x_123_9) := by
    have h := KIP126.Computation.Table.basis_value
      ⟨.mul (.named .h0) (.named .x_123_9),2⟩ (by decide)
    simpa [KIP126.Computation.Table.Expression.value,
      KIP126.Computation.Table.Expression.degree,KIP126.Computation.Standard.atom_h0,
      KIP126.Computation.Standard.product]
      using h
  rw [←hx,←hy,hbX,hbY] at hd
  exact hd

private theorem moore_source_actual_boundary :
    (KIP126.Literature.sphereFirstQuotient background 8 132).symm
        (KIP126.Computation.Standard.atom .x_124_8) ≫
      ((background.quotients.tower (S_0_0 : SyntheticSpectrum)).triangle
        (i:=1) (j:=2) (by decide) (by decide)).delta =
    susp_invariance 123 133 1 (-1) (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)
      (sphereAction KIP126.Literature.Standard.syntheticH0
        ((KIP126.Literature.sphereFirstQuotient background 9 132).symm
          (KIP126.Computation.Standard.atom .x_123_9))) ≫
        (biSuspensionIso 1 (XModLambdaN (S_0_0 : SyntheticSpectrum) 1)).hom :=
  sphere_first_actual_h0_boundary_of_d2 _ _ moore_source_d2

end
end KIP126.Main.Internal.Moore
