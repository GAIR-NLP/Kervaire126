module
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.DetectionOperations
import all KIP126.ProofTools.StretchingRepresentatives
/-! First-quotient detection for the Mahowald comparison. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem first_label_detects_unshifted
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient background X (s,t))
    (a : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : a ≫ (background.quotients.tower (background.nu.functor.obj (X.obj background.auxiliary))).rho 1 q hq =
      firstLabel background X s t x ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x)) a := by
  have first_label_detects
      (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q) (s t : ℤ)
      (x : Ambient background X (s,t))
      (a : BiHom (t-s) t (XModLambdaN (nuZero background X) q))
      (ha : a ≫ (background.quotients.tower (nuZero background X)).rho 1 q hq = firstLabel background X s t x) :
      Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
        (regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x))
        (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) := by
    let Z := background.nu.functor.obj (X.obj background.auxiliary)
    let f : nuZero background X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
    have h0 : (s,t,t+0-(0:ℕ))=(s,t,t) := by simp
    let x0 : (background.family.obj (nuZero background X)).E₂ (s,t,t) :=
      (congrArg (fun i => ((background.family.obj (nuZero background X)).E₂ i : Type)) h0).mp
        (background.comparison.nuE2 X 0 s t 0 x)
    let xq0 (n : ℕ) := familyPageMap background.family (XModLambdaN.incl (nuZero background X) n) 2 (s,t,t) x0
    let xq (n : ℕ) := familyPageMap background.family (XModLambdaN.incl Z n) 2 (s,t,t)
      (familyPageMap background.family f 2 (s,t,t) x0)
    have map_label (n : ℕ) :
        familyPageMap background.family (XModLambdaN.map f n) 2 (s,t,t) (xq0 n) = xq n := by
      dsimp only [xq0,xq]
      rw [←ModuleCat.comp_apply,family_page_comp,←XModLambdaN.incl_naturality]
      rw [←family_page_comp,ModuleCat.comp_apply]
    have rho_label :
        familyPageMap background.family ((background.quotients.tower Z).rho 1 q hq) 2 (s,t,t) (xq q) = xq 1 := by
      dsimp only [xq]
      rw [←ModuleCat.comp_apply,family_page_comp,(background.quotients.tower Z).rho_quotient]
    have hxR := (KIP126.Literature.Standard.finite_lift_criterion X q hq s t x).mpr ⟨a,ha⟩
    have hx : x ∈ KIP126.Literature.cycles background X q (s,t) := by
      have h := ((isCycle_iff_reaches background X (q+1) (by omega) (s,t) x).mpr hxR).2
      simpa only [add_sub_cancel_right] using h
    have transport_infinity {A : SyntheticAdamsSS.{0}} {i j : Tridegree}
        (h : i=j) (x : A.E₂ i)
        (hx : ∃ e : (A.sequence.ssData i).eInfty, HasInfinityRepresentative A 2 i x e) :
        ∃ e : (A.sequence.ssData j).eInfty,
          HasInfinityRepresentative A 2 j
            ((congrArg (fun k => (A.E₂ k : Type)) h).mp x) e := by
      subst j
      exact hx
    have map_cast {A B : SyntheticSpectrum} (g : A ⟶ B) {i j : Tridegree} (h : i=j)
        (x : (background.family.obj A).E₂ i) :
        (congrArg (fun k => ((background.family.obj B).E₂ k : Type)) h).mp
          (familyPageMap background.family g 2 i x) =
        familyPageMap background.family g 2 j
          ((congrArg (fun k => ((background.family.obj A).E₂ k : Type)) h).mp x) := by
      subst j
      rfl
    have hex : ∃ e0 : ((background.family.obj (XModLambdaN (nuZero background X) q)).sequence.ssData
        (s,t,t)).eInfty, HasInfinityRepresentative (background.family.obj (XModLambdaN (nuZero background X) q)) 2 (s,t,t) (xq0 q) e0 := by
      have hh := transport_infinity h0 (finiteNuLabel background X q 0 s t 0 x)
        (shifted_finite_source_exists X q hq 0 s t x hx)
      have hl : (congrArg (fun k => ((background.family.obj (XModLambdaN (nuZero background X) q)).E₂ k : Type)) h0).mp
          (finiteNuLabel background X q 0 s t 0 x) = xq0 q :=
        map_cast (XModLambdaN.incl (nuZero background X) q) h0 (background.comparison.nuE2 X 0 s t 0 x)
      exact (congrArg (fun z => ∃ e0 : ((background.family.obj (XModLambdaN (nuZero background X) q)).sequence.ssData
        (s,t,t)).eInfty, HasInfinityRepresentative (background.family.obj (XModLambdaN (nuZero background X) q)) 2 (s,t,t) z e0) hl).mp hh
    obtain ⟨e0,he0⟩ := hex
    have he := family_infinity_representative_map (XModLambdaN.map f q) (s,t,t) _ e0 he0
    have he' : HasInfinityRepresentative (background.family.obj (XModLambdaN Z q)) 2 (s,t,t) (xq q)
        ((background.family.functor.map (XModLambdaN.map f q)).eInftyMap (s,t,t) e0) :=
      (congrArg (fun z => HasInfinityRepresentative (background.family.obj (XModLambdaN Z q)) 2 (s,t,t) z
        ((background.family.functor.map (XModLambdaN.map f q)).eInftyMap (s,t,t) e0)) (map_label q)).mp he
    have hb0 : Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X))))
        (s,t,t) (xq0 1) (firstLabel background X s t x) := by
      have transport_detects {A : SyntheticObject (coefficients := background.coefficients)} {i j : Tridegree} (h : i=j)
          (x : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ i)
          (a : BiHom (i.2.1-i.1) i.2.2 (A.obj background.nu background.auxiliary))
          (ha : Detects (background.convergence A) i x a) :
          Detects (background.convergence A) j
            ((congrArg (fun k => ((background.family.obj (A.obj background.nu background.auxiliary)).E₂ k : Type)) h).mp x)
            ((congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2 (A.obj background.nu background.auxiliary)) h).mp a) := by
        subst j
        exact ha
      have h1 : (s,t,t+0)=(s,t,t) := by simp
      have h01 : (s,t,t+0-(0:ℕ))=(s,t,t+0) := by simp only [Nat.cast_zero,sub_zero]
      let x1 : (background.family.obj (nuZero background X)).E₂ (s,t,t+0) :=
        (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h01).mp
          (background.comparison.nuE2 X 0 s t 0 x)
      let a1 : BiHom (t-s) (t+0) (XModLambdaN (nuZero background X) 1) :=
        (background.firstQuotient X 0 s t).symm x
      have hr : Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X)))) (s,t,t+0)
          (familyPageMap background.family (XModLambdaN.incl (nuZero background X) 1) 2 (s,t,t+0) x1) a1 :=
        background.comparisonCompatible.first_quotient X 0 s t x
      have hh := transport_detects h1 _ _ hr
      have cast_comp {A B C : Type} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
          hBC.mp (hAB.mp a) = hAC.mp a := by
        subst B
        subst C
        rfl
      have hx1 : (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h1).mp x1 = x0 := by
        exact cast_comp
          (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h01)
          (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h1)
          (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h0)
          (background.comparison.nuE2 X 0 s t 0 x)
      have hlabel : (congrArg (fun k => ((background.family.obj (XModLambdaN (nuZero background X) 1)).E₂ k : Type)) h1).mp
          (familyPageMap background.family (XModLambdaN.incl (nuZero background X) 1) 2 (s,t,t+0) x1) = xq0 1 :=
        (map_cast _ h1 x1).trans (congrArg (familyPageMap background.family (XModLambdaN.incl (nuZero background X) 1)
          2 (s,t,t)) hx1)
      have halabel : (congrArg (fun k : Tridegree => BiHom (k.2.1-k.1) k.2.2
          (XModLambdaN (nuZero background X) 1)) h1).mp a1 = firstLabel background X s t x := by
        rfl
      exact (congrArg₂ (fun z a => Detects (background.convergence (.quotient 1 (.shift (0,0) (.nu X))))
        (s,t,t) z a) hlabel halabel).mp hh
    have hb := detects_map (.quotient 1 (.shift (0,0) (.nu X))) (.quotient 1 (.nu X))
      (XModLambdaN.map f 1) (s,t,t) _ _ hb0
    have hb' : Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) (xq 1)
        (firstLabel background X s t x ≫ XModLambdaN.map f 1) :=
      (congrArg (fun z => Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) z
        (firstLabel background X s t x ≫ XModLambdaN.map f 1)) (map_label 1)).mp hb
    have hactual :
        (a ≫ XModLambdaN.map f q) ≫ (background.quotients.tower Z).rho 1 q hq =
          firstLabel background X s t x ≫ XModLambdaN.map f 1 := by
      rw [Category.assoc,←(background.quotients.natural f).rho_naturality,
        ←Category.assoc,ha]
    have hinj : Function.Injective ((background.family.functor.map ((background.quotients.tower Z).rho 1 q hq)).eInftyMap
        (s,t,t)).hom :=
      rho_infty_injective X 1 q (by decide) hq s t t (by omega)
    have hdet := detects_reflect (.quotient q (.nu X)) (.quotient 1 (.nu X))
      ((background.quotients.tower Z).rho 1 q hq) (s,t,t) hinj (xq q) _ he'
      (a ≫ XModLambdaN.map f q) (finite_bottom_filtration X q hq s t _)
      ((congrArg₂ (fun z b => Detects (background.convergence (.quotient 1 (.nu X))) (s,t,t) z b)
        rho_label hactual).mpr hb')
    have htarget : regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x) = xq q := by
      have h2 : (s,t,t-(0:ℕ))=(s,t,t) := by simp
      have h02 : (s,t,t+0-(0:ℕ))=(s,t,t-(0:ℕ)) := by simp only [add_zero]
      let x2 : (background.family.obj (nuZero background X)).E₂ (s,t,t-(0:ℕ)) :=
        (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h02).mp
          (background.comparison.nuE2 X 0 s t 0 x)
      have cast_comp {A B C : Type} (hAB : A=B) (hBC : B=C) (hAC : A=C) (a : A) :
          hBC.mp (hAB.mp a) = hAC.mp a := by
        subst B
        subst C
        rfl
      have hx2 : (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h2).mp x2 = x0 :=
        cast_comp
          (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h02)
          (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h2)
          (congrArg (fun k => ((background.family.obj (nuZero background X)).E₂ k : Type)) h0)
          (background.comparison.nuE2 X 0 s t 0 x)
      have regrade_cast {A : SyntheticAdamsSS.{0}} {i j : Tridegree} (h : i=j) (x : A.E₂ i) :
          regradeE2 h x = (congrArg (fun k => (A.E₂ k : Type)) h).mp x := by
        subst j
        rfl
      rw [regrade_cast]
      exact (map_cast (XModLambdaN.incl Z q) h2 _).trans (congrArg
        (familyPageMap background.family (XModLambdaN.incl Z q) 2 (s,t,t))
        ((map_cast f h2 x2).trans (congrArg (familyPageMap background.family f 2 (s,t,t)) hx2)))
    exact (congrArg (fun z => Detects (background.convergence (.quotient q (.nu X))) (s,t,t) z
      (a ≫ XModLambdaN.map f q)) htarget).mpr hdet

  let Z := background.nu.functor.obj (X.obj background.auxiliary)
  let f : nuZero background X ⟶ Z := SyntheticCategory.biShift_zero.hom.app _
  let g : Z ⟶ nuZero background X := SyntheticCategory.biShift_zero.inv.app _
  have hfg : f ≫ g = 𝟙 _ := Iso.hom_inv_id_app _ _
  have hgf : g ≫ f = 𝟙 _ := Iso.inv_hom_id_app _ _
  have hfirst : (a ≫ XModLambdaN.map g q) ≫ (background.quotients.tower (nuZero background X)).rho 1 q hq =
      firstLabel background X s t x := by
    rw [Category.assoc,←(background.quotients.natural g).rho_naturality,
      ←Category.assoc,ha,Category.assoc,←background.quotients.functoriality.map_comp,hfg,
      background.quotients.functoriality.map_id,Category.comp_id]
  have h := first_label_detects X q hq s t x (a ≫ XModLambdaN.map g q) hfirst
  have hback : (a ≫ XModLambdaN.map g q) ≫ XModLambdaN.map f q = a := by
    rw [Category.assoc,←background.quotients.functoriality.map_comp,hgf,
      background.quotients.functoriality.map_id,Category.comp_id]
  exact (congrArg (fun a => Detects (background.convergence (.quotient q (.nu X))) (s,t,t)
    (regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x)) a) hback).mp h

end
end KIP126.ProofTools.Internal.Mahowald
