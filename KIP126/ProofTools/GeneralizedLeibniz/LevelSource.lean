module

public import KIP126.ProofTools.Language
import all KIP126.ProofTools.GeneralizedLeibniz.LeftEdge

/-! Intrinsic finite source labels at every lambda level, transported through
the fixed shift and a quotient comparison retaining its boundary square. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 200000
set_option Elab.async false

/-- The selected quotient shift carries both the inclusion square and the
absolute-boundary square. This is the same actual comparison throughout. -/
@[no_expose] public def levelQuotientShiftIso (X : AdamsObject (coefficients := background.coefficients)) (e : ℤ) (q : ℕ) :
    XModLambdaN ((SyntheticCategory.biShift (0,e)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift (0,e)).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
  (quotient_boundary_shift_natural_exists
    (background.nu.functor.obj (X.obj background.auxiliary)) e q).choose

private theorem level_quotient_shift_incl (X : AdamsObject (coefficients := background.coefficients)) (e : ℤ) (q : ℕ) :
    XModLambdaN.incl _ q ≫ (levelQuotientShiftIso X e q).hom =
      (SyntheticCategory.biShift (0,e)).map
        (XModLambdaN.incl (background.nu.functor.obj (X.obj background.auxiliary)) q) :=
  (quotient_boundary_shift_natural_exists
    (background.nu.functor.obj (X.obj background.auxiliary)) e q).choose_spec.1

private theorem level_quotient_shift_boundary (X : AdamsObject (coefficients := background.coefficients)) (e : ℤ) (q : ℕ) :
    (levelQuotientShiftIso X e q).hom ≫ (SyntheticCategory.biShift (0,e)).map
      (absoluteBoundary (background.nu.functor.obj (X.obj background.auxiliary)) q) ≫
      (boundaryShiftNatIso e q).hom.app (background.nu.functor.obj (X.obj background.auxiliary)) =
        absoluteBoundary ((SyntheticCategory.biShift (0,e)).obj
          (background.nu.functor.obj (X.obj background.auxiliary))) q :=
  (quotient_boundary_shift_natural_exists
    (background.nu.functor.obj (X.obj background.auxiliary)) e q).choose_spec.2

/-- The shifted image of the native finite label `lambda^k x`, using
the specified quotient-shift construction. -/
private def levelFiniteSourceLabel (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ)
    (e s t : ℤ) (k : ℕ) (x : Ambient background X (s,t)) :
    (background.family.obj ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj
      background.nu background.auxiliary)).E₂ (s,(t-s)+s,t+e-k) :=
  familyPageMap background.family (levelQuotientShiftIso X e q).inv 2 _
    (regradeE2 (by ext <;> dsimp <;> omega)
      (((essShift (0,e)).page (.quotient q (.nu X)) 2 (by decide) (t-s,t-k) s).hom
        (regradeE2 (by simp) (finiteTargetLabel background X q s t k x))))

private def levelFiniteSourceInfinity (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ)
    (e s t : ℤ) (k : ℕ)
    (z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (s,t,t-k)).eInfty) :
    ((background.family.obj ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj
      background.nu background.auxiliary)).sequence.ssData (s,(t-s)+s,t+e-k)).eInfty := by
  let A : SyntheticObject (coefficients := background.coefficients) := .quotient q (.nu X)
  let p : ℤ × ℤ := (t-s,t-k)
  let δ : ℤ × ℤ := (0,e)
  let I := towerInfinityIso (background.convergence A) (background.convergence (.shift δ A))
    ((essShift δ).filtered A p) s
  let z0 : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj
      (A.obj background.nu background.auxiliary)).sequence.ssData i).eInfty)
      (show (s,t,t-k)=(s,p.1+s,p.2) by simp [p]))) z
  let zs := I.hom z0
  let zs' : ((background.family.obj ((SyntheticObject.shift δ A).obj
      background.nu background.auxiliary)).sequence.ssData (s,(t-s)+s,t+e-k)).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj ((SyntheticObject.shift δ A).obj
      background.nu background.auxiliary)).sequence.ssData i).eInfty)
      (show (s,(p+δ).1+s,(p+δ).2)=(s,(t-s)+s,t+e-k) by
        ext <;> dsimp [p,δ] <;> omega))) zs
  exact (background.family.map (levelQuotientShiftIso X e q).inv).eInftyMap
    (s,(t-s)+s,t+e-k) zs'


set_option maxHeartbeats 100000 in
private theorem level_finite_source_representative (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ)
    (e s t : ℤ) (k : ℕ) (x : Ambient background X (s,t))
    (z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (s,t,t-k)).eInfty)
    (hz : HasInfinityRepresentative (background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
        background.nu background.auxiliary)) 2 (s,t,t-k)
      (finiteTargetLabel background X q s t k x) z) :
    HasInfinityRepresentative (background.family.obj ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj
      background.nu background.auxiliary)) 2 (s,(t-s)+s,t+e-k)
      (levelFiniteSourceLabel X q e s t k x)
      (levelFiniteSourceInfinity X q e s t k z) := by
  let A : SyntheticObject (coefficients := background.coefficients) := .quotient q (.nu X)
  let p : ℤ × ℤ := (t-s,t-k)
  let δ : ℤ × ℤ := (0,e)
  let i0 : Tridegree := (s,p.1+s,p.2)
  let iS : Tridegree := (s,(p+δ).1+s,(p+δ).2)
  let iN : Tridegree := (s,(t-s)+s,t+e-k)
  let h0 : (s,t,t-k)=i0 := by simp [i0,p]
  let hS : iS=iN := by ext <;> dsimp [iS,iN,p,δ] <;> omega
  let x0 : (background.family.obj (A.obj background.nu background.auxiliary)).E₂ i0 :=
    regradeE2 h0 (finiteTargetLabel background X q s t k x)
  let z0 : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData i0).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj
      (A.obj background.nu background.auxiliary)).sequence.ssData i).eInfty) h0)) z
  have hz0 : HasInfinityRepresentative (background.family.obj (A.obj background.nu background.auxiliary))
      2 i0 x0 z0 := representative_transport h0 _ _ hz
  let xS : (background.family.obj ((SyntheticObject.shift δ A).obj background.nu background.auxiliary)).E₂ iS :=
    ((essShift δ).page A 2 (by decide) p s).hom x0
  let I := towerInfinityIso (background.convergence A) (background.convergence (.shift δ A))
    ((essShift δ).filtered A p) s
  let zS : ((background.family.obj ((SyntheticObject.shift δ A).obj
      background.nu background.auxiliary)).sequence.ssData iS).eInfty := I.hom z0
  have hzS : HasInfinityRepresentative (background.family.obj
      ((SyntheticObject.shift δ A).obj background.nu background.auxiliary)) 2 iS xS zS :=
    ((essShift δ).representative_iff A 2 (by decide) p s x0 z0).mp hz0
  let xN : (background.family.obj ((SyntheticObject.shift δ A).obj
      background.nu background.auxiliary)).E₂ iN := regradeE2 hS xS
  let zN : ((background.family.obj ((SyntheticObject.shift δ A).obj
      background.nu background.auxiliary)).sequence.ssData iN).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj ((SyntheticObject.shift δ A).obj
      background.nu background.auxiliary)).sequence.ssData i).eInfty) hS)) zS
  have hzN : HasInfinityRepresentative (background.family.obj
      ((SyntheticObject.shift δ A).obj background.nu background.auxiliary)) 2 iN xN zN :=
    representative_transport hS xS zS hzS
  exact family_infinity_representative_map (levelQuotientShiftIso X e q).inv iN xN zN hzN


private theorem level_finite_source_infinity_eq (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ)
    (e s t : ℤ) (k : ℕ) (x : Ambient background X (s,t))
    (z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (s,t,t-k)).eInfty)
    (hz : HasInfinityRepresentative (background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
        background.nu background.auxiliary)) 2 (s,t,t-k)
      (finiteTargetLabel background X q s t k x) z)
    (zN : ((background.family.obj ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj
      background.nu background.auxiliary)).sequence.ssData (s,(t-s)+s,t+e-k)).eInfty)
    (hzN : HasInfinityRepresentative (background.family.obj ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj
        background.nu background.auxiliary)) 2 (s,(t-s)+s,t+e-k)
      (levelFiniteSourceLabel X q e s t k x) zN) :
    levelFiniteSourceInfinity X q e s t k z = zN :=
  (level_finite_source_representative X q e s t k x z hz).unique hzN

/-- At level zero the intrinsic source agrees at infinity with every original
normalized-label representative; the public comparison remains unchanged. -/
private theorem level_finite_source_zero_compatible
    (X : AdamsObject (coefficients := background.coefficients)) (q : ℕ) (hq : 0 < q)
    (e s t : ℤ) (he : e = 0 ∨ e = 1)
    (x : Ambient background X (s,t))
    (z : ((background.family.obj ((SyntheticObject.quotient q (.nu X)).obj
      background.nu background.auxiliary)).sequence.ssData (s,t,t-(0:ℕ))).eInfty)
    (hz : HasInfinityRepresentative _ 2 (s,t,t-(0:ℕ))
      (finiteTargetLabel background X q s t 0 x) z)
    (zN : ((background.family.obj ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj
      background.nu background.auxiliary)).sequence.ssData
        (s,(t-s)+s,t+e-(0:ℕ))).eInfty)
    (hzN : HasInfinityRepresentative _ 2 (s,(t-s)+s,t+e-(0:ℕ))
      (regradeE2 (by simp) (finiteNuLabel background X q e s t 0 x)) zN) :
    levelFiniteSourceInfinity X q e s t 0 z = zN := by
  let A : SyntheticObject (coefficients := background.coefficients) := .quotient q (.nu X)
  let B : SyntheticObject (coefficients := background.coefficients) := .quotient q (.shift (0,e) (.nu X))
  let δ : ℤ × ℤ := (0,e)
  let p : ℤ × ℤ := (t-s,t)
  let p0 : ℤ × ℤ := (t-s,t-(0:ℕ))
  let ε := levelQuotientShiftIso X e q
  let h0 : (s,t,t-(0:ℕ)) = (s,t,t) := by simp
  let hN : (s,(t-s)+s,t+e-(0:ℕ)) =
      (s,(p+δ).1+s,(p+δ).2) := by ext <;> dsimp [p,δ] <;> omega
  let z0 : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
      (s,t,t)).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj
      (A.obj background.nu background.auxiliary)).sequence.ssData i).eInfty) h0)) z
  let zN0 : ((background.family.obj (B.obj background.nu background.auxiliary)).sequence.ssData
      (s,(p+δ).1+s,(p+δ).2)).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj
      (B.obj background.nu background.auxiliary)).sequence.ssData i).eInfty) hN)) zN
  have hz0 : HasInfinityRepresentative _ 2 (s,t,t)
      (regradeE2 (by simp) (finiteTargetLabel background X q s t 0 x)) z0 :=
    representative_transport h0 _ _ hz
  have hzN0 : HasInfinityRepresentative _ 2 (s,(p+δ).1+s,(p+δ).2)
      (regradeE2 (by ext <;> dsimp [p,δ] <;> omega)
        (finiteNuLabel background X q e s t 0 x)) zN0 := by
    simpa only [normalized_regrade_trans] using representative_transport hN _ _ hzN
  have hold := normalized_finite_source_infinity_shift X q hq e s t he ε
    (level_quotient_shift_incl X e q) x z0 hz0 zN0 hzN0
  let a0 : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
      (s,p0.1+s,p0.2)).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj
      (A.obj background.nu background.auxiliary)).sequence.ssData i).eInfty)
      (show (s,t,t-(0:ℕ)) = (s,p0.1+s,p0.2) by simp [p0]))) z
  let a1 : ((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty :=
    (eqToHom (congrArg (fun i => ((background.family.obj
      (A.obj background.nu background.auxiliary)).sequence.ssData i).eInfty)
      (show (s,t,t) = (s,p.1+s,p.2) by simp [p]))) z0
  have ha : HEq a0 a1 :=
    (eqToHom_apply_heq _ z).trans
      ((eqToHom_apply_heq _ z0).trans (eqToHom_apply_heq _ z)).symm
  have hshift := left_infinity_shift_heq A δ p0 p s s (by simp [p0,p]) rfl a0 a1 ha
  have hlevel : HEq (levelFiniteSourceInfinity X q e s t 0 z)
      ((background.family.map ε.inv).eInftyMap (s,(p+δ).1+s,(p+δ).2)
        ((towerInfinityIso (background.convergence A) (background.convergence (.shift δ A))
          ((essShift δ).filtered A p) s).hom a1)) := by
    dsimp only [levelFiniteSourceInfinity]
    apply left_infinity_map_heq ε.inv _ _ hN
    exact (eqToHom_apply_heq _ _).trans hshift
  exact eq_of_heq (hlevel.trans ((heq_of_eq hold).trans (eqToHom_apply_heq _ zN)))

end
end KIP126.ProofTools.Internal.Leibniz
