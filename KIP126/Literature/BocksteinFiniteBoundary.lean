module
import all KIP126.Literature.BocksteinLambdaCycles

/-! The existing raw-tower differential evaluated on a specified finite
composite-cofiber lift. All maps and representatives stay fixed. -/
@[expose] section
namespace KIP126.Literature.BocksteinFiniteBoundaryConstruction
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.Literature.BocksteinRaw
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]

private theorem raw_differential_of_finite_composite_lift
    (T : RawTower C) (r : ℤ) (hr : 1 ≤ r) (p : ℤ × ℤ)
    (z : (Subobject.underlying.obj
      ((towerSSData T p).Z (↑(r-1).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (a : HomotopyGroup (p.2-p.1)
      (HasFunctorialCofiber.cofib
        (T.mapAt (show p.1+1 ≤ p.1+r by omega) ≫
          T.mapAt (show p.1 ≤ p.1+1 by omega))))
    (ha : a ≫ cofiberCompositeMap
      (T.mapAt (show p.1+1 ≤ p.1+r by omega))
      (T.mapAt (show p.1 ≤ p.1+1 by omega)) = cycleRep T p (r-1).toNat z) :
    towerD T r p ((towerSSData T p).pageπ _ z) =
      layerPage T (p+(r,r-1)) (r-1).toNat
        (degreeCast (by dsimp; omega : p.2-p.1-1 = (p+(r,r-1)).2-(p+(r,r-1)).1)
          (RawTower.desuspend (T.stageAt (p.1+r)) (p.2-p.1)
            (a ≫ HasFunctorialCofiber.cofibδ
              (T.mapAt (show p.1+1 ≤ p.1+r by omega) ≫
                T.mapAt (show p.1 ≤ p.1+1 by omega))))) := by
  rw [towerD_pageπ T r hr p z]
  apply differentialValue_of_lift
  let g := T.mapAt (show p.1+1 ≤ p.1+r by omega)
  let f := T.mapAt (show p.1 ≤ p.1+1 by omega)
  have hδ : cofiberCompositeMap g f ≫ HasFunctorialCofiber.cofibδ f =
      HasFunctorialCofiber.cofibδ (g ≫ f) ≫ (shiftFunctor C (1 : ℤ)).map g :=
    HasFunctorialCofiber.cofibMap_δ _ _ _ _ _
  change RawTower.desuspend _ _ (a ≫ HasFunctorialCofiber.cofibδ (g ≫ f)) ≫ g =
    RawTower.desuspend _ _ (cycleRep T p (r-1).toNat z ≫ HasFunctorialCofiber.cofibδ f)
  rw [← ha, Category.assoc, hδ, ← Category.assoc, raw_desuspend_natural]

end
end KIP126.Literature.BocksteinFiniteBoundaryConstruction

@[expose] section
namespace KIP126.Literature.BocksteinFiniteBoundaryConstruction
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Core.SpectralSequence
open KIP126.Literature.BocksteinRaw
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The shifted finite quotient lift supplies the connecting lift for
the raw lambda tower on the same representative. -/
private theorem lambda_finite_lift_connecting
    (coh : BiShiftCoherence Syn) (X : Syn) (k q : ℕ) (hq : 1 ≤ q) (n : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).IsTriangulated]
    (x : (lambdaTower X).FirstPage ((k:ℤ),n))
    (a : HomotopyGroup (n-k)
      ((SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN X q)))
    (ha : a ≫ (SyntheticCategory.biShift (lambdaDegree k)).map
      (XModLambdaN.restriction coh X 1 q hq) = x ≫ (lambdaLayerIso X k).hom) :
    x ≫ HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k)) =
      a ≫ (SyntheticCategory.biShift (lambdaDegree k)).map (XModLambdaN.proj X q) ≫
        ((SyntheticCategory.biShift (lambdaDegree k)).commShiftIso (1:ℤ)).hom.app
          ((SyntheticCategory.biShift (lambdaDegree q)).obj X) ≫
        (shiftFunctor Syn (1:ℤ)).map ((lambdaShiftAddIso q k (k+q) (by omega)).hom.app X) ≫
        (shiftFunctor Syn (1:ℤ)).map ((lambdaTower X).map (show k+1 ≤ k+q by omega)) := by
  let F := SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)
  let eA := (shiftFunctor Syn (1:ℤ)).mapIso
    ((lambdaShiftAddIso q k (k+q) (by omega)).symm.app X)
  let eB := (shiftFunctor Syn (1:ℤ)).mapIso
    ((lambdaShiftAddIso 1 k (k+1) (by omega)).symm.app X)
  let g := (shiftFunctor Syn (1:ℤ)).map
    ((lambdaTower X).map (show k+1 ≤ k+q by omega))
  let g' := (shiftFunctor Syn (1:ℤ)).map
    (F.map (lambdaRestrictionSourceMap 1 q hq X))
  have he : g ≫ eB.hom = eA.hom ≫ g' := by
    change (shiftFunctor Syn (1:ℤ)).map _ ≫ (shiftFunctor Syn (1:ℤ)).map _ =
      (shiftFunctor Syn (1:ℤ)).map _ ≫ (shiftFunctor Syn (1:ℤ)).map _
    rw [← Functor.map_comp, ← Functor.map_comp, lambdaTower_map coh X]
    exact (shiftFunctor Syn (1:ℤ)).congr_map
      (lambdaRestrictionSourceMap_shift_square coh X k q hq)
  have hδ : F.map (XModLambdaN.restriction coh X 1 q hq) ≫
        F.map (XModLambdaN.proj X 1) ≫
        (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) =
      (F.map (XModLambdaN.proj X q) ≫
        (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree q)).obj X)) ≫ g' := by
    have h := HasFunctorialCofiber.cofibMap_δ (lambdaPow q X) (lambdaPow 1 X)
      (lambdaRestrictionSourceMap 1 q hq X) (𝟙 X)
      (by simpa only [lambdaDegree, Category.comp_id] using
        lambdaRestrictionSourceMap_commutes coh 1 q hq X)
    change XModLambdaN.restriction coh X 1 q hq ≫ XModLambdaN.proj X 1 =
      XModLambdaN.proj X q ≫ (shiftFunctor Syn (1:ℤ)).map
        (lambdaRestrictionSourceMap 1 q hq X) at h
    rw [← F.map_comp_assoc, h, F.map_comp]
    simp only [Category.assoc, F.commShiftIso_hom_naturality]
    rfl
  have hb : (x ≫ HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k))) ≫
      eB.hom = (x ≫ (lambdaLayerIso X k).hom) ≫ F.map (XModLambdaN.proj X 1) ≫
        (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree 1)).obj X) := by
    change (x ≫ HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k))) ≫
      (shiftFunctor Syn (1:ℤ)).map ((lambdaShiftAddIso 1 k (k+1) (by omega)).inv.app X) = _
    rw [Category.assoc, lambdaLayerIso_boundary]
    exact (Category.assoc _ _ _).symm
  apply (cancel_mono eB.hom).mp
  change (x ≫ HasFunctorialCofiber.cofibδ ((lambdaTower X).map (Nat.le_succ k))) ≫
      eB.hom =
    (a ≫ F.map (XModLambdaN.proj X q) ≫
      (F.commShiftIso (1:ℤ)).hom.app ((SyntheticCategory.biShift (lambdaDegree q)).obj X) ≫
      eA.inv ≫ g) ≫ eB.hom
  rw [hb, ← ha]
  simp only [Category.assoc, he, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (fun f => a ≫ f) hδ

private def lambdaFiniteQuotientStageBoundary
    (X : Syn) (k q : ℕ) (n : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).CommShift ℤ]
    (a : HomotopyGroup (n-k)
      ((SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN X q))) :
    HomotopyGroup (n-k) (((lambdaTower X).stageAt ((k:ℤ)+q))⟦(1:ℤ)⟧) := by
  exact a ≫ (SyntheticCategory.biShift (lambdaDegree k)).map (XModLambdaN.proj X q) ≫
    ((SyntheticCategory.biShift (lambdaDegree k)).commShiftIso (1:ℤ)).hom.app
      ((SyntheticCategory.biShift (lambdaDegree q)).obj X) ≫
    (shiftFunctor Syn (1:ℤ)).map
      ((lambdaShiftAddIso q k (((k:ℤ)+q).toNat) (by omega)).hom.app X)

private theorem lambda_finite_lift_connecting_at
    (coh : BiShiftCoherence Syn) (X : Syn) (k q : ℕ) (hq : 1 ≤ q) (n : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).IsTriangulated]
    (x : (lambdaTower X).FirstPage ((k:ℤ),n))
    (a : HomotopyGroup (n-k)
      ((SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN X q)))
    (ha : a ≫ (SyntheticCategory.biShift (lambdaDegree k)).map
      (XModLambdaN.restriction coh X 1 q hq) = x ≫ (lambdaLayerIso X k).hom) :
    lambdaFiniteQuotientStageBoundary X k q n a ≫
        (shiftFunctor Syn (1:ℤ)).map
          ((lambdaTower X).mapAt (show (k:ℤ)+1 ≤ (k:ℤ)+q by omega)) =
      x ≫ HasFunctorialCofiber.cofibδ
        ((lambdaTower X).mapAt (show (k:ℤ) ≤ (k:ℤ)+1 by omega)) := by
  have h := (lambda_finite_lift_connecting coh X k q hq n x a ha).symm
  have hkq : ((k:ℤ)+(q:ℤ)).toNat=k+q := by omega
  have hk1 : ((k:ℤ)+1).toNat=k+1 := by omega
  unfold lambdaFiniteQuotientStageBoundary
  dsimp only [RawTower.mapAt, RawTower.stageAt]
  convert! h using 1 <;>
    simp only [hkq, hk1, Int.toNat_natCast, Category.assoc]
  congr! 8

/-- The actual finite quotient boundary, desuspended once, evaluates the
existing raw differential at its finite cycle representative. -/
private theorem lambda_differential_of_shifted_finite_lift
    (coh : BiShiftCoherence Syn) (X : Syn) (k q : ℕ) (hq : 1 ≤ q) (n : ℤ)
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).CommShift ℤ]
    [(SyntheticCategory.biShift (Syn:=Syn) (lambdaDegree k)).IsTriangulated]
    (z : (Subobject.underlying.obj
      ((towerSSData (lambdaTower X) ((k:ℤ),n)).Z (↑((q:ℤ)-1).toNat : WithTop ℕ)) : ModuleCat ℤ))
    (a : HomotopyGroup (n-k)
      ((SyntheticCategory.biShift (lambdaDegree k)).obj (XModLambdaN X q)))
    (ha : a ≫ (SyntheticCategory.biShift (lambdaDegree k)).map
      (XModLambdaN.restriction coh X 1 q hq) =
        cycleRep (lambdaTower X) ((k:ℤ),n) ((q:ℤ)-1).toNat z ≫ (lambdaLayerIso X k).hom) :
    towerD (lambdaTower X) q ((k:ℤ),n)
        ((towerSSData (lambdaTower X) ((k:ℤ),n)).pageπ _ z) =
      layerPage (lambdaTower X) (((k:ℤ),n)+((q:ℤ),(q:ℤ)-1)) ((q:ℤ)-1).toNat
        (degreeCast (by dsimp; omega : n-k-1 =
          (((k:ℤ),n)+((q:ℤ),(q:ℤ)-1)).2 - (((k:ℤ),n)+((q:ℤ),(q:ℤ)-1)).1)
          (RawTower.desuspend _ (n-k) (lambdaFiniteQuotientStageBoundary X k q n a))) := by
  rw [towerD_pageπ (lambdaTower X) q (by omega) ((k:ℤ),n) z]
  apply differentialValue_of_lift
  have h := lambda_finite_lift_connecting_at coh X k q hq n
    (cycleRep (lambdaTower X) ((k:ℤ),n) ((q:ℤ)-1).toNat z) a ha
  have hd := congrArg (RawTower.desuspend ((lambdaTower X).stageAt ((k:ℤ)+1)) (n-k)) h
  rw [raw_desuspend_natural] at hd
  exact hd

end
end KIP126.Literature.BocksteinFiniteBoundaryConstruction
