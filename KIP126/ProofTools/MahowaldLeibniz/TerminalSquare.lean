module

import KIP126.ProofTools.MahowaldLeibniz
import all KIP126.ProofTools.MahowaldLeibniz.Bockstein
import all KIP126.ProofTools.GeneralizedMahowald.FiniteComparison

/-! The actual normalized finite Bockstein square. All quotient and
connecting arrows are those of the selected model. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private def firstFiniteDelta (A : SyntheticSpectrum) (N : ℕ) (hN : 0<N) :
    XModLambdaN A 1 ⟶
      ((SyntheticCategory.biShift (0,-(1:ℕ))).obj (XModLambdaN A N))⟦(1:ℤ)⟧ := by
  simpa only [show 1+N-1=N by omega] using
    ((background.quotients.tower A).triangle (show 0<1 by decide)
      (show 1 < 1 + N by omega)).delta

private theorem firstFiniteDelta_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (N : ℕ) (hN : 0<N) :
    XModLambdaN.map f 1 ≫ firstFiniteDelta B N hN =
      firstFiniteDelta A N hN ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(1:ℕ))).map (XModLambdaN.map f N)) := by
  have h := (background.quotients.natural f).delta_naturality
    (show 0<1 by decide) (show 1 < 1 + N by omega)
  have transport (n : ℕ) (hn : n=N)
      (da : XModLambdaN A 1 ⟶
        ((SyntheticCategory.biShift (0,-(1:ℕ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (db : XModLambdaN B 1 ⟶
        ((SyntheticCategory.biShift (0,-(1:ℕ))).obj (XModLambdaN B n))⟦(1:ℤ)⟧)
      (h : XModLambdaN.map f 1 ≫ db = da ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(1:ℕ))).map (XModLambdaN.map f n))) :
      XModLambdaN.map f 1 ≫
        (Eq.mp (congrArg (fun j => XModLambdaN B 1 ⟶
          ((SyntheticCategory.biShift (0,-(1:ℕ))).obj (XModLambdaN B j))⟦(1:ℤ)⟧) hn) db) =
      (Eq.mp (congrArg (fun j => XModLambdaN A 1 ⟶
        ((SyntheticCategory.biShift (0,-(1:ℕ))).obj (XModLambdaN A j))⟦(1:ℤ)⟧) hn) da) ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(1:ℕ))).map (XModLambdaN.map f N)) := by
    subst n
    exact h
  exact transport (1+N-1) (by omega) _ _ h

private def firstFiniteBoundaryRepresentative (A : SyntheticSpectrum)
    (N : ℕ) (hN : 0<N) (m w : ℤ) (a : BiHom m w (XModLambdaN A 1)) :
    BiHom (m-1) (w+(1:ℕ)) (XModLambdaN A N) :=
  biSuspensionHomEquiv m w (1:ℕ) (XModLambdaN A N)
    (a ≫ firstFiniteDelta A N hN)

private theorem firstFiniteBoundaryRepresentative_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (N : ℕ) (hN : 0<N) (m w : ℤ)
    (a : BiHom m w (XModLambdaN A 1)) :
    firstFiniteBoundaryRepresentative B N hN m w (a ≫ XModLambdaN.map f 1) =
      firstFiniteBoundaryRepresentative A N hN m w a ≫ XModLambdaN.map f N := by
  dsimp only [firstFiniteBoundaryRepresentative]
  rw [Category.assoc,firstFiniteDelta_natural,←Category.assoc,
    bi_susp_natural background.quotients.coherence]

private def ordinarySuspendedRepresentative (A : SyntheticSpectrum) (m w : ℤ)
    (a : BiHom (m-1) w A) : BiHom m w (A⟦(1:ℤ)⟧) :=
  homotopyRegrade (by dsimp; omega) (by simp)
    (shiftHomotopyClass (1,0) (m-1,w) a) ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app A

private theorem ordinarySuspendedRepresentative_natural {A B : SyntheticSpectrum}
    (f : A ⟶ B) (m w : ℤ) (a : BiHom (m-1) w A) :
    ordinarySuspendedRepresentative B m w (a ≫ f) =
      ordinarySuspendedRepresentative A m w a ≫
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map f := by
  simp only [ordinarySuspendedRepresentative,shiftHomotopyClass,Functor.map_comp,
    regrade_precomp,Category.assoc]
  rw [←(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.naturality f]

private def normalizedFirstMap (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1) :
    (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (T.Y.obj background.auxiliary) := by
  simpa only [hf,Nat.cast_one] using (background.normalizedMap T.X T.Y T.f).map

private theorem cast_BiHom_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w')
    (h : BiHom m w A = BiHom m' w' A) (a : BiHom m w A) :
    h.mp a = homotopyRegrade hm hw a := by
  subst m'
  subst w'
  rfl

private theorem nativeFirstLabel_eq_regrade
    (X : AdamsObject (coefficients := background.coefficients)) (s t : ℤ) (x : Ambient background X (s,t)) :
    nativeFirstLabel X s t x =
      homotopyRegrade rfl (Int.add_zero t) ((background.firstQuotient X 0 s t).symm x) ≫
        XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1 := by
  dsimp only [nativeFirstLabel,firstLabel]
  congr 1
  exact cast_BiHom_regrade rfl (Int.add_zero t) _ _

private theorem cofiberFirstQuotientBoundary_native_label
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t)) :
    nativeFirstLabel T.Y (s+1) (t+1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) =
    homotopyRegrade (by omega) rfl
      ((background.firstQuotient T.X 1 s t).symm x ≫ XModLambdaN.map (normalizedFirstMap T hf) 1) := by
  rw [nativeFirstLabel_eq_regrade]
  simp only [
    KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary,normalizedFirstMap]
  simp only [LinearEquiv.symm_apply_apply,regrade_precomp,Category.assoc,
    ←background.quotients.functoriality.map_comp,Iso.inv_hom_id_app]
  simp only [←Category.assoc,eqToHom_trans]
  erw [Category.comp_id]

/-- An actual source for the normalized finite square, formed from the
finite Bockstein and the specified ordinary-suspension comparison. -/
private def suspendedFirstFiniteBoundary
    (A : SyntheticSpectrum) (N : ℕ) (hN : 0<N) (m w : ℤ)
    (ex : XModLambdaN (A⟦(1:ℤ)⟧) N ≅ (XModLambdaN A N)⟦(1:ℤ)⟧)
    (a : BiHom m w (XModLambdaN A 1)) :
    BiHom m (w+(1:ℕ)) (XModLambdaN (A⟦(1:ℤ)⟧) N) :=
  ordinarySuspendedRepresentative _ m (w+(1:ℕ))
    (firstFiniteBoundaryRepresentative A N hN m w a) ≫ ex.inv

/-- Boundary naturality on representatives for the normalized map,
using the inclusion-compatible suspension comparisons of finite May. -/
private theorem suspendedFirstFiniteBoundary_normalized_natural
    (X Y : AdamsObject (coefficients := background.coefficients)) (k : ℕ) (hk : k≤1) (N : ℕ) (hN : 0<N)
    (f : (SyntheticCategory.biShift (0,(k:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
      background.nu.functor.obj (Y.obj background.auxiliary))
    (ex : XModLambdaN (((SyntheticCategory.biShift (0,(k:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) N)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((background.nu.functor.obj (Y.obj background.auxiliary))⟦(1:ℤ)⟧) N ≅
      (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) N)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ N ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (hey : XModLambdaN.incl _ N ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ N))
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN ((SyntheticCategory.biShift (0,(k:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) 1)) :
    suspendedFirstFiniteBoundary _ N hN m w ex a ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) N ≫ ey.hom =
      ordinarySuspendedRepresentative _ m (w+(1:ℕ))
        (firstFiniteBoundaryRepresentative _ N hN m w (a ≫ XModLambdaN.map f 1)) := by
  rw [finite_suspension_normalized_map_on_spheres X Y k hk N hN f ex ey hex hey]
  simp only [suspendedFirstFiniteBoundary,Category.assoc,Iso.inv_hom_id_assoc]
  rw [firstFiniteBoundaryRepresentative_natural,ordinarySuspendedRepresentative_natural]

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
