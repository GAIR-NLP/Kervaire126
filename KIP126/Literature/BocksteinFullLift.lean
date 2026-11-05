module
import KIP126.Literature.Lift
/-! Exact composition and normalization of full lambda lifts, retaining the one-lambda error. -/

@[expose] section
namespace KIP126.Literature.Paper38FullLiftComposition
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic KIP126.Kervaire.Route
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C:=C)] {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C:=Syn)] (D : AdamsSyntheticBackground C Syn)

private def composeFullLift {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {k l : ℕ}
    (F : SyntheticFullLift D f k) (G : SyntheticFullLift D g l) :
    SyntheticFullLift D (f≫g) (k+l) where
  map := F.map ≫ (SyntheticCategory.biShift (0,-(k:ℤ))).map G.map ≫
    (lambdaShiftAddIso l k (k+l) (Nat.add_comm l k)).hom.app (D.nu.functor.obj Z)
  factorization := by
    simp only [Category.assoc]
    rw [lambdaPow_add_comparison D.quotients.coherence]
    simp only [lambdaDegree]
    rw [←Category.assoc ((SyntheticCategory.biShift (0,-(k:ℤ))).map G.map),
      ←Functor.map_comp, G.factorization, lambdaPow_naturality,
      ←Category.assoc, F.factorization, D.nu.functor.map_comp]

private def triangleFullLift {T : Triangle C} (L : SyntheticTriangleLift D T) :
    SyntheticFullLift D T.mor₃ 1 where
  map := L.connecting
  factorization := by
    rw [lambdaPow_one D.quotients.coherence]
    exact L.factorization

private def negFullLift {X Y : C} {f : X ⟶ Y} {k : ℕ}
    (F : SyntheticFullLift D f k) : SyntheticFullLift D (-f) k where
  map := -F.map
  factorization := by
    letI := D.nu.additive
    rw [Preadditive.neg_comp, F.factorization, D.nu.functor.map_neg]

private theorem normalizedMap_eq {X Y : C} {f : X ⟶ Y} {k : ℕ}
    (F : SyntheticFullLift D f k) (hk : 1≤k) :
    F.normalizedMap D hk = F.map ≫
      (lambdaShiftAddIso 1 (k-1) k (by omega)).inv.app (D.nu.functor.obj Y) ≫
      lambdaPow (k-1) ((SyntheticCategory.biShift (0,-1)).obj (D.nu.functor.obj Y)) := by
  simp only [SyntheticFullLift.normalizedMap, lambdaShiftAddIso, biShiftAddIso,
    Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app, lambdaDegree]
  simp only [Category.assoc]
  rfl

private theorem normalizedMap_factorization {X Y : C} {f : X ⟶ Y} {k : ℕ}
    (F : SyntheticFullLift D f k) (hk : 1≤k) :
    F.normalizedMap D hk ≫ SyntheticCategory.lam.app (D.nu.functor.obj Y) =
      D.nu.functor.map f := by
  rw [normalizedMap_eq D F hk, Category.assoc, Category.assoc,
    ←lambdaPow_naturality (k-1) (SyntheticCategory.lam.app (D.nu.functor.obj Y)),
    ←lambdaPow_one D.quotients.coherence]
  have hpow := (lambdaPow_add D.quotients.coherence 1 (k-1) k (by omega)
    (D.nu.functor.obj Y)).symm
  simp only [lambdaDegree] at hpow
  exact (congrArg (fun a => F.map ≫ a) hpow).trans F.factorization

/-- The two specified factorizations imply that one lambda kills the
ambiguity. -/
private theorem triangleFullLift_difference_lambda_zero {T : Triangle C}
    (L : SyntheticTriangleLift D T) {k : ℕ} (hk : 1≤k)
    (F : SyntheticFullLift D T.mor₃ k) :
    (L.connecting - F.normalizedMap D hk) ≫
      SyntheticCategory.lam.app (D.nu.functor.obj (T.obj₁⟦(1:ℤ)⟧)) = 0 := by
  rw [Preadditive.sub_comp, L.factorization, normalizedMap_factorization D F hk,
    sub_self]

end
end KIP126.Literature.Paper38FullLiftComposition
