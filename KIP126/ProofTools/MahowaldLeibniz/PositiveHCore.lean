module
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

/-! The actual common finite-quotient core in the positive third-exponent
branch. Both labels and the source cycle use the same May representative;
the annihilation condition acts on actual higher-filtration differences. -/

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

private def PositiveThirdFiniteCoreStatement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (_hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (_hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
 : Prop :=
  ∀ (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s,t)) (u : Ambient background T.X (s+1,t))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa using u))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) z
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (ey : XModLambdaN ((normalizedTriangle background T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₂ (q+1))⟦(1:ℤ)⟧)
    (hey : XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (εN : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+(q+1))))
    (hεN : XModLambdaN.incl _ (c+(q+1)) ≫ εN.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1)))),
    let V := normalizedTriangle background T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((background.quotients.tower V.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel background T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
        finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv) ∧
      IsCycle background T.X (q+1) (s+1,t) u ∧
      ((∀ e : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
        FiltrationAtLeast background.syntheticTower ((s+1)+1)
          (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN e) →
        e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1))=0) →
        ∀ d : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
          Detects (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
            (s+1,t,t-c) (finiteTargetLabel background T.X (c+(q+1)) (s+1) t c u)
            (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN d) →
          d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)) =
            a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) (c+(q+1)))

private theorem positive_third_finite_core
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
 :
    PositiveThirdFiniteCoreStatement T he hT hf hg hh := by
  intro c q hq s t z u v hu hd ey hey εN hεN
  dsimp only
  obtain ⟨a,ha,himage⟩ := positive_h_classical_second_may_at_level
    T he hT hf hg hh c q hq s t z u v hu hd ey hey εN hεN
  have hc := (finite_rho_lift_label_and_cycles T.X (c+(q+1)) (c+(q+1)) c le_rfl
    (by omega) (s+1) t u _ ha _ (by rw [(background.quotients.tower _).rho_id,Category.comp_id])).2
  have hc' : IsCycle background T.X (q+1) (s+1,t) u := by
    refine ⟨by omega, ?_⟩
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left] using hc
  refine ⟨a,ha,himage,hc',?_⟩
  intro hA d hd
  have hdiff := detects_sub_filtration (background.convergence (.quotient (c+(q+1)) (.nu T.X)))
    (s+1,t,t-c) hd ha
  have he : FiltrationAtLeast background.syntheticTower ((s+1)+1)
      (positiveHSourceDesuspend T he hf (c+(q+1)) c s t εN (d-a)) := by
    simpa only [positiveHSourceDesuspend,Preadditive.sub_comp,homotopy_regrade_sub,
      quotient_unshift_sub] using hdiff
  have hz := hA (d-a) he
  simpa only [Preadditive.sub_comp,sub_eq_zero] using hz

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
