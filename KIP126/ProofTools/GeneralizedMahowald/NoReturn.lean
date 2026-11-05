module
import all KIP126.ProofTools.GeneralizedMahowald.Filtration
import all KIP126.ProofTools.GeneralizedMahowald.Coherence
import all KIP126.ProofTools.ConvergenceOperations
/-! No-return relations for the Mahowald comparison. -/
@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem nu_infinity_zero_above (X : AdamsObject (coefficients := background.coefficients)) (s t w : ℤ) (hw : t < w) :
    IsZero (((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w)).eInfty) := by
  haveI : Subsingleton (KIP126.Literature.nuEInftyModel background X (s,t) w) := by
    simp only [KIP126.Literature.nuEInftyModel, not_le.mpr hw, ite_false]
    infer_instance
  haveI : Subsingleton (((background.family.nu background.nu (X.obj background.auxiliary)).sequence.ssData (s,t,w)).eInfty) :=
    (KIP126.Literature.Standard.eInfinity_nu X (s,t) w).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/- The endpoint shift places the image above the finite quotient window,
including a positive normalized source shift. -/
private theorem nonreturn_at_window_end (X Y : AdamsObject (coefficients := background.coefficients))
    (j : ℕ) (hj : 0 < j) (d : ℤ) (hd : d ≤ -(j:ℤ)) (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift (0,d)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))))
    (z : (SyntheticCategory.biShift (0,d)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
        XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) j) : c ≫ z = 0 := by
  let A : SyntheticObject (coefficients := background.coefficients) := .shift (0,d) (.nu X)
  let B : SyntheticObject (coefficients := background.coefficients) := .quotient j (.nu Y)
  let L : ℤ := w-m-d
  have hzA (k : ℤ) (hk : k < L) :
      IsZero (((background.family.obj (A.obj background.nu background.auxiliary)).sequence.ssData (k,m+k,w)).eInfty) := by
    have hz := nu_infinity_zero_above X k (m+k) (w-d) (by dsimp [L] at hk; omega)
    let e := towerInfinityIso (background.convergence (.nu X)) (background.convergence A)
      ((essShift (0,d)).filtered (.nu X) (m,w-d)) k
    have he := hz.of_iso e.symm
    have hw : w - d + d = w := by omega
    simpa only [e, A, Prod.fst_add, Prod.snd_add, add_zero, hw] using he
  have hc0 := filtration_at_zero background.syntheticTower _ m w c
  have hcL : FiltrationAtLeast background.syntheticTower L c := by
    by_cases hL : L ≤ 0
    · exact background.syntheticTower.filtrationSubmodule_antitone _ (m,w) hL hc0
    · exact (filtration_iff_of_infinity_zero (background.convergence A) 0 L m w
        (by omega) (fun k _ hk => hzA k hk) c).mp hc0
  have hcz : FiltrationAtLeast background.syntheticTower L (c ≫ z) :=
    map_preserves_filtration (background.convergentMap A B z) (m,w) L c hcL
  exact finite_high_filtration_zero Y j hj m w L (by dsimp [L]; omega) (c ≫ z) hcz


theorem negative_shift_nu_to_quotient_zero (X Y : AdamsObject (coefficients := background.coefficients))
    (j : ℕ) (hj : 0 < j) (m w : ℤ)
    (c : BiHom m w ((SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary))))
    (z : (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
        XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) j) : c ≫ z = 0 := by
  exact nonreturn_at_window_end X Y j hj (-(j:ℤ)-1) (by omega) m w c z


theorem quotient_nu_maps_equal_on_spheres
      (X Y : AdamsObject (coefficients := background.coefficients))
      (j : ℕ) (hj : 0 < j)
      (a b : XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) j ⟶
        XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) j)
      (hab : XModLambdaN.incl _ j ≫ a = XModLambdaN.incl _ j ≫ b) :
      ∀ (m w : ℤ) (c : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) j)),
        c ≫ a = c ≫ b := by
    apply quotient_maps_equal_on_spheres_of_no_return j a b hab
    intro m w c z
    let V := background.nu.functor.obj (X.obj background.auxiliary)
    let ε : ((SyntheticCategory.biShift (0,-(j:ℤ))).obj V)⟦(1:ℤ)⟧ ≅
        (SyntheticCategory.biShift (0,-(j:ℤ)-1)).obj
          (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) :=
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (0,-(j:ℤ)) (1,0)).app V ≪≫
        eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
          (show (0,-(j:ℤ))+(1,0)=(1,1)+(0,-(j:ℤ)-1) by ext <;> simp)) ≪≫
        (SyntheticCategory.biShift_comp (1,1) (0,-(j:ℤ)-1)).symm.app V ≪≫
        (SyntheticCategory.biShift (0,-(j:ℤ)-1)).mapIso (background.nu.suspensionIso _).symm
    have h := negative_shift_nu_to_quotient_zero (.shift 1 X) Y j hj m w
      (c ≫ ε.hom) (ε.inv ≫ z)
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h

theorem shift_minus_one_quotient_maps_equal_on_spheres
      (X Y : AdamsObject (coefficients := background.coefficients))
      (d : ℕ)
      (a b : (SyntheticCategory.biShift (0,-1)).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) d) ⟶
        XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) (d+1))
      (hab : (SyntheticCategory.biShift (0,-1)).map (XModLambdaN.incl _ d) ≫ a =
        (SyntheticCategory.biShift (0,-1)).map (XModLambdaN.incl _ d) ≫ b) :
      ∀ (m w : ℤ) (c : BiHom m w ((SyntheticCategory.biShift (0,-1)).obj
          (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) d))), c ≫ a = c ≫ b := by
    letI := background.exactness.shiftCommShift (0,-1)
    letI := background.exactness.shiftExact (0,-1)
    let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-1)
    let V := background.nu.functor.obj (X.obj background.auxiliary)
    let T := XModLambdaN.cofiberTriangle V d
    have hzero : (F.mapTriangle.obj T).mor₂ ≫ (a-b) = 0 := by
      change F.map (XModLambdaN.incl V d) ≫ (a-b) = 0
      rw [Preadditive.comp_sub,hab,sub_self]
    obtain ⟨z,hz⟩ := Triangle.yoneda_exact₃ (F.mapTriangle.obj T)
      (F.map_distinguished T (XModLambdaN.cofiberTriangle_distinguished V d)) (a-b) hzero
    intro m w c
    let ε : (F.obj ((SyntheticCategory.biShift (0,-(d:ℤ))).obj V))⟦(1:ℤ)⟧ ≅
        (SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ)-1)).obj
          (background.nu.functor.obj ((AdamsObject.shift 1 X).obj background.auxiliary)) :=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso ((lambdaShiftAddIso d 1 (d+1) rfl).app V) ≪≫
        (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app _ ≪≫
        (SyntheticCategory.biShift_comp (0,-((d+1:ℕ):ℤ)) (1,0)).app V ≪≫
        eqToIso (congrArg (fun p => (SyntheticCategory.biShift p).obj V)
          (show (0,-((d+1:ℕ):ℤ))+(1,0)=(1,1)+(0,-((d+1:ℕ):ℤ)-1) by ext <;> simp)) ≪≫
        (SyntheticCategory.biShift_comp (1,1) (0,-((d+1:ℕ):ℤ)-1)).symm.app V ≪≫
        (SyntheticCategory.biShift (0,-((d+1:ℕ):ℤ)-1)).mapIso (background.nu.suspensionIso _).symm
    have h := negative_shift_nu_to_quotient_zero (.shift 1 X) Y (d+1) (by omega) m w
      ((c ≫ (F.mapTriangle.obj T).mor₃) ≫ ε.hom) (ε.inv ≫ z)
    have hcz : (c ≫ (F.mapTriangle.obj T).mor₃) ≫ z = 0 := by
      simpa only [Category.assoc,Iso.hom_inv_id_assoc] using h
    apply sub_eq_zero.mp
    rw [←Preadditive.comp_sub,hz,←Category.assoc]
    exact hcz
/-- Chosen cofiber fillings for a normalized source agree on sphere maps.
The exponent-one case uses the endpoint of the finite no-return window. -/
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
end
end KIP126.ProofTools.Internal.Mahowald
