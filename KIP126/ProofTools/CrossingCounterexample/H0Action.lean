module

import all KIP126.ProofTools.CrossingCounterexample.Base
import all KIP126.ProofTools.GeneralizedMahowald.Coherence

/-! Torsion in the first two actual finite λ quotients of the completed sphere. -/

@[expose] section
namespace KIP126.ProofTools.Internal.CrossingCounterexample

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Completed (background)
open KIP126.ProofTools.Internal.Mahowald

noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem shifted_first_sphere_quotient_two (m w : ℤ)
    (a : BiHom m w ((SyntheticCategory.biShift (0, -1)).obj
      (XModLambdaN (background.nu.functor.obj S) 1))) :
    (2 : ℕ) • a = 0 := by
  let e : BiHom m (w + 1) (XModLambdaN (background.nu.functor.obj S) 1) ≃+
      BiHom m w ((SyntheticCategory.biShift (0, -1)).obj
        (XModLambdaN (background.nu.functor.obj S) 1)) := by
    have e := suspInvarianceAddEquiv m (w + 1) 0 (-1)
      (XModLambdaN (background.nu.functor.obj S) 1)
    have hm : m + 0 = m := by omega
    have hw : w + 1 + -1 = w := by omega
    rw [hm, hw] at e
    exact e
  obtain ⟨b, rfl⟩ := e.surjective a
  rw [← map_nsmul, first_sphere_quotient_two, map_zero]

/-- The kernel is the image of the selected λ arrow in the actual quotient triangle. -/
private theorem second_sphere_quotient_rho_kernel (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj S) 2))
    (ha : a ≫ (background.quotients.tower (background.nu.functor.obj S)).rho
      1 2 (by decide) = 0) :
    ∃ b : BiHom m w ((SyntheticCategory.biShift (0, -1)).obj
        (XModLambdaN (background.nu.functor.obj S) 1)),
      b ≫ ((background.quotients.tower (background.nu.functor.obj S)).triangle
        (by decide : 0 < 1) (by decide : 1 < 2)).lambdaMap = a := by
  let T := (background.quotients.tower (background.nu.functor.obj S)).triangle
    (by decide : 0 < 1) (by decide : 1 < 2)
  have hz : a ≫ T.rho = 0 := by
    simpa only [T, (background.quotients.tower _).triangle_rho] using ha
  obtain ⟨b, hb⟩ := (Triangle.mk T.lambdaMap T.rho T.delta).coyoneda_exact₂
    T.distinguished a hz
  exact ⟨b, hb.symm⟩

private theorem second_sphere_quotient_kernel_two (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj S) 2))
    (ha : a ≫ (background.quotients.tower (background.nu.functor.obj S)).rho
      1 2 (by decide) = 0) :
    (2 : ℕ) • a = 0 := by
  obtain ⟨b, hb⟩ := second_sphere_quotient_rho_kernel m w a ha
  rw [← hb, ← Preadditive.nsmul_comp, shifted_first_sphere_quotient_two, zero_comp]

private theorem second_sphere_quotient_four (m w : ℤ)
    (a : BiHom m w (XModLambdaN (background.nu.functor.obj S) 2)) :
    (4 : ℕ) • a = 0 := by
  have hz : ((2 : ℕ) • a) ≫
      (background.quotients.tower (background.nu.functor.obj S)).rho 1 2 (by decide) = 0 := by
    rw [Preadditive.nsmul_comp, first_sphere_quotient_two]
  have h := second_sphere_quotient_kernel_two m w ((2 : ℕ) • a) hz
  rw [smul_smul] at h
  exact h

end
end KIP126.ProofTools.Internal.CrossingCounterexample
