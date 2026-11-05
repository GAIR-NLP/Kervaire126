module

import all KIP126.ProofTools.GeneralizedMahowald.Geometry

/-! Fixed-quotient coordinates for the signed finite May statement.

The statement uses one normalized triangle and the selected quotient towers.
Both output equations concern one representative. The final lemma supplies
the restriction equation and a lambda factorization of its second image. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The signed finite May target in fixed quotient coordinates.
The source has arbitrary bidegree and an explicit ordinary suspension.
The length `(A+B)-A` is the short quotient selected by the tower and equals `B`.
The statement quantifies over suspension comparisons satisfying the quotient
inclusion square. -/
private def finiteMayFixedQuotients
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (m w : ℤ) : Prop :=
  let N := normalizedTriangle background T he
  let F := SyntheticCategory.biShift (Syn := SyntheticSpectrum) (0,-(A:ℤ))
  let LZ := (background.quotients.tower N.obj₃).triangle hA (show A < A+B by omega)
  let LY := (background.quotients.tower N.obj₂).triangle hA (show A < A+B by omega)
  ∀ (esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) (A+B) ≅
        (XModLambdaN N.obj₂ (A+B))⟦(1:ℤ)⟧),
    XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) (A+B) ≫ esusp.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ (A+B)) →
    ∀ (a : BiHom m w (XModLambdaN N.obj₃ A))
      (b : BiHom m w ((F.obj (XModLambdaN N.obj₂ ((A+B)-A)))⟦(1:ℤ)⟧)),
      a ≫ LZ.delta = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (F.map (XModLambdaN.map N.mor₂ ((A+B)-A))) →
      ∃ c : BiHom m w (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (A+B)),
        c ≫ (background.quotients.tower (N.obj₁⟦(1:ℤ)⟧)).rho A (A+B) (by omega) =
          a ≫ XModLambdaN.map N.mor₃ A ∧
        c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (A+B) ≫
            esusp.hom =
          -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map LY.lambdaMap)

/-- A common fixed-quotient lift with a lambda preimage of its second image.
Both equations use the same c and maps selected before c. Exactness supplies
the preimage d. -/
private theorem finite_may_first_image_and_second_factor
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (m w : ℤ)
    (a : BiHom m w (XModLambdaN (normalizedTriangle background T he).obj₃ A))
    (b : BiHom m w
      (((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (normalizedTriangle background T he).obj₂ ((A+B)-A)))⟦(1:ℤ)⟧))
    (hab : a ≫ ((background.quotients.tower (normalizedTriangle background T he).obj₃).triangle
        hA (show A < A+B by omega)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(A:ℤ))).map
          (XModLambdaN.map (normalizedTriangle background T he).mor₂ ((A+B)-A)))) :
    let N := normalizedTriangle background T he
    ∃ (c : BiHom m w (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (A+B)))
      (d : BiHom m w ((SyntheticCategory.biShift (0,-(A:ℤ))).obj
        (XModLambdaN (N.obj₂⟦(1:ℤ)⟧) ((A+B)-A)))),
      c ≫ (background.quotients.tower (N.obj₁⟦(1:ℤ)⟧)).rho A (A+B) (by omega) =
        a ≫ XModLambdaN.map N.mor₃ A ∧
      d ≫ ((background.quotients.tower (N.obj₂⟦(1:ℤ)⟧)).triangle
        hA (show A < A+B by omega)).lambdaMap =
        c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (A+B) := by
  let N := normalizedTriangle background T he
  have hgh : N.mor₂ ≫ N.mor₃ = 0 := comp_distTriang_mor_zero₂₃ N hT
  have hhf : N.mor₃ ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁ = 0 :=
    comp_distTriang_mor_zero₃₁ N hT
  obtain ⟨c,hc⟩ := quotient_boundary_lift N.mor₂ N.mor₃ hgh
    A (A+B) hA (by omega) a b hab
  obtain ⟨d,hd⟩ := quotient_lift_image_division N.mor₃
    ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) hhf
    A (A+B) hA (by omega) a c hc
  exact ⟨c,d,hc,hd⟩

end
end KIP126.ProofTools.Internal.Mahowald
