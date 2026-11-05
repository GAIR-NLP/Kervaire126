module

import all KIP126.Literature.BocksteinSequenceComparison
import all KIP126.Literature.BocksteinSuccessorComparison

/-! The canonical successor square of the coefficient-tower comparison,
from the sequence isomorphism and successor computation rule.
-/

@[expose] section
namespace KIP126.Literature.BocksteinComparison.Sequence
open KIP126.AdamsSynthetic KIP126.Literature.Paper38Successor
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Core.SpectralSequence
universe u v
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {X Y : C} {T : AbstractAdamsTower unit X} {U : AbstractAdamsTower unit Y}
  (S S' : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ))
  (h0 : S.r₀ = 2) (hd : ∀ r, S.diffDeg r = (r,r-1))
  (h0' : S'.r₀ = 2) (hd' : ∀ r, S'.diffDeg r = (r,r-1))
  (P : TowerSequencePresentation unit T S.ssData (normalizedDifferential S h0 hd))
  (Q : TowerSequencePresentation unit U S'.ssData (normalizedDifferential S' h0' hd'))
  (e : X ≅ Y)

/-- Each vertex is the actual quotient map of the same tower ambient isomorphism. -/
private def presentedCenteredComplexIso (r : ℤ) (p : ℤ × ℤ) :
    (normalizedAdamsSequence S h0 hd).pageShortComplex r (p-(r,r-1)) ≅
      (normalizedAdamsSequence S' h0' hd').pageShortComplex r (p-(r,r-1)) := by
  let f := presentedSequenceMap S S' h0 hd h0' hd' P Q e
  let g := centeredComplexMap f r p
  haveI : IsIso g.τ₁ := by
    change IsIso ((presentedPageIso P Q e (p-(r,r-1))
      (↑(r-2).toNat : WithTop ℕ)).hom ≫ 𝟙 _)
    infer_instance
  haveI : IsIso g.τ₂ := by
    change IsIso ((presentedPageIso P Q e (p-(r,r-1)+(r,r-1))
      (↑(r-2).toNat : WithTop ℕ)).hom ≫ 𝟙 _)
    infer_instance
  haveI : IsIso g.τ₃ := by
    change IsIso ((presentedPageIso P Q e (p-(r,r-1)+(r,r-1)+(r,r-1))
      (↑(r-2).toNat : WithTop ℕ)).hom ≫ 𝟙 _)
    infer_instance
  letI : IsIso g := ShortComplex.isIso_of_isIso g
  exact asIso g

/-- The induced isomorphism on homology, using that same centered-complex map. -/
private def presentedHomologyIso (r : ℤ) (p : ℤ × ℤ) :
    ((normalizedAdamsSequence S h0 hd).pageShortComplex r (p-(r,r-1))).homology ≅
      ((normalizedAdamsSequence S' h0' hd').pageShortComplex r (p-(r,r-1))).homology :=
  ShortComplex.homologyMapIso (presentedCenteredComplexIso S S' h0 hd h0' hd' P Q e r p)


/-- The actual successor square, using the pre-existing canonical pageHomologyIso
on both sides and the homology map induced by the same tower page comparison. -/
private theorem presentedCanonicalSuccessor_comm (r : ℤ) (hr : 2 ≤ r) (p : ℤ × ℤ) :
    (pageHomologyIso (normalizedAdamsSequence S h0 hd) r p hr).hom ≫
      (presentedHomologyIso S S' h0 hd h0' hd' P Q e r p).hom =
    (presentedPageIso P Q e p (↑(r+1-2).toNat : WithTop ℕ)).hom ≫
      (pageHomologyIso (normalizedAdamsSequence S' h0' hd') r p hr).hom := by
  exact canonicalSuccessor_naturality
    (presentedSequenceMap S S' h0 hd h0' hd' P Q e) r p hr

end
end KIP126.Literature.BocksteinComparison.Sequence
end
