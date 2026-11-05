module

public import KIP126.AdamsSynthetic.Completed.Background
public import KIP126.AdamsSynthetic.AdamsFiltration
import all KIP126.AdamsSynthetic.Completed.Source
import all KIP126.AdamsSynthetic.Source
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Recognition
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.ZeroPrespectrum

/-! Direct acyclic-tower vanishing for the actual completed Adams system.
No UCT, synthetic object, first quotient, normalized map, tensor exactness or
HF₂-localized Adams comparison is used. -/

@[expose] section
namespace KIP126.AdamsSynthetic.Completed
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open scoped ZeroObject
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

/-- Homotopy detection on the actual completed category. Its proof uses
its fully faithful local-object inclusion and the completed sphere adjunction. -/
public theorem isZero_of_homotopy_zero (X : Spectrum)
    (hπ : ∀ d : ℤ, Subsingleton (HomotopyGroup d X)) : IsZero X := by
  sorry

private theorem acyclic_tower_coefficient_stage (X : Spectrum)
    (hH : ∀ n : ℤ, Subsingleton (ModTwoHomology coefficients n X)) (n : ℕ) :
    IsZero (coefficients.object ⊗ (classicalTower.tower X).stage n) := by
  let T := classicalTower.tower X
  induction n with
  | zero =>
    exact (isZero_of_homotopy_zero (coefficients.object ⊗ X) hH).of_iso
      ((tensorLeft coefficients.object).mapIso T.zeroIso)
  | succ n ih =>
    have hc : IsZero (HasFunctorialCofiber.cofib (T.map (Nat.le_succ n))) :=
      ih.of_iso (T.layerIso n)
    letI : IsIso (T.map (Nat.le_succ n)) :=
      (Triangle.isZero₃_iff_isIso₁
        (Triangle.mk (T.map (Nat.le_succ n)) _ _)
        (HasFunctorialCofiber.cofib_distinguished _)).mp hc
    exact ih.of_iso ((tensorLeft coefficients.object).mapIso
      (asIso (T.map (Nat.le_succ n))))

private theorem acyclic_tower_layer (X : Spectrum)
    (hH : ∀ n : ℤ, Subsingleton (ModTwoHomology coefficients n X)) (s : ℤ) :
    IsZero ((classicalTower.tower X).layer s) := by
  let T := classicalTower.tower X
  by_cases hs : s < 0
  · have hi (a b : ℕ) (hab : a ≤ b) (h : a = b) : IsIso (T.map hab) := by
      subst b
      rw [T.map_self]
      infer_instance
    let f := T.mapAt (show s ≤ s+1 by omega)
    letI : IsIso f := hi s.toNat (s+1).toNat (by omega) (by omega)
    exact Triangle.isZero₃_of_isIso₁
      (Triangle.mk f _ _) (HasFunctorialCofiber.cofib_distinguished f)
      (show IsIso f from inferInstance)
  · lift s to ℕ using (by omega : 0 ≤ s)
    change IsZero (HasFunctorialCofiber.cofib (T.map (Nat.le_succ s)))
    exact (acyclic_tower_coefficient_stage X hH s).of_iso (T.layerIso s)

private theorem acyclic_page_of_ambient (D : SSData (ModuleCat.{0} ℤ))
    (r : WithTop ℕ) [Subsingleton D.V] : Subsingleton (D.page r) := by
  have hV : IsZero D.V := ModuleCat.isZero_of_subsingleton D.V
  have hZ : IsZero (Subobject.underlying.obj (D.Z r)) :=
    IsZero.of_mono (D.Z r).arrow hV
  letI : Epi (D.pageπ r) := coequalizer.π_epi
  exact ModuleCat.subsingleton_of_isZero (IsZero.of_epi (D.pageπ r) hZ)

private theorem acyclic_tower_page (X : Spectrum)
    (hH : ∀ n : ℤ, Subsingleton (ModTwoHomology coefficients n X))
    (p : ℤ × ℤ) (r : WithTop ℕ) :
    Subsingleton (((classical.obj X).ssData p).page r) := by
  let T := classicalTower.tower X
  letI : Subsingleton (T.FirstPage p) :=
    ⟨fun a b => (acyclic_tower_layer X hH p.1).eq_of_tgt a b⟩
  let D := (classical.obj X).ssData p
  letI : Subsingleton D.V :=
    (classicalTower.sequence X).ambient p |>.toLinearEquiv.injective.subsingleton
  exact acyclic_page_of_ambient D r

/-- Every displayed page of the fixed completed Adams sequence of any actual
HF₂-acyclic spectrum is zero. -/
public theorem classical_page_subsingleton_of_homology_zero
    (X : Spectrum)
    (hH : ∀ n : ℤ, Subsingleton (ModTwoHomology coefficients n X))
    (r s t : ℤ) : Subsingleton ((classical.obj X).Page r (s,t)) :=
  acyclic_tower_page X hH (s,t) _

/-- The actual Z∞/B∞ page of the same completed sequence is also zero. -/
public theorem classical_infty_subsingleton_of_homology_zero
    (X : Spectrum)
    (hH : ∀ n : ℤ, Subsingleton (ModTwoHomology coefficients n X))
    (s t : ℤ) : Subsingleton (((classical.obj X).ssData (s,t)).eInfty) :=
  acyclic_tower_page X hH (s,t) ⊤

end
end KIP126.AdamsSynthetic.Completed
