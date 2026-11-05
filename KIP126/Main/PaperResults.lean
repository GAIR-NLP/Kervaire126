module

public import KIP126.Main.Conditions
import KIP126.Main.H6SquarePermanent
import all KIP126.Main.SectionSeven.Predicates
import all KIP126.Main.SectionSeven.AlphaOne
import all KIP126.Main.SectionSeven.NormalizedNu
import all KIP126.Main.Internal.NuNinth.Assembly

/-! Statements from Section 7 of AimPaper, with fixed quotient maps and nonzero
associated grades. Lemma 7.16 and Corollary 7.18 follow by contradiction
from the incompatibility of their two hypotheses. -/

section
namespace KIP126.Main.Paper
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
open KIP126.Literature.Standard (eta syntheticH0)
noncomputable section

/-- Nonzero detection of the specified sphere class in its actual finite
lambda quotient, using the page map of the quotient projection. -/
@[expose] public def FiniteDetected (n : ℕ) (_hn : 0 < n) (s t : ℤ) (k : ℕ)
    (x : KIP126.AdamsSynthetic.Completed.sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) n)) : Prop :=
  DetectsNonzero (background.convergence (.quotient n .sphere)) (s,t,t-k)
    ((KIP126.AdamsSynthetic.Completed.family.quotientProjection
      KIP126.AdamsSynthetic.Completed.syntheticSphere n).pageMap 2 (s,t,t-k)
        (KIP126.AdamsSynthetic.Completed.comparison.sphereE2 s t k x)) a

/-- Nonzero detection in the fixed untruncated synthetic sphere. -/
@[expose] public def SphereDetected (s t : ℤ) (k : ℕ)
    (x : KIP126.AdamsSynthetic.Completed.sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (S_0_0 : SyntheticSpectrum)) : Prop :=
  DetectsNonzero (background.convergence .sphere) (s,t,t-k)
    (KIP126.AdamsSynthetic.Completed.comparison.sphereE2 s t k x) a




/-- AimPaper Lemma 7.20 (`lem:nuext125`). The normalized Hopf element
acts on an existential representative of lambda^4 X by lambda times an
existential representative of lambda^5 Y in the same actual Q9. -/
public theorem exists_nu_extension_in_ninth_quotient :
    ∃ (x : BiHom 122 126 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
      (y : BiHom 125 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
      FiniteDetected 9 (by decide) 8 130 4 KIP126.Computation.Standard.X x ∧
      FiniteDetected 9 (by decide) 11 136 5 KIP126.Computation.Standard.Y y ∧
      sphereAction (KIP126.Literature.normalizedNu background
        KIP126.Literature.Standard.nuCofiber_nu_exponent) x = lambdaMultiply 1 y := by
  exact KIP126.Main.Internal.NuNinth.nu_extension_in_ninth_quotient

/-- AimPaper Lemma 7.16 (`lem:toda2ext`). One Q11 alpha-one witness supplies
its Q9 image and the properties of Lemma 7.14. Every member of the same
nonempty right-module Toda bracket (eta, h0, lambda^3 alpha-one) is nonzero
and detected by lambda^4 Y. The alpha-one witness remains fixed.
The hypotheses are incompatible. -/
public theorem exists_alpha_one_with_toda_bracket_detected_by_Y
    (hc3 : Stem126D6Vanishes) (hc5 : EtaExtensionDetection) :
    ∃ a11 : BiHom 123 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 11),
      let a9 := a11 ≫ (background.quotients.tower S_0_0).rho 9 11 (by decide)
      let bracket := fun z : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) =>
        KIP126.StableHomotopy.Toda.Relation
          ((KIP126.Literature.Route.tripleTodaSource 1 2 0 1 123 129).inv ≫ z)
          ((SyntheticCategory.biShift (123,130)).map eta)
          ((SyntheticCategory.biShift_comp (0,1) (123,129)).inv.app S_0_0 ≫
            (SyntheticCategory.biShift (123,129)).map syntheticH0)
          (lambdaMultiply 3 a9)
      (FiniteDetected 11 (by decide) 9 132 0 KIP126.Computation.Standard.V a11 ∧
        FiniteDetected 9 (by decide) 9 132 0 KIP126.Computation.Standard.V a9 ∧
        (∀ u : BiHom 124 134 (S_0_0 : SyntheticSpectrum),
          SphereDetected 10 134 0 KIP126.Computation.Standard.U u →
          ∃ (a2 : BiHom 124 137 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
            (a3 : BiHom 125 140 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)),
            lambdaMultiply 3 (sphereAction eta a9) =
              (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
                lambdaMultiply 3 (quotientClass 9 u)) +
              (show BiHom 124 131 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) from
                lambdaMultiply 6 a2) ∧
            sphereAction eta a2 = lambdaMultiply 1 a3) ∧
        lambdaMultiply 3 (sphereAction syntheticH0 a9) = 0) ∧
      (∃ z, bracket z) ∧
      ∀ z, bracket z →
        FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y z ∧ z ≠ 0 := by
  exact False.elim (KIP126.Main.eta_extension_excluded_of_d6_vanishes hc3 hc5)

/-- AimPaper Corollary 7.18 (`cor:2ext125`). For every Y-detected representative
there is a T-detected representative which may depend on it. Both lie in
the same Q9 and satisfy the stated unmultiplied equation.
The hypotheses are incompatible. -/
public theorem exists_syntheticH0_extension_of_Y_detection
    (hc3 : Stem126D6Vanishes) (hc5 : EtaExtensionDetection) :
    ∀ y : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiniteDetected 9 (by decide) 11 136 4 KIP126.Computation.Standard.Y y →
      ∃ t : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
        FiniteDetected 9 (by decide) 14 139 0 KIP126.Computation.Standard.T t ∧
        sphereAction syntheticH0 y = lambdaMultiply 6 t ∧ lambdaMultiply 6 t ≠ 0 := by
  exact False.elim (KIP126.Main.eta_extension_excluded_of_d6_vanishes hc3 hc5)

end
end KIP126.Main.Paper
