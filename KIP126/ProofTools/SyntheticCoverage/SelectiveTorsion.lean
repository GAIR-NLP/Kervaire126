module

import all KIP126.ProofTools.SyntheticCoverage.MiddleElimination
import all KIP126.ProofTools.SyntheticCoverage.Permanence
import all KIP126.ProofTools.GeneralizedLeibniz.Reverse

/-! Finite torsion bounds for the middle error in restricted differential
criteria. The torsion exponent of the specified full representative bounds
the boundary space of its visible finite label. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2500000

/-- Multiplication by a positive lambda power retains the specified classical
label at any admissible weight, with the larger true-boundary denominator. -/
private theorem nu_weight_lambda_detects (X : (AdamsObject (coefficients := background.coefficients))) (k : ℕ) (hk : 0<k)
    (s t w : ℤ) (hw : w≤t) (y : Ambient background X (s,t))
    (α : BiHom (t-s) w (background.nu.functor.obj (X.obj background.auxiliary)))
    (ha : Detects (background.convergence (.nu X)) (s,t,w)
      (nuWeightLabel background X s t w hw y) α) :
    Detects (background.convergence (.nu X)) (s,t,w-k)
      (nuWeightLabel background X s t (w-k) (by omega) y) (lambdaMultiply k α) := by
  let A := background.nu.functor.obj (X.obj background.auxiliary)
  have hsource : (s,t,w)=(s,(t-s)+s,w) := by simp
  have hstem := detects_transport hsource _ _ ha
  let L : ((SyntheticObject.shift (0,-(k:ℤ)) (.nu X)).obj background.nu background.auxiliary) ⟶ A := lambdaPow k A
  have hmap := shifted_map_detects (.nu X) (.nu X) (0,-(k:ℤ)) (t-s,w) s L
    (regradeE2 hsource (nuWeightLabel background X s t w hw y)) α hstem
  have hindex : (s,((t-s,w)+(0,-(k:ℤ))).1+s,((t-s,w)+(0,-(k:ℤ))).2) =
      (s,t,w-k) := by ext <;> simp [sub_eq_add_neg]
  have hmap := detects_transport hindex _ _ hmap
  obtain ⟨e,he,b,hb,hgb⟩ := hmap
  obtain ⟨e0,he0,_⟩ := ha
  have heStem := representative_transport hsource _ _ he0
  have heMap := shifted_representative_map (.nu X) (.nu X)
    (0,-(k:ℤ)) (t-s,w) s L _ _ heStem
  have heMap := representative_transport hindex _ _ heMap
  have heq := he.unique heMap
  have heq' : e = KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) w e0 := by
    convert heq using 1
    simp only [KIP126.Literature.Standard.infinityLambda,
      InfinityShiftCoordinates.lambdaMap, show k ≠ 0 by omega, ↓reduceDIte,
      InfinityShiftCoordinates.shift, infinityShift, Iso.trans_hom, ModuleCat.comp_apply,
      eqToIso.hom, KIP126.Literature.Standard.infinityShiftData,
      KIP126.Literature.Standard.infinityShift_comparison]
    exact (infinity_map_regrade L hindex _).symm
  have he0' := (KIP126.Literature.Standard.eInfinity_nu_labels X s t w hw y e0).mp he0
  have hlabel : HasInfinityRepresentative _ 2 (s,t,w-k)
      (nuWeightLabel background X s t (w-k) (by omega) y)
      (KIP126.Literature.Standard.infinityLambda (.nu X) k (s,t) w e0) := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t (w-k) (by omega) y _).mpr
    refine ⟨he0'.1,?_⟩
    rw [KIP126.Literature.Standard.eInfinity_lambda_nu X k (s,t) w hw,he0'.2]
    rfl
  have heFinal : HasInfinityRepresentative _ 2 (s,t,w-k)
      (nuWeightLabel background X s t (w-k) (by omega) y) e := by
    rw [heq']
    exact hlabel
  refine ⟨e,heFinal,b,?_,hgb⟩
  convert hb using 1
  simp only [regrade_precomp,L,shiftHomotopyClass,lambdaMultiply,Category.assoc]
  simp only [A]
  erw [lambdaPow_naturality k α]
  simp only [←Category.assoc,eqToHom_trans]

/-- A true torsion bound on this full lift gives a true early-boundary bound
for its specified finite target label. -/
private theorem finite_torsion_label_boundary
    (X : (AdamsObject (coefficients := background.coefficients))) (N k l : ℕ) (hkN : k<N) (hl : 0<l) (s t : ℤ)
    (y : Ambient background X (s,t))
    (β : BiHom (t-s) (t-k) (background.nu.functor.obj (X.obj background.auxiliary)))
    (hfinite : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X N s t k y) (β≫XModLambdaN.incl _ N))
    (ht : lambdaMultiply l β=0) :
    y ∈ boundaries background X ((k:ℤ)+l+1) (s,t) := by
  rw [←middle_finite_label_as_weight] at hfinite
  have hfull := finite_projection_detects_reflect X N (by omega) s t (t-k)
    (by omega) y β hfinite
  have hd := nu_weight_lambda_detects X l hl s t (t-k) (by omega) y β hfull
  rw [ht] at hd
  have he := detected_zero_infinity (.nu X) (s,t,t-k-l) _ hd
  have hc := (KIP126.Literature.Standard.eInfinity_nu_labels
    X s t (t-k-l) (by omega) y 0).mp he
  have hb := (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hc.1⟩).mp (by
    rw [←hc.2,map_zero])
  convert hb using 1
  congr 1
  omega

/-- The torsion bound is invariant under the invisible
next-filtration difference in middle correction. -/
private theorem finite_torsion_label_boundary_of_next_filtration
    (X : (AdamsObject (coefficients := background.coefficients))) (N k l : ℕ) (hkN : k<N) (hl : 0<l) (s t : ℤ)
    (y : Ambient background X (s,t))
    (b : BiHom (t-s) (t-k) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) N))
    (β : BiHom (t-s) (t-k) (background.nu.functor.obj (X.obj background.auxiliary)))
    (hb : Detects (background.convergence (.quotient N (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X N s t k y) b)
    (hnext : FiltrationAtLeast background.syntheticTower (s+1)
      (β≫XModLambdaN.incl _ N-b))
    (ht : lambdaMultiply l β=0) :
    y ∈ boundaries background X ((k:ℤ)+l+1) (s,t) := by
  exact finite_torsion_label_boundary X N k l hkN hl s t y β
    (detects_of_next_filtration_difference (.quotient N (.nu X)) (s,t,t-k)
      _ _ _ hb hnext) ht

end
end KIP126.ProofTools.Internal.SyntheticCoverage
