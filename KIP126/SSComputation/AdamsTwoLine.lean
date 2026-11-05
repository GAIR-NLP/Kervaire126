module
public import KIP126.AdamsComputation
import all KIP126.SSComputation.Internal.StringCertificate
meta import Lean.Elab.Tactic
import Batteries.Data.String.Lemmas
import KIP126.AdamsComputation.Table.Values
import KIP126.AdamsComputation.Table.Dimensions
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.CharP.Two
/-! The d₂-stage analysis of products hᵢhⱼ for 0 ≤ i,j ≤ 7. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
@[expose] section
namespace KIP126.SSComputation
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Computation KIP126.Computation.Standard KIP126.Computation.Table
open KIP126.AdamsSynthetic.Completed (background)

public def TwoLineD2Candidate (i j : ℕ) : Prop :=
  (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨
  (i = 1 ∧ 3 ≤ j) ∨ i = j ∨
  (i = 2 ∧ j = 5) ∨ (i = 3 ∧ j = 5) ∨ (i = 3 ∧ j = 6) ∨
  (i = 0 ∧ j = 4)

/- Sphere Leibniz law transported through the mapping-spectrum comparison. -/
private theorem pairing_d2
    {E : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)}
    (P : SSPairing E E E) (p q u v r : ℤ × ℤ)
    (x : E.Page 2 p) (y : E.Page 2 q)
    (dx : E.Page 2 u) (dy : E.Page 2 v)
    (hx : HasDifferential E 2 p u x dx)
    (hy : HasDifferential E 2 q v y dy)
    (hur : u + q = r) (hvr : p + v = r) :
    HasDifferential E 2 (p+q) r (P.pair 2 p q x y)
      ((transportPage E 2 hur) (P.pair 2 u q dx y) +
        (if P.parity p = 1 then (-1 : ℤ) else 1) •
          (transportPage E 2 hvr) (P.pair 2 p v x dy)) := by
  obtain ⟨hdu,hdx⟩ := hx.eq_on_page_two
  obtain ⟨hdv,hdy⟩ := hy.eq_on_page_two
  subst u
  subst v
  subst r
  simp (config := { congrConsts := false }) only [eqToHom_refl, Category.comp_id] at hdx hdy
  refine ⟨by ac_rfl, _, _, RepresentsOnPage.self_two _, RepresentsOnPage.self_two _, ?_⟩
  have H := P.leibniz 2 p q x y
  rw [hdx,hdy] at H
  change (E.d 2 (p+q) ≫ eqToHom (congrArg (E.Page 2) (show (p+q)+E.diffDeg 2=(p+E.diffDeg 2)+q by ac_rfl))) (P.pair 2 p q x y) = _
  rw [ModuleCat.comp_apply,H,map_add,map_zsmul]
  delta transportPage
  simp (config := { congrConsts := false }) only [←ModuleCat.comp_apply,eqToHom_trans,eqToHom_refl,ModuleCat.id_apply]

private theorem pageMap_transport
    {E F : KIP126.Core.SpectralSequence (ModuleCat.{0} ℤ) (ℤ × ℤ)}
    (f : E ⟶ F) (r : ℤ) {p q : ℤ × ℤ} (h : p=q) (x : E.Page r p) :
    f.pageMap r q (transportPage E r h x) =
      transportPage F r h (f.pageMap r p x) := by
  subst q
  rfl

private theorem sphere_product_d2
    (p q u v r : ℤ × ℤ)
    (x : background.classical.sphere.Page 2 p) (y : background.classical.sphere.Page 2 q)
    (dx : background.classical.sphere.Page 2 u) (dy : background.classical.sphere.Page 2 v)
    (hx : HasDifferential background.classical.sphere 2 p u x dx)
    (hy : HasDifferential background.classical.sphere 2 q v y dy)
    (hur : u + q = r) (hvr : p + v = r)
    (htwo : ∀ z : background.classical.sphere.Page 2 r, -z=z) :
    HasDifferential background.classical.sphere 2 (p+q) r
      (background.sphereAlgebra.product p q x y)
      ((transportPage background.classical.sphere 2 hur)
        (background.sphereAlgebra.product u q dx y) +
       (transportPage background.classical.sphere 2 hvr)
        (background.sphereAlgebra.product p v x dy)) := by
  let S : KIP126.AdamsSynthetic.Completed.FiniteSpectrum :=
    ⟨KIP126.StableHomotopy.SphereSpectrum, KIP126.AdamsSynthetic.IsFiniteSpectrum.sphere⟩
  let I := KIP126.AdamsSynthetic.sphereMappingAdamsIso
    KIP126.AdamsSynthetic.Completed.closedBackground background.classical
  let P := (KIP126.AdamsSynthetic.Completed.mapping_pairing S S S).ssPairing
  have hinv (r : ℤ) (p : ℤ × ℤ) (a : background.classical.sphere.Page r p) :
      I.hom.pageMap r p (I.inv.pageMap r p a)=a := by
    change (I.inv.pageMap r p ≫ I.hom.pageMap r p) a=a
    rw [←SpectralSequenceMorphism.pageMap_comp,I.inv_hom_id,SpectralSequenceMorphism.pageMap_id]
    rfl
  have hp (p q : ℤ × ℤ) (a) (b) :
      I.hom.pageMap 2 (p+q) (P.pair 2 p q a b) =
        background.sphereAlgebra.product p q (I.hom.pageMap 2 p a) (I.hom.pageMap 2 q b) :=
    KIP126.AdamsSynthetic.Completed.mapping_sphere_product p q a b
  have h := I.hom.hasDifferential (pairing_d2 P p q u v r
    (I.inv.pageMap 2 p x) (I.inv.pageMap 2 q y)
    (I.inv.pageMap 2 u dx) (I.inv.pageMap 2 v dy)
    (I.inv.hasDifferential hx) (I.inv.hasDifferential hy) hur hvr)
  simp (config := { congrConsts := false }) only [map_add,map_zsmul] at h
  have hleft := pageMap_transport I.hom 2 hur
    (P.pair 2 u q (I.inv.pageMap 2 u dx) (I.inv.pageMap 2 q y))
  have hright := pageMap_transport I.hom 2 hvr
    (P.pair 2 p v (I.inv.pageMap 2 p x) (I.inv.pageMap 2 v dy))
  erw [hleft,hright] at h
  simp (config := { congrConsts := false }) only [hp,hinv] at h
  by_cases hparity : P.parity p = 1
  · simpa (config := { congrConsts := false }) only [if_pos hparity, neg_one_zsmul, htwo] using h
  · simpa (config := { congrConsts := false }) only [if_neg hparity, one_zsmul] using h

private theorem sphere_neg_eq_self (s t : ℕ) (ht : t≤261)
    (z : background.classical.sphere.Page 2 ((s:ℤ),(t:ℤ))) : -z=z := by
  apply (KIP126.Computation.Standard.coordinates s t ht).injective
  rw [map_neg]
  apply Finsupp.ext
  intro i
  exact (by decide : ∀ a : ZMod 2, -a=a) _


/- The nine nonzero targets are the specified monomials of the fixed E₂ archive. -/
private theorem source_four_nonzero (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (archive.basisMonomial s t i).value sourceData sourceGenerator ≠ 0 := by
  intro hz
  have hb := sourceBasis_values s t ht i
  rw [hz] at hb
  have hs : (Finsupp.single i (1 : ZMod 2)) = 0 :=
    (sourceCoordinates s t ht).symm.injective (hb.trans (map_zero _).symm)
  have h := congrArg (fun f : Fin (archive.basisCount s t) →₀ ZMod 2 => f i) hs
  exact one_ne_zero (by simpa (config := { congrConsts := false }) only [Finsupp.single_eq_same, Finsupp.zero_apply] using h)

private theorem fourLineH0H0H4H4_source_ne_zero :
    sourceData.product 1 1 3 33 (sourceData.atom .h0)
      (sourceData.product 1 1 2 32 (sourceData.atom .h0)
        (sourceData.product 1 16 1 16 (sourceData.atom .h4) (sourceData.atom .h4))) ≠ 0 := by
  exact source_four_nonzero 4 34 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H0H4H4_ne_zero :
    product (r := (4,34)) (background.standardClasses.standardHi 0)
      (product (r := (3,33)) (background.standardClasses.standardHi 0)
        (product (r := (2,32)) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 4))) ≠ 0 := by
  have h := fourLineH0H0H4H4_source_ne_zero
  have hc : comparison 4 34 (by decide)
    (sourceData.product 1 1 3 33 (sourceData.atom .h0)
      (sourceData.product 1 1 2 32 (sourceData.atom .h0)
        (sourceData.product 1 16 1 16 (sourceData.atom .h4) (sourceData.atom .h4)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 34 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 33, comparison_product 1 1 2 32,
    comparison_product 1 16 1 16, comparison_h0, comparison_h4] at hc
  exact hc

private theorem fourLineH0H0H5H5_source_ne_zero :
    sourceData.product 1 1 3 65 (sourceData.atom .h0)
      (sourceData.product 1 1 2 64 (sourceData.atom .h0)
        (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5))) ≠ 0 := by
  exact source_four_nonzero 4 66 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H0H5H5_ne_zero :
    product (r := (4,66)) (background.standardClasses.standardHi 0)
      (product (r := (3,65)) (background.standardClasses.standardHi 0)
        (product (r := (2,64)) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 5))) ≠ 0 := by
  have h := fourLineH0H0H5H5_source_ne_zero
  have hc : comparison 4 66 (by decide)
    (sourceData.product 1 1 3 65 (sourceData.atom .h0)
      (sourceData.product 1 1 2 64 (sourceData.atom .h0)
        (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 66 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 65, comparison_product 1 1 2 64,
    comparison_product 1 32 1 32, comparison_h0, comparison_h5] at hc
  exact hc

private theorem fourLineH0H0H6H6_source_ne_zero :
    sourceData.product 1 1 3 129 (sourceData.atom .h0)
      (sourceData.product 1 1 2 128 (sourceData.atom .h0)
        (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6))) ≠ 0 := by
  exact source_four_nonzero 4 130 (by decide) ⟨1, by decide⟩

private theorem fourLineH0H0H6H6_ne_zero :
    product (r := (4,130)) (background.standardClasses.standardHi 0)
      (product (r := (3,129)) (background.standardClasses.standardHi 0)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) ≠ 0 := by
  have h := fourLineH0H0H6H6_source_ne_zero
  have hc : comparison 4 130 (by decide)
    (sourceData.product 1 1 3 129 (sourceData.atom .h0)
      (sourceData.product 1 1 2 128 (sourceData.atom .h0)
        (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 130 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 129, comparison_product 1 1 2 128,
    comparison_product 1 64 1 64, comparison_h0, comparison_h6] at hc
  exact hc

private theorem fourLineH0H2H5H5_source_ne_zero :
    sourceData.product 1 1 3 68 (sourceData.atom .h0)
      (sourceData.product 1 4 2 64 (sourceData.atom .h2)
        (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5))) ≠ 0 := by
  exact source_four_nonzero 4 69 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H2H5H5_ne_zero :
    product (r := (4,69)) (background.standardClasses.standardHi 0)
      (product (r := (3,68)) (background.standardClasses.standardHi 2)
        (product (r := (2,64)) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 5))) ≠ 0 := by
  have h := fourLineH0H2H5H5_source_ne_zero
  have hc : comparison 4 69 (by decide)
    (sourceData.product 1 1 3 68 (sourceData.atom .h0)
      (sourceData.product 1 4 2 64 (sourceData.atom .h2)
        (sourceData.product 1 32 1 32 (sourceData.atom .h5) (sourceData.atom .h5)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 69 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 68, comparison_product 1 4 2 64,
    comparison_product 1 32 1 32, comparison_h0, comparison_h2, comparison_h5] at hc
  exact hc

private theorem fourLineH0H2H6H6_source_ne_zero :
    sourceData.product 1 1 3 132 (sourceData.atom .h0)
      (sourceData.product 1 4 2 128 (sourceData.atom .h2)
        (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6))) ≠ 0 := by
  exact source_four_nonzero 4 133 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H2H6H6_ne_zero :
    product (r := (4,133)) (background.standardClasses.standardHi 0)
      (product (r := (3,132)) (background.standardClasses.standardHi 2)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) ≠ 0 := by
  have h := fourLineH0H2H6H6_source_ne_zero
  have hc : comparison 4 133 (by decide)
    (sourceData.product 1 1 3 132 (sourceData.atom .h0)
      (sourceData.product 1 4 2 128 (sourceData.atom .h2)
        (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 133 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 132, comparison_product 1 4 2 128,
    comparison_product 1 64 1 64, comparison_h0, comparison_h2, comparison_h6] at hc
  exact hc

private theorem fourLineH0H3H6H6_source_ne_zero :
    sourceData.product 1 1 3 136 (sourceData.atom .h0)
      (sourceData.product 1 8 2 128 (sourceData.atom .h3)
        (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6))) ≠ 0 := by
  exact source_four_nonzero 4 137 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H3H6H6_ne_zero :
    product (r := (4,137)) (background.standardClasses.standardHi 0)
      (product (r := (3,136)) (background.standardClasses.standardHi 3)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) ≠ 0 := by
  have h := fourLineH0H3H6H6_source_ne_zero
  have hc : comparison 4 137 (by decide)
    (sourceData.product 1 1 3 136 (sourceData.atom .h0)
      (sourceData.product 1 8 2 128 (sourceData.atom .h3)
        (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 137 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 136, comparison_product 1 8 2 128,
    comparison_product 1 64 1 64, comparison_h0, comparison_h3, comparison_h6] at hc
  exact hc

private theorem fourLineH0H3H3H6_source_ne_zero :
    sourceData.product 1 1 3 80 (sourceData.atom .h0)
      (sourceData.product 1 8 2 72 (sourceData.atom .h3)
        (sourceData.product 1 8 1 64 (sourceData.atom .h3) (sourceData.atom .h6))) ≠ 0 := by
  exact source_four_nonzero 4 81 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H3H3H6_ne_zero :
    product (r := (4,81)) (background.standardClasses.standardHi 0)
      (product (r := (3,80)) (background.standardClasses.standardHi 3)
        (product (r := (2,72)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 6))) ≠ 0 := by
  have h := fourLineH0H3H3H6_source_ne_zero
  have hc : comparison 4 81 (by decide)
    (sourceData.product 1 1 3 80 (sourceData.atom .h0)
      (sourceData.product 1 8 2 72 (sourceData.atom .h3)
        (sourceData.product 1 8 1 64 (sourceData.atom .h3) (sourceData.atom .h6)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 81 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 80, comparison_product 1 8 2 72,
    comparison_product 1 8 1 64, comparison_h0, comparison_h3, comparison_h6] at hc
  exact hc

private theorem fourLineH0H3H3H7_source_ne_zero :
    sourceData.product 1 1 3 144 (sourceData.atom .h0)
      (sourceData.product 1 8 2 136 (sourceData.atom .h3)
        (sourceData.product 1 8 1 128 (sourceData.atom .h3) (sourceData.atom .h7))) ≠ 0 := by
  exact source_four_nonzero 4 145 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H3H3H7_ne_zero :
    product (r := (4,145)) (background.standardClasses.standardHi 0)
      (product (r := (3,144)) (background.standardClasses.standardHi 3)
        (product (r := (2,136)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 7))) ≠ 0 := by
  have h := fourLineH0H3H3H7_source_ne_zero
  have hc : comparison 4 145 (by decide)
    (sourceData.product 1 1 3 144 (sourceData.atom .h0)
      (sourceData.product 1 8 2 136 (sourceData.atom .h3)
        (sourceData.product 1 8 1 128 (sourceData.atom .h3) (sourceData.atom .h7)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 145 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 144, comparison_product 1 8 2 136,
    comparison_product 1 8 1 128, comparison_h0, comparison_h3, comparison_h7] at hc
  exact hc

private theorem fourLineH0H4H4H7_source_ne_zero :
    sourceData.product 1 1 3 160 (sourceData.atom .h0)
      (sourceData.product 1 16 2 144 (sourceData.atom .h4)
        (sourceData.product 1 16 1 128 (sourceData.atom .h4) (sourceData.atom .h7))) ≠ 0 := by
  exact source_four_nonzero 4 161 (by decide) ⟨0, by decide⟩

private theorem fourLineH0H4H4H7_ne_zero :
    product (r := (4,161)) (background.standardClasses.standardHi 0)
      (product (r := (3,160)) (background.standardClasses.standardHi 4)
        (product (r := (2,144)) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 7))) ≠ 0 := by
  have h := fourLineH0H4H4H7_source_ne_zero
  have hc : comparison 4 161 (by decide)
    (sourceData.product 1 1 3 160 (sourceData.atom .h0)
      (sourceData.product 1 16 2 144 (sourceData.atom .h4)
        (sourceData.product 1 16 1 128 (sourceData.atom .h4) (sourceData.atom .h7)))) ≠ 0 := by
    exact fun hz => h ((comparison 4 161 (by decide)).injective (hz.trans (map_zero _).symm))
  rw [comparison_product 1 1 3 160, comparison_product 1 16 2 144,
    comparison_product 1 16 1 128, comparison_h0, comparison_h4, comparison_h7] at hc
  exact hc


private theorem finite_page_neg (s t : ℕ) (ht : t ≤ 261)
    (z : background.classical.sphere.Page 2 (s,t)) : -z=z := by
  let e := coordinates s t ht
  apply e.injective
  rw [map_neg]
  ext i
  simp (config := { congrConsts := false }) only [Finsupp.neg_apply]
  exact CharTwo.neg_eq _

private theorem zero_dimension (s t : ℕ) (ht : t ≤ 261)
    (hd : basisDimension s t=0) (x : background.classical.sphere.Page 2 (s,t)) : x=0 := by
  let e := coordinates s t ht
  have hn : archive.basisCount s t=0 := (archive_dimension s t ht).trans hd
  haveI : Subsingleton (Fin (archive.basisCount s t) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  exact e.injective (Subsingleton.elim _ _)

private theorem adjacent_product_zero (i : ℕ) (hi : i ≤ 6) :
    KIP126.Literature.Standard.hiProduct i (i+1) = 0 := by
  interval_cases i <;> exact zero_dimension _ _ (by decide) (by decide) _

private theorem low_hi_d2 (i : ℕ) (hi : i=0 ∨ i=2 ∨ i=3) :
    HasDifferential background.classical.sphere 2 (hiDegree i) (hiDegree i + (2,1))
      (background.standardClasses.standardHi i) 0 := by
  have hdeg : hiDegree i + background.classical.sphere.diffDeg 2 = hiDegree i + (2,1) := by
    rw [background.classical.differentialDegree]
    rfl
  haveI : Subsingleton (background.classical.sphere.Page 2 (hiDegree i + (2,1))) := by
    rcases hi with rfl | rfl | rfl <;> exact ⟨fun x y => (zero_dimension _ _ (by decide) (by decide) x).trans
      (zero_dimension _ _ (by decide) (by decide) y).symm⟩
  exact hasDifferential_two_of_subsingleton_target hdeg _

private theorem reached_d2_target_zero {p q : ℤ×ℤ}
    {x : background.classical.sphere.Page 2 p} {y : background.classical.sphere.Page 2 q}
    (hr : ReachesPage background.classical.sphere 3 p x)
    (hd : HasDifferential background.classical.sphere 2 p q x y) : y=0 := by
  obtain ⟨hdeg,h⟩ := hd.eq_on_page_two
  have hz := (PageThree.reachesPage_iff_d2_eq_zero
    (by rw [background.classical.firstPage]) p x).mp hr
  simpa (config := { congrConsts := false }) only [ModuleCat.comp_apply,hz,map_zero] using h.symm

private theorem h0h5_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 0 + hiDegree 5)
      (KIP126.Literature.Standard.hiProduct 0 5) := by
  intro hr
  have hd := sphere_product_d2 (1,1) (1,32) (3,2) (3,33) (4,34)
    (background.standardClasses.standardHi 0) (background.standardClasses.standardHi 5)
    0 (KIP126.Literature.oneLineTarget background 5)
    (low_hi_d2 0 (by decide))
    (KIP126.Literature.Standard.adamsOneLine_d2 5 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 34 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H0H4H4_ne_zero
  simp (config := { congrConsts := false }) only [LinearMap.zero_apply,map_zero,zero_add] at hz
  change product (r := (4,34)) (background.standardClasses.standardHi 0)
    (product (r := (3,33)) (background.standardClasses.standardHi 0)
      (product (r := (2,32)) (background.standardClasses.standardHi 4)
        (background.standardClasses.standardHi 4))) = 0 at hz
  exact hz

private theorem h0h6_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 0 + hiDegree 6)
      (KIP126.Literature.Standard.hiProduct 0 6) := by
  intro hr
  have hd := sphere_product_d2 (1,1) (1,64) (3,2) (3,65) (4,66)
    (background.standardClasses.standardHi 0) (background.standardClasses.standardHi 6)
    0 (KIP126.Literature.oneLineTarget background 6)
    (low_hi_d2 0 (by decide))
    (KIP126.Literature.Standard.adamsOneLine_d2 6 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 66 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H0H5H5_ne_zero
  simp (config := { congrConsts := false }) only [LinearMap.zero_apply,map_zero,zero_add] at hz
  change product (r := (4,66)) (background.standardClasses.standardHi 0)
    (product (r := (3,65)) (background.standardClasses.standardHi 0)
      (product (r := (2,64)) (background.standardClasses.standardHi 5)
        (background.standardClasses.standardHi 5))) = 0 at hz
  exact hz

private theorem h0h7_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 0 + hiDegree 7)
      (KIP126.Literature.Standard.hiProduct 0 7) := by
  intro hr
  have hd := sphere_product_d2 (1,1) (1,128) (3,2) (3,129) (4,130)
    (background.standardClasses.standardHi 0) (background.standardClasses.standardHi 7)
    0 (KIP126.Literature.oneLineTarget background 7)
    (low_hi_d2 0 (by decide))
    (KIP126.Literature.Standard.adamsOneLine_d2 7 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 130 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H0H6H6_ne_zero
  simp (config := { congrConsts := false }) only [LinearMap.zero_apply,map_zero,zero_add] at hz
  change product (r := (4,130)) (background.standardClasses.standardHi 0)
    (product (r := (3,129)) (background.standardClasses.standardHi 0)
      (product (r := (2,128)) (background.standardClasses.standardHi 6)
        (background.standardClasses.standardHi 6))) = 0 at hz
  exact hz


private theorem reorderH2H0H5H5 :
    product (r := (4,69)) (background.standardClasses.standardHi 2)
      (product (r := (3,65)) (background.standardClasses.standardHi 0)
        (product (r := (2,64)) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 5))) =
    product (r := (4,69)) (background.standardClasses.standardHi 0)
      (product (r := (3,68)) (background.standardClasses.standardHi 2)
        (product (r := (2,64)) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 5))) := by
  let z := product (r := (2,64)) (background.standardClasses.standardHi 5)
    (background.standardClasses.standardHi 5)
  calc
    _ = product (r := (4,69))
          (product (r := (2,5)) (background.standardClasses.standardHi 2)
            (background.standardClasses.standardHi 0)) z :=
      eq_of_heq (background.sphereAlgebra.assoc (1,4) (1,1) (2,64) _ _ z).symm
    _ = product (r := (4,69))
          (product (r := (2,5)) (background.standardClasses.standardHi 0)
            (background.standardClasses.standardHi 2)) z := by
      rw [Table.product_comm 1 4 1 1 (by decide)]
    _ = _ := eq_of_heq (background.sphereAlgebra.assoc (1,1) (1,4) (2,64) _ _ z)

private theorem reorderH2H0H6H6 :
    product (r := (4,133)) (background.standardClasses.standardHi 2)
      (product (r := (3,129)) (background.standardClasses.standardHi 0)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) =
    product (r := (4,133)) (background.standardClasses.standardHi 0)
      (product (r := (3,132)) (background.standardClasses.standardHi 2)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) := by
  let z := product (r := (2,128)) (background.standardClasses.standardHi 6)
    (background.standardClasses.standardHi 6)
  calc
    _ = product (r := (4,133))
          (product (r := (2,5)) (background.standardClasses.standardHi 2)
            (background.standardClasses.standardHi 0)) z :=
      eq_of_heq (background.sphereAlgebra.assoc (1,4) (1,1) (2,128) _ _ z).symm
    _ = product (r := (4,133))
          (product (r := (2,5)) (background.standardClasses.standardHi 0)
            (background.standardClasses.standardHi 2)) z := by
      rw [Table.product_comm 1 4 1 1 (by decide)]
    _ = _ := eq_of_heq (background.sphereAlgebra.assoc (1,1) (1,4) (2,128) _ _ z)

private theorem reorderH3H0H6H6 :
    product (r := (4,137)) (background.standardClasses.standardHi 3)
      (product (r := (3,129)) (background.standardClasses.standardHi 0)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) =
    product (r := (4,137)) (background.standardClasses.standardHi 0)
      (product (r := (3,136)) (background.standardClasses.standardHi 3)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) := by
  let z := product (r := (2,128)) (background.standardClasses.standardHi 6)
    (background.standardClasses.standardHi 6)
  calc
    _ = product (r := (4,137))
          (product (r := (2,9)) (background.standardClasses.standardHi 3)
            (background.standardClasses.standardHi 0)) z :=
      eq_of_heq (background.sphereAlgebra.assoc (1,8) (1,1) (2,128) _ _ z).symm
    _ = product (r := (4,137))
          (product (r := (2,9)) (background.standardClasses.standardHi 0)
            (background.standardClasses.standardHi 3)) z := by
      rw [Table.product_comm 1 8 1 1 (by decide)]
    _ = _ := eq_of_heq (background.sphereAlgebra.assoc (1,1) (1,8) (2,128) _ _ z)

private theorem reorderH0H3H3H6 :
    product (r := (4,81))
      (product (r := (3,17)) (background.standardClasses.standardHi 0)
        (product (r := (2,16)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 3))) (background.standardClasses.standardHi 6) =
    product (r := (4,81)) (background.standardClasses.standardHi 0)
      (product (r := (3,80)) (background.standardClasses.standardHi 3)
        (product (r := (2,72)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 6))) := by
  calc
    _ = product (r := (4,81)) (background.standardClasses.standardHi 0)
      (product (r := (3,80))
        (product (r := (2,16)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 3)) (background.standardClasses.standardHi 6)) :=
      eq_of_heq (background.sphereAlgebra.assoc (1,1) (2,16) (1,64) _ _ _)
    _ = _ := by
      exact congrArg (fun x : background.classical.sphere.Page 2 (3,80) =>
        product (r := (4,81)) (background.standardClasses.standardHi 0) x)
        (eq_of_heq (background.sphereAlgebra.assoc (1,8) (1,8) (1,64)
          (background.standardClasses.standardHi 3) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 6)))
private theorem reorderH0H3H3H7 :
    product (r := (4,145))
      (product (r := (3,17)) (background.standardClasses.standardHi 0)
        (product (r := (2,16)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 3))) (background.standardClasses.standardHi 7) =
    product (r := (4,145)) (background.standardClasses.standardHi 0)
      (product (r := (3,144)) (background.standardClasses.standardHi 3)
        (product (r := (2,136)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 7))) := by
  calc
    _ = product (r := (4,145)) (background.standardClasses.standardHi 0)
      (product (r := (3,144))
        (product (r := (2,16)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 3)) (background.standardClasses.standardHi 7)) :=
      eq_of_heq (background.sphereAlgebra.assoc (1,1) (2,16) (1,128) _ _ _)
    _ = _ := by
      exact congrArg (fun x : background.classical.sphere.Page 2 (3,144) =>
        product (r := (4,145)) (background.standardClasses.standardHi 0) x)
        (eq_of_heq (background.sphereAlgebra.assoc (1,8) (1,8) (1,128)
          (background.standardClasses.standardHi 3) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 7)))
private theorem reorderH0H4H4H7 :
    product (r := (4,161))
      (product (r := (3,33)) (background.standardClasses.standardHi 0)
        (product (r := (2,32)) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 4))) (background.standardClasses.standardHi 7) =
    product (r := (4,161)) (background.standardClasses.standardHi 0)
      (product (r := (3,160)) (background.standardClasses.standardHi 4)
        (product (r := (2,144)) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 7))) := by
  calc
    _ = product (r := (4,161)) (background.standardClasses.standardHi 0)
      (product (r := (3,160))
        (product (r := (2,32)) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 4)) (background.standardClasses.standardHi 7)) :=
      eq_of_heq (background.sphereAlgebra.assoc (1,1) (2,32) (1,128) _ _ _)
    _ = _ := by
      exact congrArg (fun x : background.classical.sphere.Page 2 (3,160) =>
        product (r := (4,161)) (background.standardClasses.standardHi 0) x)
        (eq_of_heq (background.sphereAlgebra.assoc (1,16) (1,16) (1,128)
          (background.standardClasses.standardHi 4) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 7)))

private theorem reorderAdjacent45_zero
    (hz : product (r := (2,48)) (background.standardClasses.standardHi 4)
      (background.standardClasses.standardHi 5) = 0) :
    product (r := (4,81)) (background.standardClasses.standardHi 4)
      (product (r := (3,65)) (background.standardClasses.standardHi 0)
        (product (r := (2,64)) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 5))) = 0 := by
  let z := product (r := (2,64)) (background.standardClasses.standardHi 5)
    (background.standardClasses.standardHi 5)
  calc
    _ = product (r := (4,81))
          (product (r := (2,17)) (background.standardClasses.standardHi 4)
            (background.standardClasses.standardHi 0)) z :=
      eq_of_heq (background.sphereAlgebra.assoc (1,16) (1,1) (2,64) _ _ z).symm
    _ = product (r := (4,81))
          (product (r := (2,17)) (background.standardClasses.standardHi 0)
            (background.standardClasses.standardHi 4)) z := by
      rw [Table.product_comm 1 16 1 1 (by decide)]
    _ = product (r := (4,81)) (background.standardClasses.standardHi 0)
      (product (r := (3,80)) (background.standardClasses.standardHi 4) z) :=
      eq_of_heq (background.sphereAlgebra.assoc (1,1) (1,16) (2,64) _ _ z)
    _ = product (r := (4,81)) (background.standardClasses.standardHi 0)
      (product (r := (3,80))
        (product (r := (2,48)) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 5)) (background.standardClasses.standardHi 5)) := by
      exact congrArg (fun x : background.classical.sphere.Page 2 (3,80) =>
        product (r := (4,81)) (background.standardClasses.standardHi 0) x)
        (eq_of_heq (background.sphereAlgebra.assoc (1,16) (1,32) (1,32)
          (background.standardClasses.standardHi 4) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 5)).symm)
    _ = 0 := by
      rw [hz]
      dsimp only [product]
      simp (config := { congrConsts := false }) only [map_zero, LinearMap.zero_apply]

private theorem reorderAdjacent56_zero
    (hz : product (r := (2,96)) (background.standardClasses.standardHi 5)
      (background.standardClasses.standardHi 6) = 0) :
    product (r := (4,161)) (background.standardClasses.standardHi 5)
      (product (r := (3,129)) (background.standardClasses.standardHi 0)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) = 0 := by
  let z := product (r := (2,128)) (background.standardClasses.standardHi 6)
    (background.standardClasses.standardHi 6)
  calc
    _ = product (r := (4,161))
          (product (r := (2,33)) (background.standardClasses.standardHi 5)
            (background.standardClasses.standardHi 0)) z :=
      eq_of_heq (background.sphereAlgebra.assoc (1,32) (1,1) (2,128) _ _ z).symm
    _ = product (r := (4,161))
          (product (r := (2,33)) (background.standardClasses.standardHi 0)
            (background.standardClasses.standardHi 5)) z := by
      rw [Table.product_comm 1 32 1 1 (by decide)]
    _ = product (r := (4,161)) (background.standardClasses.standardHi 0)
      (product (r := (3,160)) (background.standardClasses.standardHi 5) z) :=
      eq_of_heq (background.sphereAlgebra.assoc (1,1) (1,32) (2,128) _ _ z)
    _ = product (r := (4,161)) (background.standardClasses.standardHi 0)
      (product (r := (3,160))
        (product (r := (2,96)) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 6)) (background.standardClasses.standardHi 6)) := by
      exact congrArg (fun x : background.classical.sphere.Page 2 (3,160) =>
        product (r := (4,161)) (background.standardClasses.standardHi 0) x)
        (eq_of_heq (background.sphereAlgebra.assoc (1,32) (1,64) (1,64)
          (background.standardClasses.standardHi 5) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6)).symm)
    _ = 0 := by
      rw [hz]
      dsimp only [product]
      simp (config := { congrConsts := false }) only [map_zero, LinearMap.zero_apply]

private theorem h2h6_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 2 + hiDegree 6)
      (KIP126.Literature.Standard.hiProduct 2 6) := by
  intro hr
  have hd := sphere_product_d2 (1,4) (1,64) (3,5) (3,65) (4,69)
    (background.standardClasses.standardHi 2) (background.standardClasses.standardHi 6)
    0 (KIP126.Literature.oneLineTarget background 6)
    (low_hi_d2 2 (by decide))
    (KIP126.Literature.Standard.adamsOneLine_d2 6 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 69 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H2H5H5_ne_zero
  simp (config := { congrConsts := false }) only [LinearMap.zero_apply,map_zero,zero_add] at hz
  change product (r := (4,69)) (background.standardClasses.standardHi 2)
    (product (r := (3,65)) (background.standardClasses.standardHi 0)
      (product (r := (2,64)) (background.standardClasses.standardHi 5)
        (background.standardClasses.standardHi 5))) = 0 at hz
  rw [reorderH2H0H5H5] at hz
  exact hz

private theorem h2h7_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 2 + hiDegree 7)
      (KIP126.Literature.Standard.hiProduct 2 7) := by
  intro hr
  have hd := sphere_product_d2 (1,4) (1,128) (3,5) (3,129) (4,133)
    (background.standardClasses.standardHi 2) (background.standardClasses.standardHi 7)
    0 (KIP126.Literature.oneLineTarget background 7)
    (low_hi_d2 2 (by decide))
    (KIP126.Literature.Standard.adamsOneLine_d2 7 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 133 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H2H6H6_ne_zero
  simp (config := { congrConsts := false }) only [LinearMap.zero_apply,map_zero,zero_add] at hz
  change product (r := (4,133)) (background.standardClasses.standardHi 2)
    (product (r := (3,129)) (background.standardClasses.standardHi 0)
      (product (r := (2,128)) (background.standardClasses.standardHi 6)
        (background.standardClasses.standardHi 6))) = 0 at hz
  rw [reorderH2H0H6H6] at hz
  exact hz

private theorem h3h7_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 3 + hiDegree 7)
      (KIP126.Literature.Standard.hiProduct 3 7) := by
  intro hr
  have hd := sphere_product_d2 (1,8) (1,128) (3,9) (3,129) (4,137)
    (background.standardClasses.standardHi 3) (background.standardClasses.standardHi 7)
    0 (KIP126.Literature.oneLineTarget background 7)
    (low_hi_d2 3 (by decide))
    (KIP126.Literature.Standard.adamsOneLine_d2 7 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 137 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H3H6H6_ne_zero
  simp (config := { congrConsts := false }) only [LinearMap.zero_apply,map_zero,zero_add] at hz
  change product (r := (4,137)) (background.standardClasses.standardHi 3)
    (product (r := (3,129)) (background.standardClasses.standardHi 0)
      (product (r := (2,128)) (background.standardClasses.standardHi 6)
        (background.standardClasses.standardHi 6))) = 0 at hz
  rw [reorderH3H0H6H6] at hz
  exact hz

private theorem h4h6_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 4 + hiDegree 6)
      (KIP126.Literature.Standard.hiProduct 4 6) := by
  intro hr
  have hd := sphere_product_d2 (1,16) (1,64) (3,17) (3,65) (4,81)
    (background.standardClasses.standardHi 4) (background.standardClasses.standardHi 6)
    (KIP126.Literature.oneLineTarget background 4) (KIP126.Literature.oneLineTarget background 6)
    (KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide) (by decide)).toHasDifferential
    (KIP126.Literature.Standard.adamsOneLine_d2 6 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 81 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H3H3H6_ne_zero
  change product (r := (4,81))
      (product (r := (3,17)) (background.standardClasses.standardHi 0)
        (product (r := (2,16)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 3))) (background.standardClasses.standardHi 6) +
    product (r := (4,81)) (background.standardClasses.standardHi 4)
      (product (r := (3,65)) (background.standardClasses.standardHi 0)
        (product (r := (2,64)) (background.standardClasses.standardHi 5)
          (background.standardClasses.standardHi 5))) = 0 at hz
  rw [reorderH0H3H3H6, reorderAdjacent45_zero
    (adjacent_product_zero 4 (by decide)), add_zero] at hz
  exact hz

private theorem h5h7_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 5 + hiDegree 7)
      (KIP126.Literature.Standard.hiProduct 5 7) := by
  intro hr
  have hd := sphere_product_d2 (1,32) (1,128) (3,33) (3,129) (4,161)
    (background.standardClasses.standardHi 5) (background.standardClasses.standardHi 7)
    (KIP126.Literature.oneLineTarget background 5) (KIP126.Literature.oneLineTarget background 7)
    (KIP126.Literature.Standard.adamsOneLine_d2 5 (by decide) (by decide)).toHasDifferential
    (KIP126.Literature.Standard.adamsOneLine_d2 7 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 161 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H4H4H7_ne_zero
  change product (r := (4,161))
      (product (r := (3,33)) (background.standardClasses.standardHi 0)
        (product (r := (2,32)) (background.standardClasses.standardHi 4)
          (background.standardClasses.standardHi 4))) (background.standardClasses.standardHi 7) +
    product (r := (4,161)) (background.standardClasses.standardHi 5)
      (product (r := (3,129)) (background.standardClasses.standardHi 0)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) = 0 at hz
  rw [reorderH0H4H4H7, reorderAdjacent56_zero
    (adjacent_product_zero 5 (by decide)), add_zero] at hz
  exact hz


/- The native quotient relation h₄h₆² = 0, certified by its archive row. -/
section NativeRelationCertificate
open Lean Elab Tactic Meta
private meta partial def relationBalancedChars (cs : List Char) : Expr :=
  if cs.length ≤ 128 then
    let charTy := mkConst ``Char
    let cons := mkApp (mkConst ``List.cons [.zero]) charTy
    cs.reverse.foldl (fun acc c => mkApp2 cons (toExpr c) acc)
      (mkApp (mkConst ``List.nil [.zero]) charTy)
  else
    mkApp3 (mkConst ``List.append [.zero]) (mkConst ``Char)
      (relationBalancedChars (cs.take (cs.length/2)))
      (relationBalancedChars (cs.drop (cs.length/2)))
private meta def relationMember : TacticM Unit := do
  let g ← getMainGoal
  let target ← instantiateMVars (←g.getType)
  let some split := target.find? (fun e => e.isAppOfArity ``String.splitOn 2)
    | throwError "Expected string split membership"
  let se := split.getAppArgs[0]!
  let normalized ← withTransparency .all (whnf se)
  let .lit (.strVal s) := normalized
    | throwError "Expected a literal archive relation chunk"
  let code := "7,1,69,2"
  let parts := s.splitOn ("\n"++code++"\n")
  unless parts.length=2 do throwError "Expected unique relation row"
  let ae := relationBalancedChars parts[0]!.toList
  let ce := relationBalancedChars code.toList
  let be := relationBalancedChars parts[1]!.toList
  let proofTerm ← mkAppM ``KIP126.Computation.Standard.nativeCoreMiddleMember
    #[se,toExpr code,ae,ce,be]
  let gs ← g.apply proofTerm
  replaceMainGoal gs
  evalTactic (← `(tactic| all_goals first | rfl | decide +kernel))
end NativeRelationCertificate

private theorem source_h4_h6_square_zero : sourceData.product 1 16 2 128 (sourceData.atom .h4)
    (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6)) = 0 := by
  apply Subtype.ext
  change (Ideal.Quotient.mk _ (MvPolynomial.X (⟨7, by decide⟩ : Fin 2914))) *
    ((Ideal.Quotient.mk _ (MvPolynomial.X (⟨69, by decide⟩ : Fin 2914))) *
      (Ideal.Quotient.mk _ (MvPolynomial.X (⟨69, by decide⟩ : Fin 2914)))) = 0
  rw [←map_mul, ←map_mul]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  refine ⟨"7,1,69,2", ?_, ?_⟩
  · apply List.mem_append.mpr
    right
    apply List.mem_flatMap.mpr
    refine ⟨_,Array.getElem_mem_toList (i:=11) (by decide),?_⟩
    run_tac relationMember
  · have hs : "7,1,69,2".splitOn ";"=["7,1,69,2"] := by
      rw [show ";"=String.singleton ';' from rfl,nativeCoreSplitOnChar]
      rfl
    have hm : (("7,1,69,2".splitOn ",").map (fun n=>n.toNat?.getD 0))=[7,1,69,2] := by
      have hx : "7,1,69,2".splitOn ","=["7","1","69","2"] := by
        rw [show ","=String.singleton ',' from rfl,nativeCoreSplitOnChar]
        rfl
      rw [hx]
      simp (config := { congrConsts := false }) +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    change _ = (("7,1,69,2".splitOn ";").map _).sum
    rw [hs]
    simp (config := { congrConsts := false }) only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    change _ = (if "7,1,69,2"="" then 1 else _) + 0
    simp (config := { congrConsts := false }) only [if_neg (by decide : "7,1,69,2"≠"")]
    rw [hm]
    change _ = (MvPolynomial.X (⟨7,by decide⟩ : Fin 2914))^1 *
      ((MvPolynomial.X (⟨69,by decide⟩ : Fin 2914))^2 * 1) + 0
    ring


private theorem actual_h4_h6_square_zero :
    product (r := (3,144)) (background.standardClasses.standardHi 4)
      (product (r := (2,128)) (background.standardClasses.standardHi 6)
        (background.standardClasses.standardHi 6)) = 0 := by
  have h := comparison_product 1 16 2 128 (by decide) (sourceData.atom .h4)
    (sourceData.product 1 64 1 64 (sourceData.atom .h6) (sourceData.atom .h6))
  rw [source_h4_h6_square_zero,map_zero,comparison_product 1 64 1 64,
    comparison_h4,comparison_h6] at h
  exact h.symm

private theorem h4_h0_h6_square_zero :
    product (r := (4,145)) (background.standardClasses.standardHi 4)
      (product (r := (3,129)) (background.standardClasses.standardHi 0)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) = 0 := by
  let z := product (r := (2,128)) (background.standardClasses.standardHi 6)
    (background.standardClasses.standardHi 6)
  calc
    _ = product (r := (4,145))
          (product (r := (2,17)) (background.standardClasses.standardHi 4)
            (background.standardClasses.standardHi 0)) z :=
      eq_of_heq (background.sphereAlgebra.assoc (1,16) (1,1) (2,128) _ _ z).symm
    _ = product (r := (4,145))
          (product (r := (2,17)) (background.standardClasses.standardHi 0)
            (background.standardClasses.standardHi 4)) z := by
      rw [Table.product_comm 1 16 1 1 (by decide)]
    _ = product (r := (4,145)) (background.standardClasses.standardHi 0)
      (product (r := (3,144)) (background.standardClasses.standardHi 4) z) :=
      eq_of_heq (background.sphereAlgebra.assoc (1,1) (1,16) (2,128) _ _ z)
    _ = 0 := by
      rw [actual_h4_h6_square_zero]
      dsimp only [product]
      simp (config := { congrConsts := false }) only [map_zero]

private theorem h4h7_not_reaches :
    ¬ ReachesPage background.classical.sphere 3 (hiDegree 4 + hiDegree 7)
      (KIP126.Literature.Standard.hiProduct 4 7) := by
  intro hr
  have hd := sphere_product_d2 (1,16) (1,128) (3,17) (3,129) (4,145)
    (background.standardClasses.standardHi 4) (background.standardClasses.standardHi 7)
    (KIP126.Literature.oneLineTarget background 4) (KIP126.Literature.oneLineTarget background 7)
    (KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide) (by decide)).toHasDifferential
    (KIP126.Literature.Standard.adamsOneLine_d2 7 (by decide) (by decide)).toHasDifferential
    (by decide) (by decide) (finite_page_neg 4 145 (by decide))
  have hz := reached_d2_target_zero hr hd
  apply fourLineH0H3H3H7_ne_zero
  change product (r := (4,145))
      (product (r := (3,17)) (background.standardClasses.standardHi 0)
        (product (r := (2,16)) (background.standardClasses.standardHi 3)
          (background.standardClasses.standardHi 3))) (background.standardClasses.standardHi 7) +
    product (r := (4,145)) (background.standardClasses.standardHi 4)
      (product (r := (3,129)) (background.standardClasses.standardHi 0)
        (product (r := (2,128)) (background.standardClasses.standardHi 6)
          (background.standardClasses.standardHi 6))) = 0 at hz
  rw [reorderH0H3H3H7, h4_h0_h6_square_zero, add_zero] at hz
  exact hz

/-- Candidates among the nonzero products hᵢhⱼ with 0 ≤ i ≤ j ≤ 7
that reach E₃. -/
public theorem two_line_d2_candidates (i j : ℕ) (hij : i ≤ j)
    (hiBound : i ≤ 7) (hjBound : j ≤ 7)
    (hne : KIP126.Literature.Standard.hiProduct i j ≠ 0)
    (hreach : ReachesPage background.classical.sphere 3 (hiDegree i + hiDegree j)
      (KIP126.Literature.Standard.hiProduct i j)) : TwoLineD2Candidate i j := by
  -- Of the 36 ordered pairs, seven adjacent products vanish in E₂ and
  -- Nine further products have the nonzero d₂ targets identified above.
  interval_cases i <;> interval_cases j <;> first
    | exact (by unfold TwoLineD2Candidate; decide)
    | omega
    | exact (hne (adjacent_product_zero _ (by decide))).elim
    | exact (h0h5_not_reaches hreach).elim
    | exact (h0h6_not_reaches hreach).elim
    | exact (h0h7_not_reaches hreach).elim
    | exact (h2h6_not_reaches hreach).elim
    | exact (h2h7_not_reaches hreach).elim
    | exact (h3h7_not_reaches hreach).elim
    | exact (h4h6_not_reaches hreach).elim
    | exact (h4h7_not_reaches hreach).elim
    | exact (h5h7_not_reaches hreach).elim

end KIP126.SSComputation
