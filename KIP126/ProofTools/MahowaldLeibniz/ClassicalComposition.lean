module

import all KIP126.ProofTools.MahowaldLeibniz.Corollaries
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGCorollary
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHCorollary

/-! Classical NC composition for all normalized exponent positions.
Only actual selected operations and homogeneous-label transports occur
in these internal specializations. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

private theorem pdf_conditions_classical_corollary_heq
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+(c+1)+1,t+(c+1)))
    (z : Ambient background T.Z (s+(c+1)+1,(t+(c+1))+1))
    (v : Ambient background T.Y ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q))
    (hu : ∃ u' : Ambient background T.X (s+(c+1)+1,((t+(c+1))+1)-1),
      (background.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
        ((background.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) u' ∧ HEq u' u)
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      ((c+1)+1) (s,t) (s+(c+1)+1,t+(c+1)) x u)
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+(c+1)+1,(t+(c+1))+1) ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) z
      ((background.classical.map T.g).pageMap 2 ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      cycles background T.X (((q+1:ℕ):ℤ)-j)
        ((s+(c+1)+1)+j,(t+(c+1))+j) ≤
      boundaries background T.X ((c:ℤ)+j+1)
        ((s+(c+1)+1)+j,(t+(c+1))+j))
    (hNC2 : ∀ a : Ambient background T.X
        ((s+(c+1)+1)+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        ((s+(c+1)+1)+(q+1:ℕ)-1) ((t+(c+1))+(q+1:ℕ)-1) a ∈
      boundaries background T.Y (c+(q+1))
        ((s+(c+1)+1)+(q+1:ℕ)-1+1,(t+(c+1))+(q+1:ℕ)-1+1)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle background T.Y (c+(q+1)) (s+1,t+1) y ∧
      DifferentialAt background T.Y (c+(q+1)+1) (s+1,t+1)
        ((s+(c+1)+1)+q+1,((t+(c+1))+1)+q) y v := by
  obtain ⟨u',hu',hU⟩ := hu
  apply pdf_conditions_classical_corollary T he hT hf hg hh c q hq s t x u z v ?_ hdx hdz hNC1 hNC2
  let uc : Ambient background T.X (s+(c+1)+1,((t+(c+1))+1)-1) := by simpa using u
  have hc : HEq uc u := cast_heq _ _
  have heq : u'=uc := eq_of_heq (hU.trans hc.symm)
  change (background.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
    ((background.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) uc
  rw [←heq]
  exact hu'

private theorem pdf_conditions_classical_corollary_RK
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (R K : ℕ) (hR : 2≤R) (hK : 2≤K) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (u : Ambient background T.X (s+R,t+R-1))
    (z : Ambient background T.Z (s+R,t+R))
    (v : Ambient background T.Y (s+R+K,t+R+K-1))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
      ((background.classical.map T.h).pageMap 2 (s+R,t+R) z) u)
    (hdx : DifferentialAt background T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt background T.Z K (s+R,t+R) (s+R+K,t+R+K-1) z
      ((background.classical.map T.g).pageMap 2 (s+R+K,t+R+K-1) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<K-1 →
      cycles background T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries background T.X ((R:ℤ)+j-1) (s+R+j,t+R+j-1))
    (hNC2 : ∀ a : Ambient background T.X (s+R+K-1,t+R+K-2),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        (s+R+K-1) (t+R+K-2) a ∈
      boundaries background T.Y ((R:ℤ)+K-2)
        ((s+R+K-1)+1,(t+R+K-2)+1)) :
    let y := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
    IsCycle background T.Y ((R:ℤ)+K-2) (s+1,t+1) y ∧
      DifferentialAt background T.Y ((R:ℤ)+K-1) (s+1,t+1) (s+R+K,t+R+K-1) y v := by
  obtain ⟨c,rfl⟩ : ∃c,R=c+2 := ⟨R-2,by omega⟩
  obtain ⟨q,rfl⟩ : ∃q,K=q+1 := ⟨K-1,by omega⟩
  have Hst := pdf_conditions_classical_corollary_heq T he hT hf hg hh c q (by omega) s t
  rw [show (s+((c:ℤ)+1)+1)+q+1=s+(c+2:ℕ)+(q+1:ℕ) by omega,
    show ((t+((c:ℤ)+1))+1)+q=t+(c+2:ℕ)+(q+1:ℕ)-1 by omega,
    show (t+((c:ℤ)+1))+1=t+(c+2:ℕ) by omega,
    show s+((c:ℤ)+1)+1=s+(c+2:ℕ) by omega,
    show t+((c:ℤ)+1)=t+(c+2:ℕ)-1 by omega] at Hst
  rw [show ((c:ℤ)+1)+1=(c+2:ℕ) by omega,
    show ((c:ℤ)+((q:ℤ)+1)+1)=(c+2:ℕ)+(q+1:ℕ)-1 by omega,
    show ((c:ℤ)+((q:ℤ)+1))=(c+2:ℕ)+(q+1:ℕ)-2 by omega,
    show (t+(c+2:ℕ)-1)+(q+1:ℕ)-1=t+(c+2:ℕ)+(q+1:ℕ)-2 by omega] at Hst
  have hind (j : ℕ) : (t+(c+2:ℕ)-1)+j=t+(c+2:ℕ)+j-1 := by omega
  have hbound (j : ℕ) : (c:ℤ)+j+1=(c+2:ℕ)+j-1 := by omega
  have HNC := Hst x u z v ⟨u,hu,HEq.rfl⟩ hdx.2 hdz.2
  apply HNC ?_ hNC2
  intro j hj hjq
  rw [hind j,hbound j]
  exact hNC1 j hj hjq

private theorem classical_label_regrade_heq {X : AdamsObject (coefficients := background.coefficients)} {p q : ℤ×ℤ}
    (h : p=q) (x : Ambient background X p) : HEq (classicalLabelRegrade h x) x := by
  subst q
  rfl

private theorem classical_map_label_heq (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient background X p) (b : Ambient background X q)
    (hab : HEq a b) :
    HEq ((background.classical.map f).pageMap 2 p a)
      ((background.classical.map f).pageMap 2 q b) := by
  subst q
  cases eq_of_heq hab
  rfl

private theorem classical_cycle_heq (X : AdamsObject (coefficients := background.coefficients)) (r : ℤ)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient background X p) (b : Ambient background X q)
    (hab : HEq a b) (ha : IsCycle background X r p a) : IsCycle background X r q b := by
  subst q
  cases eq_of_heq hab
  exact ha

private theorem classical_boundary_heq (X : AdamsObject (coefficients := background.coefficients)) (r : ℤ)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient background X p) (b : Ambient background X q)
    (hab : HEq a b) (ha : a ∈ boundaries background X r p) : b ∈ boundaries background X r q := by
  subst q
  cases eq_of_heq hab
  exact ha

private theorem classical_differential_heq (X : AdamsObject (coefficients := background.coefficients)) (r : ℤ)
    {p p' q q' : ℤ×ℤ} (hp : p=p') (hq : q=q')
    (a : Ambient background X p) (a' : Ambient background X p')
    (b : Ambient background X q) (b' : Ambient background X q')
    (ha : HEq a a') (hb : HEq b b')
    (hd : DifferentialAt background X r p q a b) :
    DifferentialAt background X r p' q' a' b' := by
  subst p' q'
  cases eq_of_heq ha
  cases eq_of_heq hb
  exact hd

private theorem normalized_operation_zero_heq (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (hf : normalizedExponent background.classicalTower f = 0)
    (s t : ℤ) (x : Ambient background X (s,t)) :
    HEq (normalizedClassicalOperation X Y f s t x)
      ((background.classical.map f).pageMap 2 (s,t) x) :=
  (classical_label_regrade_heq _ _).symm.trans
    (heq_of_eq (normalized_classical_operation_zero X Y f hf s t x))

private theorem normalized_operation_f_one_heq (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (s t : ℤ) (x : Ambient background T.X (s,t)) :
    HEq (normalizedClassicalOperation T.X T.Y T.f s t x)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) :=
  (classical_label_regrade_heq _ _).symm.trans
    (heq_of_eq (normalized_classical_operation_f_one T hf s t x))

private theorem positive_f_classical_nc_statement
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0) :
    ClassicalNCCompositionStatement T he := by
  have hT := KIP126.Literature.Standard.normalized_triangle_distinguished T he
  intro R K hR hK s t x z v hx hz hu hdz hNC1 hNC2
  have hzdeg : (s+R-normalizedExponent background.classicalTower T.h,
      t+R-normalizedExponent background.classicalTower T.h)=(s+R,t+R) := by simp [hh]
  have hvdeg : (s+R+normalizedExponent background.classicalTower T.f+K-1,
      t+R+normalizedExponent background.classicalTower T.f+K-2)=(s+R+K,t+R+K-1) := by
    simp only [hf,Nat.cast_one]
    ext <;> dsimp <;> omega
  let z0 := classicalLabelRegrade hzdeg z
  let v0 := classicalLabelRegrade hvdeg v
  have hz0 : HEq z z0 := (classical_label_regrade_heq hzdeg z).symm
  have hv0 : HEq v v0 := (classical_label_regrade_heq hvdeg v).symm
  obtain ⟨u,hu,hdx⟩ := hu
  have hhu : HEq
      (classicalLabelRegrade (X := .shift 1 T.X) (q := (s+R,t+R))
        (by ext <;> dsimp <;> omega)
        (normalizedClassicalOperation T.Z (.shift 1 T.X) T.h
          (s+R-normalizedExponent background.classicalTower T.h)
          (t+R-normalizedExponent background.classicalTower T.h) z))
      ((background.classical.map T.h).pageMap 2 (s+R,t+R) z0) :=
    (classical_label_regrade_heq _ _).trans
      ((normalized_operation_zero_heq T.Z (.shift 1 T.X) T.h hh _ _ z).trans
        (classical_map_label_heq T.Z (.shift 1 T.X) T.h hzdeg z z0 hz0))
  rw [eq_of_heq hhu] at hu
  have htarget : HEq
      (classicalLabelRegrade (X := T.Z)
        (q := (s+R-normalizedExponent background.classicalTower T.h+K,
          t+R-normalizedExponent background.classicalTower T.h+K-1))
        (by ext <;> dsimp <;> omega)
        (normalizedClassicalOperation T.Y T.Z T.g
          (s+R+normalizedExponent background.classicalTower T.f+K-1)
          (t+R+normalizedExponent background.classicalTower T.f+K-2) v))
      ((background.classical.map T.g).pageMap 2 (s+R+K,t+R+K-1) v0) :=
    (classical_label_regrade_heq _ _).trans
      ((normalized_operation_zero_heq T.Y T.Z T.g hg _ _ v).trans
        (classical_map_label_heq T.Y T.Z T.g hvdeg v v0 hv0))
  have hdz0 := classical_differential_heq T.Z K hzdeg
    (show (s+R-normalizedExponent background.classicalTower T.h+K,
      t+R-normalizedExponent background.classicalTower T.h+K-1)=(s+R+K,t+R+K-1) by simp [hh])
    z z0 _ _ hz0 htarget hdz
  have hNC2' : ∀ a : Ambient background T.X (s+R+K-1,t+R+K-2),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf
        (s+R+K-1) (t+R+K-2) a ∈
      boundaries background T.Y ((R:ℤ)+K-2)
        ((s+R+K-1)+1,(t+R+K-2)+1) := by
    intro a
    exact classical_boundary_heq T.Y ((R:ℤ)+K-2)
      (by simp only [hf,Nat.cast_one]) _ _
      (normalized_operation_f_one_heq T hf _ _ a) (hNC2 a)
  obtain ⟨hy,hdy⟩ := pdf_conditions_classical_corollary_RK T he hT hf hg hh
    R K hR hK s t x u z0 v0 hu hdx hdz0 hNC1 hNC2'
  let y := normalizedClassicalOperation T.X T.Y T.f s t x
  let y0 := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x
  have hydeg : (s+1,t+1)=(s+normalizedExponent background.classicalTower T.f,
      t+normalizedExponent background.classicalTower T.f) := by simp [hf]
  have hyy : HEq y0 y := (normalized_operation_f_one_heq T hf s t x).symm
  exact ⟨classical_cycle_heq T.Y ((R:ℤ)+K-2) hydeg y0 y hyy hy,
    classical_differential_heq T.Y ((R:ℤ)+K-1) hydeg hvdeg.symm
      y0 y v0 v hyy hv0.symm hdy⟩

/-- The NC1/NC2 conditions imply the full classical composition conclusion for
all three possible positions of the positive normalized exponent. -/
private theorem classical_nc_composition
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1) :
    ClassicalNCCompositionStatement T he := by
  have hcases :
      (normalizedExponent background.classicalTower T.f = 1 ∧
        normalizedExponent background.classicalTower T.g = 0 ∧
        normalizedExponent background.classicalTower T.h = 0) ∨
      (normalizedExponent background.classicalTower T.f = 0 ∧
        normalizedExponent background.classicalTower T.g = 1 ∧
        normalizedExponent background.classicalTower T.h = 0) ∨
      (normalizedExponent background.classicalTower T.f = 0 ∧
        normalizedExponent background.classicalTower T.g = 0 ∧
        normalizedExponent background.classicalTower T.h = 1) := by omega
  rcases hcases with ⟨hf,hg,hh⟩ | ⟨hf,hg,hh⟩ | ⟨hf,hg,hh⟩
  · exact positive_f_classical_nc_statement T he hf hg hh
  · exact positive_g_classical_nc_statement T he hf hg hh
  · exact positive_h_classical_nc_statement T he hf hg hh

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
