module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyDifferential
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyTorsionTransfer

/-! The ordinary-first branches of the early-boundary torsion corollary.
The paper parameter is r = N + 1. Literature.boundaries b includes d_b
and is the paper space B_{<b+1}; hence the candidate upper bound
B_{<r+j+1} is expressed by boundaries (N+j+1).
All original source, target, root, and terminal conditions are retained.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

/-- The complete displayed-source torsion criterion for the ordinary third branch.
Taking i = 1 includes the early d₂ case. -/
public theorem ordinary_early_torsion_target_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (N i d : ℕ) (hi : 0 < i) (hiN : i < N) (hd : 0 < d) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (y : Ambient background T.Y (s,t))
    (hy : y-(background.classical.map T.f).pageMap 2 (s,t) x∈boundaries background T.Y N (s,t))
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y ((s+N)+d+1,(t+N)+d))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 → permanentCycles background T.Y (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
    (Qm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hQm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      boundaries background T.Y ((N:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j) ≤ Qm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j ⊓ Qm j →
        ∃ z : Ambient background T.Z (((s+N)+1)+j-1,(t+N)+j),
          z ∈ cycles background T.Z (((d+1):ℤ)-j) (((s+N)+1)+j-1,(t+N)+j) ∧
        ∃ u : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
          (background.classicalSuspension T.X).DesuspendsClass (((s+N)+1)+j-1+1) ((t+N)+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (((s+N)+1)+j-1) ((t+N)+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j))
    (c : Ambient background T.Y ((s+N)-i,(t+N)-i))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (((s+N)-i),((t+N)-i)) ((s+N)+1,(t+N)) c ((background.classical.map T.f).pageMap 2 ((s+N)+1,(t+N)) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) (((s+N)-i),((t+N)-i)) (((s+N)+d+1),((t+N)+d)) ((background.classical.map T.g).pageMap 2 (((s+N)-i),((t+N)-i)) c)
      ((background.classical.map T.g).pageMap 2 (((s+N)+d+1),((t+N)+d)) v))
    (hR : ∀ p : ℤ, ((s+N)-i)+1≤p → p<((s+N)-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,((t+N)-i)-((s+N)-i)+p), z ∈ cycles background T.Z ((i+1)-(p-((s+N)-i)).toNat:ℕ) (p,((t+N)-i)-((s+N)-i)+p) →
      ∃ y : Ambient background T.Y (p,((t+N)-i)-((s+N)-i)+p), y ∈ cycles background T.Y ((i+1)-(p-((s+N)-i)).toNat:ℕ) (p,((t+N)-i)-((s+N)-i)+p) ∧
      ∃ k : Ambient background T.Z (p,((t+N)-i)-((s+N)-i)+p), k ∈ cycles background T.Z ((i+d)+1-(p-((s+N)-i)).toNat:ℕ) (p,((t+N)-i)-((s+N)-i)+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,((t+N)-i)-((s+N)-i)+p) y-k ∈ boundaries background T.Z ((p-((s+N)-i)).toNat+1) (p,((t+N)-i)-((s+N)-i)+p))
    (hH : ∀ z : Ambient background T.Z (((s+N)-i)+(i+1)-1,((t+N)-i)+(i+1)-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (((s+N)-i)+(i+1)-1) (((t+N)-i)+(i+1)-1) z ∈
          boundaries background (.shift 1 T.X) (i+1) ((((s+N)-i)+(i+1)-1)+1,(((t+N)-i)+(i+1)-1)+1))
    (P : Submodule ℤ (Ambient background T.Y ((s+N)+d+1,(t+N)+d)))
    (hP : permanentCycles background T.Y ((s+N)+d+1,(t+N)+d)≤P) (hv : v∈P)
    (hker : ∀ z∈P, (background.classical.map T.g).pageMap 2 ((s+N)+d+1,(t+N)+d) z=0 →
      z∈boundaries background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d)) :
    IsCycle background T.Y (N+d:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d) v ∧
      DifferentialAt background T.Y ((N+d:ℕ)+1) (s,t) ((s+N)+d+1,(t+N)+d) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨a,u',aHat,D,ha,hu,hD,_,himageA⟩ :=
    ordinary_compatible_source_third_at T he hf hg hh
      i (i+d) hi (by omega) ((s+N)-i) ((t+N)-i) (s+N) (t+N)
      ((s+N)+d+1) ((t+N)+d) (d+1) d
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      c u v hearly hdroot hR hH
  have himg : a≫XModLambdaN.map (background.nu.functor.map T.f) (d+1)-D≫XModLambdaN.incl _ (d+1)=
      homotopyRegrade (show ((t+N)+d)-((s+N)+d+1)=(t+N)-(s+N+1) by omega)
        (show ((t+N)+d)-d=t+N by omega) (finiteTopLabel T.Y d hd ((s+N)+d+1) ((t+N)+d) v) := by
    rw [himageA,add_sub_cancel_left]
    simp only [finiteTopLabelAtWeight,normalized_homotopy_regrade_trans]
  have hCand (j : ℕ) (hj : 1≤j) (hjd : j<(d+1)-1) :
      boundaries background T.Y ((N:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j ⊓ Qm j := by
    intro b hb
    exact ⟨hPm j hj hjd ((boundaries_le_finalBoundaries T.Y _ _).trans
      (finalBoundaries_le_permanentCycles T.Y _) hb), hQm j hj hjd hb⟩
  exact torsion_ordinary_early_target_of_compatible_source_third T he hT hf hg hh
    N i d hi hiN hd s t x y hy u u' hdx hu v (fun j => Pm j ⊓ Qm j) hCand hmid
      a ha aHat D hD himg P hP hv hker

/-- The complete displayed-source torsion criterion for the ordinary second branch.
Taking i = 1 includes the early d₂ case. -/
public theorem ordinary_early_torsion_target_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (N i d : ℕ) (hi : 0 < i) (hiN : i < N) (hd : 0 < d) (s t : ℤ)
    (x : Ambient background T.X (s,t)) (y : Ambient background T.Y (s,t))
    (hy : y-(background.classical.map T.f).pageMap 2 (s,t) x∈boundaries background T.Y N (s,t))
    (u : Ambient background T.X (s+N+1,t+N))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (s,t) (s+N+1,t+N) x u)
    (v : Ambient background T.Y ((s+N)+d+1,(t+N)+d))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 → permanentCycles background T.Y (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j)
    (Qm : (j : ℕ) → Submodule ℤ (Ambient background T.Y (((s+N)+1)+j-1+1,(t+N)+j)))
    (hQm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      boundaries background T.Y ((N:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j) ≤ Qm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j ⊓ Qm j →
        ∃ z : Ambient background T.Z (((s+N)+1)+j-1+1,(t+N)+j+1),
          z ∈ cycles background T.Z (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j+1) ∧
        ∃ u : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
          (background.classicalSuspension T.X).DesuspendsClass (((s+N)+1)+j-1+1) ((t+N)+j+1)
            ((background.classical.map T.h).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j+1) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j))
    (c : Ambient background T.Y ((s+N)-i,(t+N)-i))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (((s+N)-i),((t+N)-i)) ((s+N)+1,(t+N)) c ((background.classical.map T.f).pageMap 2 ((s+N)+1,(t+N)) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) (((s+N)-i)+1,((t+N)-i)+1) (((s+N)+d+1)+1,((t+N)+d)+1)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) ((s+N)-i) ((t+N)-i) c)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) ((s+N)+d+1) ((t+N)+d) v))
    (hR : ∀ p : ℤ, ((s+N)-i)+1≤p → p<((s+N)-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p+1,(((t+N)-i)-((s+N)-i)+p)+1),
        z ∈ cycles background T.Z ((i+1)-(p-((s+N)-i)).toNat:ℕ) (p+1,(((t+N)-i)-((s+N)-i)+p)+1) →
      ∃ y : Ambient background T.Y (p,((t+N)-i)-((s+N)-i)+p),
        y ∈ cycles background T.Y ((i+1)-(p-((s+N)-i)).toNat:ℕ) (p,((t+N)-i)-((s+N)-i)+p) ∧
      ∃ k : Ambient background T.Z (p+1,(((t+N)-i)-((s+N)-i)+p)+1),
        k ∈ cycles background T.Z ((i+d)+1-(p-((s+N)-i)).toNat:ℕ) (p+1,(((t+N)-i)-((s+N)-i)+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p (((t+N)-i)-((s+N)-i)+p) y-k ∈
          boundaries background T.Z ((p-((s+N)-i)).toNat+1) (p+1,(((t+N)-i)-((s+N)-i)+p)+1))
    (hH : ∀ z : Ambient background T.Z (((s+N)-i)+(i+1),(((t+N)-i)+(i+1)-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (((s+N)-i)+(i+1)) (((t+N)-i)+(i+1)-1) z ∈
        boundaries background T.X (i+1) (((s+N)-i)+(i+1),((t+N)-i)+(i+1)-1))
    (P : Submodule ℤ (Ambient background T.Y ((s+N)+d+1,(t+N)+d)))
    (hP : permanentCycles background T.Y ((s+N)+d+1,(t+N)+d)≤P) (hv : v∈P)
    (hker : ∀ z∈P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) ((s+N)+d+1) ((t+N)+d) z=0 →
      z∈boundaries background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d)) :
    IsCycle background T.Y (N+d:ℕ) (s,t) y ∧
      IsCycle background T.Y (N+d:ℕ) ((s+N)+d+1,(t+N)+d) v ∧
      DifferentialAt background T.Y ((N+d:ℕ)+1) (s,t) ((s+N)+d+1,(t+N)+d) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨a,u',aHat,D,ha,hu,hD,_,himageA⟩ :=
    ordinary_compatible_source_second_at T he hf hg hh
      i (i+d) hi (by omega) ((s+N)-i) ((t+N)-i) (s+N) (t+N)
      ((s+N)+d+1) ((t+N)+d) (d+1) d
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      c u v hearly hdroot hR hH
  have himg : a≫XModLambdaN.map (background.nu.functor.map T.f) (d+1)-D≫XModLambdaN.incl _ (d+1)=
      homotopyRegrade (show ((t+N)+d)-((s+N)+d+1)=(t+N)-(s+N+1) by omega)
        (show ((t+N)+d)-d=t+N by omega) (finiteTopLabel T.Y d hd ((s+N)+d+1) ((t+N)+d) v) := by
    rw [himageA,add_sub_cancel_left]
    simp only [finiteTopLabelAtWeight,normalized_homotopy_regrade_trans]
  have hCand (j : ℕ) (hj : 1≤j) (hjd : j<(d+1)-1) :
      boundaries background T.Y ((N:ℤ)+j+1) (((s+N)+1)+j-1+1,(t+N)+j) ≤ Pm j ⊓ Qm j := by
    intro b hb
    exact ⟨hPm j hj hjd ((boundaries_le_finalBoundaries T.Y _ _).trans
      (finalBoundaries_le_permanentCycles T.Y _) hb), hQm j hj hjd hb⟩
  exact torsion_ordinary_early_target_of_compatible_source_second T he hT hf hg hh
    N i d hi hiN hd s t x y hy u u' hdx hu v (fun j => Pm j ⊓ Qm j) hCand hmid
      a ha aHat D hD himg P hP hv hker

end
end KIP126.ProofTools.Internal.SyntheticCoverage
