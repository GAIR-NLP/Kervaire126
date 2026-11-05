module

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.EarlyBoundaryDifferential
import all KIP126.ProofTools.SyntheticCoverage.BottomFiniteLift
import all KIP126.ProofTools.SyntheticCoverage.EarlySourceCorrection
import all KIP126.ProofTools.SyntheticCoverage.EarlySelectiveTop

/-! Early-boundary target differentials. The finite source and its actual
absolute boundary are retained through the final extension and decoding.
The original candidate kernel is applied only after an actual differential
has been constructed. -/

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
set_option maxHeartbeats 3000000


private theorem early_bi_susp_regrade {A : SyntheticSpectrum}
    {m m' w w' : ℤ} (hm : m=m') (hw : w=w') (i : ℤ)
    (a : BiHom m w (((SyntheticCategory.biShift (0,-i)).obj A)⟦(1:ℤ)⟧)) :
    biSuspensionHomEquiv m' w' i A (homotopyRegrade hm hw a)=
      homotopyRegrade (by omega) (by omega) (biSuspensionHomEquiv m w i A a) := by
  subst m'; subst w'; rfl

/-- A fixed finite source whose actual boundary has the prescribed top
extends to the output page. The actual last error is then removed by the
original restricted kernel, after its constructed differential target has
provided permanence. This lemma is only the terminal step. -/
private theorem early_target_of_retained_boundary_top
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (L d : ℕ) (hL : 1≤L) (hd : 0<d) (s t : ℤ)
    (y : Ambient background Y (s,t))
    (v error : Ambient background Y (s+(L+d)+1,t+(L+d)))
    (P : Submodule ℤ (Ambient background Y (s+(L+d)+1,t+(L+d))))
    (hP : permanentCycles background Y (s+(L+d)+1,t+(L+d)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map g).pageMap 2 (s+(L+d)+1,t+(L+d)) a=0 →
      a∈boundaries background Y (L+d) (s+(L+d)+1,t+(L+d)))
    (he : (background.classical.map g).pageMap 2 (s+(L+d)+1,t+(L+d)) error=0)
    (ξ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) L))
    (hξ : ξ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel Y s t y)
    (htop : homotopyRegrade
        (show (t-s)-1=(t+(L+d))-(s+(L+d)+1) by omega)
        (show t+L=(t+(L+d))-d by omega)
        (biSuspensionHomEquiv (t-s) t L (background.nu.functor.obj (Y.obj background.auxiliary))
          (ξ ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ (d+1)) =
      finiteTopLabel Y d hd (s+(L+d)+1) (t+(L+d)) (v+error)) :
    IsCycle background Y (L+d) (s,t) y ∧
      IsCycle background Y (L+d) (s+(L+d)+1,t+(L+d)) v ∧
      DifferentialAt background Y (L+d+1) (s,t) (s+(L+d)+1,t+(L+d)) y v := by
  obtain ⟨η,w,hη,hw,_,hwe⟩ := finite_extension_of_boundary_top Y L d (by omega) hd
    (t-s) t (s+(L+d)+1) (t+(L+d)) (by omega) (by omega) ξ (v+error) htop
  have hfirst : η ≫ (background.quotients.tower _).rho 1 (L+d) (by omega)=nativeFirstLabel Y s t y := by
    rw [←(background.quotients.tower _).rho_comp hL (show L≤L+d by omega),←Category.assoc,hη,hξ]
  have hboundary : adjacentBoundaryLabel Y (L+d) s t η=
      nativeFirstLabel Y (s+(L+d)+1) (t+(L+d)) w := by
    simpa only [adjacentBoundaryLabel,boundaryRepresentative,regrade_comp,
      normalized_homotopy_regrade_trans] using hw
  have hdiff : DifferentialAt background Y (L+d+1) (s,t) (s+(L+d)+1,t+(L+d)) y w :=
    ⟨by omega,(differential_iff_specified_adjacent_lift Y (L+d) (by omega) s t y w).mpr
      ⟨η,hfirst,hboundary⟩⟩
  have herr : w-v-error ∈ boundaries background Y (L+d+1-1) (s+(L+d)+1,t+(L+d)) := by
    have hh := boundaries_monotone background Y (s+(L+d)+1,t+(L+d))
      (show (d:ℤ)+1≤L+d+1-1 by omega) hwe
    simpa only [sub_add_eq_sub_sub] using hh
  have hfinal := differential_target_of_permanent_candidate_kernel Y Z g (L+d+1)
    (s,t) (s+(L+d)+1,t+(L+d)) y w v error P hP hdiff hv herr he
    (by simpa only [add_sub_cancel_right] using hker)
  have hcycles := cycles_of_differential Y _ _ _ _ _ hfinal
  refine ⟨?_,?_,hfinal⟩
  · simpa only [add_sub_cancel_right] using hcycles.1
  · simpa only [add_sub_cancel_right] using hcycles.2

/-- The terminal construction in prescribed target coordinates, keeping
both the input representative and the candidate subspace fixed. -/
private theorem early_target_of_retained_boundary_top_at_degree
    (Y Z : (AdamsObject (coefficients := background.coefficients))) (g : Y.obj background.auxiliary ⟶ Z.obj background.auxiliary)
    (L d : ℕ) (hL : 1≤L) (hd : 0<d) (s t S V : ℤ)
    (hm : (t-s)-1=V-S) (hV : t+L+d=V)
    (y : Ambient background Y (s,t)) (v error : Ambient background Y (S,V))
    (P : Submodule ℤ (Ambient background Y (S,V)))
    (hP : permanentCycles background Y (S,V) ≤ P) (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map g).pageMap 2 (S,V) a=0 →
      a∈boundaries background Y (L+d) (S,V))
    (he : (background.classical.map g).pageMap 2 (S,V) error=0)
    (ξ : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) L))
    (hξ : ξ ≫ (background.quotients.tower _).rho 1 L hL=nativeFirstLabel Y s t y)
    (htop : homotopyRegrade hm (show t+L=V-d by omega)
        (biSuspensionHomEquiv (t-s) t L (background.nu.functor.obj (Y.obj background.auxiliary))
          (ξ ≫ XModLambdaN.proj _ L) ≫ XModLambdaN.incl _ (d+1)) =
      finiteTopLabel Y d hd S V (v+error)) :
    IsCycle background Y (L+d) (s,t) y ∧ IsCycle background Y (L+d) (S,V) v ∧
      DifferentialAt background Y (L+d+1) (s,t) (S,V) y v := by
  have hS : S=s+(L+d)+1 := by omega
  have hV' : V=t+(L+d) := by omega
  subst S
  subst hV'
  exact early_target_of_retained_boundary_top Y Z g L d hL hd s t y v error P hP hv hker he ξ hξ htop

/-- Changing the displayed source to its specified page class keeps the
constructed early-target differential and its exact output label. -/
private theorem early_target_of_page_source
    (Y : (AdamsObject (coefficients := background.coefficients))) (D r : ℤ) (p q : ℤ×ℤ) (hr : r≤D-1)
    (y y' : Ambient background Y p) (v : Ambient background Y q)
    (hd : DifferentialAt background Y D p q y v)
    (hy : y'-y∈boundaries background Y r p) :
    IsCycle background Y (D-1) p y' ∧ IsCycle background Y (D-1) q v ∧
      DifferentialAt background Y D p q y' v := by
  have hd' := differential_of_earlier_boundaries Y D r (D-1) p q y y' v v hd hr le_rfl hy
    (by rw [sub_self]; exact (boundaries background Y (D-1) q).zero_mem)
  exact ⟨(cycles_of_differential Y _ _ _ _ _ hd').1,
    (cycles_of_differential Y _ _ _ _ _ hd').2,hd'⟩

/-- Replace the original differential target by the actual divided source
label, then correct the positive image of that same chosen lift by the
produced early boundary. The full source for middle elimination is the
actual positive adjusted boundary of the returned lift. -/
private theorem early_positive_corrected_source
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (L : ℕ) (hL : 2≤L) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u u' : Ambient background T.X (s+L+1,t+L))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hu : u'-u∈boundaries background T.X 2 (s+L+1,t+L))
    (aHat : BiHom (((t+L)-(s+L+1))+1) (((t+L)+1)-1)
      (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) 1))
    (W : BiHom ((t+L)-(s+L+1)) ((t+L)+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (hW : W=homotopyRegrade (show (((t+L)-(s+L+1))+1)-1=(t+L)-(s+L+1) by omega)
        (show (((t+L)+1)-1)+1=(t+L)+1 by omega)
        (biSuspensionHomEquiv (((t+L)-(s+L+1))+1) (((t+L)+1)-1) 1
          (background.nu.functor.obj (T.Y.obj background.auxiliary)) (aHat ≫ XModLambdaN.proj _ 1))) :
    ∃ ζ : BiHom (t-s) t
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) L),
      ζ ≫ (background.quotients.tower _).rho 1 L (by omega)=nativeFirstLabel T.X s t x ∧
      positiveAdjustedBoundary T.X L s t ζ ≫ XModLambdaN.incl _ 1=
        nativeFirstLabel T.X (s+L+1) (t+L) u' ∧
      ∃ ξ : BiHom (t-s) (t+1)
          (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) L),
        homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl
            (ξ ≫ (background.quotients.tower _).rho 1 L (by omega)) =
          nativeFirstLabel T.Y (s+1) (t+1)
            (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
        homotopyRegrade (show (t-s)-1=(t+L)-(s+L+1) by omega)
            (show (t+1)+L=(t+L)+1 by omega)
            (biSuspensionHomEquiv (t-s) (t+1) L
              (background.nu.functor.obj (T.Y.obj background.auxiliary)) (ξ ≫ XModLambdaN.proj _ L)) =
          (verticalTranslate _ 1 ((t+L)-(s+L+1)) (t+L)
            (positiveAdjustedBoundary T.X L s t ζ) ≫ lastLayerNormalizedMap T hf)-W := by
  have hd' := differential_of_earlier_boundaries T.X (L+1) 2 2
    (s,t) (s+L+1,t+L) x x u u' ⟨by omega,hdx⟩ (by omega) (by omega)
    (by rw [sub_self]; exact (boundaries background T.X 2 (s,t)).zero_mem) hu
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L (by omega) s t x u').mp hd'.2
  refine ⟨ζ,hζ,(positive_adjusted_boundary_first T.X L s t ζ).trans hU,?_⟩
  let a₀ := homotopyRegrade (show ((t+L)-(s+L+1))+1=t-s by omega)
    (show ((t+L)+1)-1=(t+1)+L-1 by omega) aHat
  obtain ⟨ξ,hξ,hξb⟩ := positive_source_correction_of_earlier_boundary T hf L 1 (by decide)
    (by omega) s t x ζ hζ a₀
  refine ⟨ξ,hξ,?_⟩
  have haW : homotopyRegrade (show (t-s)-1=(t+L)-(s+L+1) by omega)
      (show (((t+1)+L-1)+1)=(t+L)+1 by omega)
      (biSuspensionHomEquiv (t-s) ((t+1)+L-1) 1
        (background.nu.functor.obj (T.Y.obj background.auxiliary)) (a₀ ≫ XModLambdaN.proj _ 1)) = W := by
    dsimp only [a₀]
    rw [←regrade_comp,early_bi_susp_regrade,normalized_homotopy_regrade_trans]
    exact hW.symm
  erw [haW] at hξb
  exact hξb


/-- The target early-boundary differential criterion in the positive-first-arrow
branch, with the entire original restricted middle subspaces and candidate kernel. Here the
original source page is L+1, the early root page is d+2, and the output
page is L+d+1. Every finite representative
and the early boundary correction are constructed from the displayed E₂
conditions. -/
private theorem differential_of_early_boundary_positive
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L d : ℕ) (hL : 2≤L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y (s+L,t+L))
    (v : Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hd₂ : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s+L,t+L) ((s+L)+1+1,(t+L)+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((d+1)+1) (s+L,t+L) ((s+L)+(d+1)+1,(t+L)+(d+1))
      ((background.classical.map T.g).pageMap 2 (s+L,t+L) c)
      ((background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) v))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X 2 (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1))))
    (hP : permanentCycles background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1))) :
    IsCycle background T.Y (L+d) (s+1,t+1)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) ∧
    IsCycle background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L)+(d+1)+1,(t+L)+(d+1))
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨cA,u',aHat,W,hcA,hu',hW,_,hcAi⟩ := early_positive_compatible_finite_lift
    T he hT hf hg hh (d+1) (by omega) (s+L) (t+L) c u v hdz hH hd₂
  obtain ⟨ζ,hζ,hU,ξ,hξ,hξb⟩ := early_positive_corrected_source T hf L hL s t x u u' hdx hu' aHat W hW
  obtain ⟨e,error,herror,htop⟩ := early_positive_selective_top_at_degree T he hT hf hg hh
    d (((d+1)+1)-1) hd (by omega) (s+L+1) (t+L)
    ((s+L)+(d+1)+1) ((t+L)+(d+1)) (by omega) (by omega) u' v
    Pm hPm hmid (positiveAdjustedBoundary T.X L s t ζ) hU cA hcA W hcAi
  have heG : (background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) error=0 := by
    have hgF := (KIP126.Literature.Standard.E2Exactness.e2ExactAtY
      T hf hg hh ((s+L+1)+d) ((t+L)+d)
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+d) ((t+L)+d) e)).mpr ⟨e,rfl⟩
    have transport (p p' : ℤ×ℤ) (hp : p=p')
        (a : Ambient background T.Y p) (b : Ambient background T.Y p') (hab : HEq a b)
        (hb : (background.classical.map T.g).pageMap 2 p' b=0) :
        (background.classical.map T.g).pageMap 2 p a=0 := by
      subst p'
      simpa only [eq_of_heq hab] using hb
    exact transport _ _ (by ext <;> dsimp <;> omega) _ _ herror hgF
  let ξY := homotopyRegrade (show t-s=(t+1)-(s+1) by omega) rfl ξ
  have hξY : ξY ≫ (background.quotients.tower _).rho 1 L (by omega)=
      nativeFirstLabel T.Y (s+1) (t+1)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) := by
    simpa only [ξY,←regrade_comp] using hξ
  have hfinalTop : homotopyRegrade
      (show ((t+1)-(s+1))-1=((t+L)+(d+1))-((s+L)+(d+1)+1) by omega)
      (show (t+1)+L=((t+L)+(d+1))-d by omega)
      (biSuspensionHomEquiv ((t+1)-(s+1)) (t+1) L
        (background.nu.functor.obj (T.Y.obj background.auxiliary)) (ξY ≫ XModLambdaN.proj _ L) ≫
          XModLambdaN.incl _ (d+1)) =
      finiteTopLabel T.Y d hd ((s+L)+(d+1)+1) ((t+L)+(d+1)) (v+error) := by
    have hb := congrArg (fun b => b ≫ XModLambdaN.incl
      (background.nu.functor.obj (T.Y.obj background.auxiliary)) (((d+1)+1)-1)) hξb
    have hb' := congrArg (homotopyRegrade
      (show (t+L)-(s+L+1)=((t+L)+(d+1))-((s+L)+(d+1)+1) by omega) rfl) hb
    rw [←regrade_comp,normalized_homotopy_regrade_trans] at hb'
    have ht := hb'.trans htop
    have ht' := congrArg (homotopyRegrade (rfl :
        ((t+L)+(d+1))-((s+L)+(d+1)+1)=((t+L)+(d+1))-((s+L)+(d+1)+1))
      (show (t+L)+1=((t+L)+(d+1))-d by omega)) ht
    convert ht' using 1 <;>
      simp only [ξY,←regrade_comp,early_bi_susp_regrade,normalized_homotopy_regrade_trans,
        finiteTopLabelAtWeight,top_target_regrade_self,Nat.add_sub_cancel]
    all_goals rfl
  exact early_target_of_retained_boundary_top_at_degree T.Y T.Z T.g L d (by omega) hd
    (s+1) (t+1) ((s+L)+(d+1)+1) ((t+L)+(d+1)) (by omega) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) v error P hP hv hker heG ξY hξY hfinalTop

/-- The complete displayed-page-source form of the target early-boundary
differential criterion for α=1.
The equation F_r[x]=[y] is expressed by its exact E₂ representatives modulo
B_{<r}; both asserted output cycles are derived. -/
public theorem differential_of_early_boundary_positive_page_source
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (L d : ℕ) (hL : 2≤L) (hd : 0<d) (s t : ℤ)
    (x : Ambient background T.X (s,t))
    (y : Ambient background T.Y (s+1,t+1))
    (u : Ambient background T.X (s+L+1,t+L))
    (c : Ambient background T.Y (s+L,t+L))
    (v : Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (s,t) (s+L+1,t+L) x u)
    (hd₂ : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      2 (s+L,t+L) ((s+L)+1+1,(t+L)+1) c
      (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+L+1) (t+L) u))
    (hdz : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((d+1)+1) (s+L,t+L) ((s+L)+(d+1)+1,(t+L)+(d+1))
      ((background.classical.map T.g).pageMap 2 (s+L,t+L) c)
      ((background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) v))
    (hH : ∀ z : Ambient background T.Z (s+L+1,(t+L)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+L+1) (t+L) z ∈
        boundaries background T.X 2 (s+L+1,t+L))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((s+L+1)+j+1,(t+L)+j+1)))
    (hPm : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      permanentCycles background T.Y ((s+L+1)+j+1,(t+L)+j+1) ≤ Pm j)
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ a : Ambient background T.X ((s+L+1)+j,(t+L)+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf ((s+L+1)+j) ((t+L)+j) a ∈ Pm j →
        ∃ z : Ambient background T.Z ((s+L+1)+j,(t+L)+j+1),
          z ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((s+L+1)+j,(t+L)+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((s+L+1)+j) ((t+L)+j) z ∈
            boundaries background T.X ((j:ℤ)+1) ((s+L+1)+j,(t+L)+j))
    (P : Submodule ℤ (Ambient background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1))))
    (hP : permanentCycles background T.Y ((s+L)+(d+1)+1,(t+L)+(d+1)) ≤ P)
    (hv : v∈P)
    (hker : ∀ a∈P, (background.classical.map T.g).pageMap 2 ((s+L)+(d+1)+1,(t+L)+(d+1)) a=0 →
      a∈boundaries background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1)))
    (hy : y-KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x ∈
      boundaries background T.Y L (s+1,t+1)) :
    IsCycle background T.Y (L+d) (s+1,t+1) y ∧
    IsCycle background T.Y (L+d) ((s+L)+(d+1)+1,(t+L)+(d+1)) v ∧
    DifferentialAt background T.Y (L+d+1) (s+1,t+1) ((s+L)+(d+1)+1,(t+L)+(d+1))
      y v := by
  have hd' := differential_of_early_boundary_positive T he hf hg hh L d hL hd s t
    x u c v hdx hd₂ hdz hH Pm hPm hmid P hP hv hker
  have hh' := early_target_of_page_source T.Y (L+d+1) L (s+1,t+1)
    ((s+L)+(d+1)+1,(t+L)+(d+1)) (by omega)
    (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t x) y v hd'.2.2 hy
  simpa only [add_sub_cancel_right] using hh'

end
end KIP126.ProofTools.Internal.SyntheticCoverage
