module

public import KIP126.ProofTools.SyntheticCoverage.PositiveAffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.SourceAdjustedPermanencePositive
import all KIP126.ProofTools.SyntheticCoverage.NonStrictSource

/-! Positive normalized extension equations with permanent source corrections. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.FiniteLifting
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000


/-- Extension equations after higher permanent source corrections, including
zero source grades. The zero correction spaces preserve every prescribed source. -/
public theorem source_adjusted_affine_permanence_positive_f
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (C : ∀ p : Bidegree, Submodule ℤ (Ambient background T.X p))
    (hC : ∀ p, C p ≤ permanentCycles background T.X p)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r+1,t-s+r+1)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r+1,t-s+r+1) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf r (t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          ∃ u : Ambient background T.X (r,t-s+r), u ∈ C (r,t-s+r) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r)
              (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T r (t-s+r) zH-u))
    (x x' : Ambient background T.X (s,t))
    (hx : x ∈ permanentCycles background T.X (s,t))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (x'-x))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) (t+1) (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (_hk : 0<k) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d+1,t+d+1)) (P : Submodule ℤ (Ambient background T.Y (s+d+1,t+d+1)))
    (hP : permanentCycles background T.Y (s+d+1,t+d+1) ≤ P) (hv : v∈P)
    (hterminal : (positiveFirstOperationLinear T hf (s+d) (t+d)).range ⊓ P ≤
      finalBoundaries T.Y (s+d+1,t+d+1) ⊔ (C (s+d,t+d)).map (positiveFirstOperationLinear T hf (s+d) (t+d)))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega)=nativeFirstLabel T.X s t x')
    (hc : positiveFiniteImage T hf (d+1) (levelQuotientShiftIso T.X 1 (d+1)) (t-s) t c=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d+1)-(s+d+1)=t-s by omega) (show (t+d+1)-d=t+1 by omega)
          (finiteTopLabel T.Y d hd (s+d+1) (t+d+1) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1) v ∧
      (∃ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ ∧
        ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
          (eqToHom (congrArg (Sphere (C:=Spectrum))
            (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ ξ ≫ T.f)) ∧
      (∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ∃ η : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
          η ∈ (background.classicalTower.tower (T.X.obj background.auxiliary)).filtrationSubmodule (s+1) (t-s) ∧
          ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
            (eqToHom (congrArg (Sphere (C:=Spectrum))
              (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ (ξ-η) ≫ T.f)) ∧
      ((∀ r : ℤ, s+1≤r → r≤s+d → C (r,t-s+r)=⊥) →
        ∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
          ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
          ClassicalDetects (background.classicalConvergence T.Y) (s+d+1,t+d+1) v
            (eqToHom (congrArg (Sphere (C:=Spectrum))
              (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ ξ ≫ T.f)) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  let R := KIP126.Literature.Standard.realizationData
  obtain ⟨a₀,ha₀⟩ := permanent_native_source T.X s t x hx
  obtain ⟨a₁,ha₁,_⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  have hmid' : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf r (t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          ∃ u : Ambient background T.X (r,t-s+r), u ∈ permanentCycles background T.X (r,t-s+r) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r)
              (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T r (t-s+r) zH-u) := by
    intro r hr hrd z hz hzP
    obtain ⟨zH,hzH,u,hu,he⟩ := hmid r hr hrd z hz hzP
    exact ⟨zH,hzH,u,hC _ hu,he⟩
  have hterminal' : ∀ e : Ambient background T.X (s+d,t+d),
      positiveFirstOperationLinear T hf (s+d) (t+d) e ∈ P →
      ∃ u : Ambient background T.X (s+d,t+d), u ∈ permanentCycles background T.X (s+d,t+d) ∧
        IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+d+1,t+d+1)
          (positiveFirstOperationLinear T hf (s+d) (t+d) e-positiveFirstOperationLinear T hf (s+d) (t+d) u) := by
    intro e he
    obtain ⟨b,hb,z,hz,hbz⟩ := Submodule.mem_sup.mp (hterminal ⟨⟨e,rfl⟩,he⟩)
    obtain ⟨u,hu,rfl⟩ := Submodule.mem_map.mp hz
    refine ⟨u,hC _ hu,?_⟩
    change _ ∈ finalBoundaries T.Y (s+d+1,t+d+1)
    rw [←hbz,add_sub_cancel_right]
    exact hb
  obtain ⟨a₂,ha₂,hp,hdet₂⟩ := positive_f_source_adjusted_full_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid hmid' a₁ c W k hW v P hP hv hterminal' (ha₁.trans hfirst.symm) hc
  let ξ' : HomotopyGroup (t-s) (T.X.obj background.auxiliary) :=
    (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₂ ≫ (hcomp.nu T.X).target.hom
  have hξ' : ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ' := by
    have hx' := full_source_detects_first_label R hcomp T.X s t x' a₂ (ha₂.trans ha₁)
    exact (classical_detects_of_final_boundary_difference T.X (s,t) x' x ξ' hx' hxx).2
  refine ⟨hp,⟨ξ',hξ',?_⟩,?_,?_⟩
  · simpa only [ξ',Category.assoc] using hdet₂
  · intro ξ hξ
    refine ⟨ξ-ξ',classical_detects_difference T.X s t x ξ ξ' hξ hξ',?_⟩
    simpa only [sub_sub_cancel,ξ',Category.assoc] using hdet₂
  · intro hzero ξ hξ
    have hmid₀ : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf r (t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r)
            (z-KIP126.ProofTools.Standard.classicalTriangleHMapHom T r (t-s+r) zH) := by
      intro r hr hrd z hz hzP
      obtain ⟨zH,hzH,u,hu,he⟩ := hmid r hr hrd z hz hzP
      have hu₀ : u=0 := by simpa only [hzero r hr (le_of_lt hrd),Submodule.mem_bot] using hu
      refine ⟨zH,hzH,?_⟩
      simpa only [hu₀,sub_zero] using he
    have hCterminal : C (s+d,t+d)=⊥ := by
      have heq : (s+(d:ℤ),t-s+(s+(d:ℤ)))=(s+(d:ℤ),t+(d:ℤ)) := by
        congr 1
        omega
      exact heq ▸ hzero (s+d) (by omega) le_rfl
    have hterminal₀ : (positiveFirstOperationLinear T hf (s+d) (t+d)).range ⊓ P ≤
        finalBoundaries T.Y (s+d+1,t+d+1) := by
      simpa only [hCterminal,Submodule.map_bot,sup_bot_eq] using hterminal
    obtain ⟨a₃,ha₃,hreal₃⟩ := prescribed_native_source_nonstrict hcomp T.X s t x ξ hξ
    obtain ⟨a₄,ha₄,hreal₄⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₃ ha₃ hxx
    obtain ⟨_,hvdet⟩ := positive_f_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
      Pmid hPmid hmid₀ a₄ c W k hW v P hP hv hterminal₀ (ha₄.trans hfirst.symm) hc
    have hsource : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₄ ≫
        (hcomp.nu T.X).target.hom=ξ := by
      have h := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom) hreal₄
      simp only [Category.assoc] at h
      exact h.trans hreal₃
    have hresult := congrArg (fun z => eqToHom (congrArg (Sphere (C:=Spectrum))
      (show (t+d+1)-(s+d+1)=t-s by omega)) ≫ z ≫ T.f) hsource
    simp only [Category.assoc] at hresult
    exact hresult ▸ hvdet

end
end KIP126.ProofTools.Internal.SyntheticCoverage
end
