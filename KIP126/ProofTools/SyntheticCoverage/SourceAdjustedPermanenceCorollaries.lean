module

public import KIP126.ProofTools.SyntheticCoverage.AffinePermanence
import all KIP126.ProofTools.SyntheticCoverage.SourceAdjustedPermanence
import all KIP126.ProofTools.SyntheticCoverage.NonStrictSource

/-! Classical extension equations after corrections in higher source filtration.
The permanent correction spaces are indexed by all bidegrees; the finite
family in the statement is extended by zero away from its specified layers. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.FiniteLifting
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

private theorem ordinary_source_realization_image
    (R : RealizationCoordinates background) (hcomp : LambdaInversionAdamsComparison background R)
    (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (s t : ℤ) (a : BiHom (t-s) t (background.nu.functor.obj (X.obj background.auxiliary))) :
    (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a ≫ background.nu.functor.map f) ≫
        (hcomp.nu Y).target.hom =
      ((R.sphere (t-s) t).hom ≫ background.recovery.realization.map a ≫ (hcomp.nu X).target.hom) ≫ f := by
  rw [Functor.map_comp,hcomp.nu_target]
  have hn := background.recovery.nuRealizationIso.hom.naturality f
  dsimp only [Functor.comp_map,Functor.id_map] at hn
  simp only [Category.assoc]
  rw [hn,←hcomp.nu_target X]

/-- Higher-source correction and its zero-correction specialization in the positive-h normalization.
The extension equation is stated using one common classical representative, including zero grades. -/
public theorem source_adjusted_affine_permanence_positive_h
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (C : ∀ p : Bidegree, Submodule ℤ (Ambient background T.X p))
    (hC : ∀ p, C p ≤ permanentCycles background T.X p)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r,t-s+r)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r,t-s+r) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        (background.classical.map T.f).pageMap 2 (r,t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r-1,t-s+r),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r-1,t-s+r) ∧
          ∃ u : Ambient background T.X (r,t-s+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-s+r+1)
              (middleLabelRegrade (X := .shift 1 T.X)
                (show (r-1+1,t-s+r+1)=(r,t-s+r+1) by congr 1; omega)
                (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
                  (r-1) (t-s+r) zH)) (by simpa using u) ∧
            ∃ c : Ambient background T.X (r,t-s+r), c ∈ C (r,t-s+r) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u-c))
    (x x' : Ambient background T.X (s,t))
    (hx : x ∈ permanentCycles background T.X (s,t))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (x'-x))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (_hk : 0<k) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ∀ e : Ambient background T.X (s+d,t+d),
      (background.classical.map T.f).pageMap 2 (s+d,t+d) e ∈ P →
      ∃ r : Ambient background T.X (s+d,t+d), r ∈ C (s+d,t+d) ∧
        IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d)
          ((background.classical.map T.f).pageMap 2 (s+d,t+d) e-(background.classical.map T.f).pageMap 2 (s+d,t+d) r))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega)=nativeFirstLabel T.X s t x')
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      (∃ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ ∧
        ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
          (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f)) ∧
      (∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ∃ η : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
          η ∈ (background.classicalTower.tower (T.X.obj background.auxiliary)).filtrationSubmodule (s+1) (t-s) ∧
          ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
            (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ (ξ-η) ≫ T.f)) ∧
      ((∀ r : ℤ, s+1≤r → r≤s+d → C (r,t-s+r)=⊥) → ∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
          (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f)) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨a₀,ha₀⟩ := permanent_native_source T.X s t x hx
  obtain ⟨a₁,ha₁,_⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨a₂,ha₂,hp,hdet₂⟩ := positive_h_source_adjusted_full_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid (by
      intro r hr hr' z hz hzP
      obtain ⟨zH,hzH,u,hu,c,hc,hb⟩ := hmid r hr hr' z hz hzP
      exact ⟨zH,hzH,u,hu,c,hC _ hc,hb⟩)
    a₁ c W k hW v P hP hv (by
      intro e he
      obtain ⟨r,hr,hb⟩ := hterminal e he
      exact ⟨r,hC _ hr,hb⟩) (ha₁.trans hfirst.symm) hc
  let ξ' : HomotopyGroup (t-s) (T.X.obj background.auxiliary) :=
    (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₂ ≫ (hcomp.nu T.X).target.hom
  have hsource' : ClassicalDetects (background.classicalConvergence T.X) (s,t) x' ξ' :=
    full_source_detects_first_label R hcomp T.X s t x' a₂ (ha₂.trans ha₁)
  have hsource := (classical_detects_of_final_boundary_difference T.X (s,t) x' x ξ' hsource' hxx).2
  have himage := ordinary_source_realization_image R hcomp T.X T.Y T.f s t a₂
  have htarget : ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
      (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ ξ' ≫ T.f) := by
    simpa only [himage,ξ',Category.assoc] using hdet₂
  refine ⟨hp,⟨ξ',hsource,htarget⟩,?_,?_⟩
  · intro ξ hξ
    refine ⟨ξ-ξ',classical_detects_difference T.X s t x ξ ξ' hξ hsource,?_⟩
    simpa only [sub_sub_cancel] using htarget
  · intro hzero
    have hmid0 : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        (background.classical.map T.f).pageMap 2 (r,t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r-1,t-s+r),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r-1,t-s+r) ∧
          ∃ u : Ambient background T.X (r,t-s+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-s+r+1)
              (middleLabelRegrade (X := .shift 1 T.X)
                (show (r-1+1,t-s+r+1)=(r,t-s+r+1) by congr 1; omega)
                (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
                  (r-1) (t-s+r) zH)) (by simpa using u) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u) := by
      intro r hr hr' z hz hzP
      obtain ⟨zH,hzH,u,hu,c,hc,hb⟩ := hmid r hr hr' z hz hzP
      have hc0 : c=0 := by simpa only [hzero r hr (by omega),Submodule.mem_bot] using hc
      exact ⟨zH,hzH,u,hu,by simpa only [hc0,sub_zero] using hb⟩
    have hterminal0 : ((background.classical.map T.f).pageMap 2 (s+d,t+d)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+d,t+d) := by
      rintro y ⟨⟨e,rfl⟩,he⟩
      obtain ⟨r,hr,hb⟩ := hterminal e he
      have hCterm0 : C (s+d,t+d)=⊥ := by
        have hdegree : (s+(d:ℤ),t-s+(s+(d:ℤ)))=(s+(d:ℤ),t+(d:ℤ)) := by
          congr 1
          omega
        exact hdegree ▸ hzero (s+d) (by omega) (by omega)
      have hr0 : r=0 := by simpa only [hCterm0,Submodule.mem_bot] using hr
      apply (mem_finalBoundaries_iff T.Y (s+d,t+d) _).mpr
      simpa only [hr0,map_zero,sub_zero] using hb
    intro ξ hdet
    obtain ⟨a₀,ha₀,hreal₀⟩ := prescribed_native_source_nonstrict hcomp T.X s t x ξ hdet
    obtain ⟨a₁,ha₁,hreal₁⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
    obtain ⟨_,hvdet⟩ := positive_h_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
      Pmid hPmid hmid0 a₁ c W k hW v P hP hv hterminal0 (ha₁.trans hfirst.symm) hc
    have hsource : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₁ ≫
        (hcomp.nu T.X).target.hom=ξ := by
      have h := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom) hreal₁
      simp only [Category.assoc] at h
      exact h.trans hreal₀
    have himage : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map
        (a₁ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom=ξ ≫ T.f := by
      rw [Functor.map_comp,hcomp.nu_target]
      have hn := background.recovery.nuRealizationIso.hom.naturality T.f
      dsimp only [Functor.comp_map,Functor.id_map] at hn
      simp only [Category.assoc]
      rw [hn,←hcomp.nu_target T.X]
      simpa only [Category.assoc] using congrArg (fun z => z ≫ T.f) hsource
    have himage' := congrArg (fun z => eqToHom (congrArg (Sphere (C := Spectrum))
      (show (t+d)-(s+d)=t-s by omega)) ≫ z) himage
    have heq : eqToHom (congrArg (Sphere (C := Spectrum))
        (show (t+d)-(s+d)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a₁ ≫ background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom =
        eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f := by
      simpa only [Category.assoc] using himage'
    exact heq ▸ hvdet


/-- Higher-source correction and its zero-correction specialization in the positive-g normalization.
The extension equation is stated using one common classical representative, including zero grades. -/
public theorem source_adjusted_affine_permanence_positive_g
    (T : TriangleData background.auxiliary)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (d : ℕ) (hd : 0<d) (s t : ℤ)
    (C : ∀ p : Bidegree, Submodule ℤ (Ambient background T.X p))
    (hC : ∀ p, C p ≤ permanentCycles background T.X p)
    (Pmid : ∀ r : ℤ, Submodule ℤ (Ambient background T.Y (r,t-s+r)))
    (hPmid : ∀ r : ℤ, s+1≤r → r<s+d → permanentCycles background T.Y (r,t-s+r) ≤ Pmid r)
    (hmid : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        (background.classical.map T.f).pageMap 2 (r,t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          ∃ u : Ambient background T.X (r,t-s+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-s+r+1)
              ((background.classical.map T.h).pageMap 2 (r,t-s+r+1) zH) (by simpa using u) ∧
            ∃ c : Ambient background T.X (r,t-s+r), c ∈ C (r,t-s+r) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u-c))
    (x x' : Ambient background T.X (s,t))
    (hx : x ∈ permanentCycles background T.X (s,t))
    (hxx : IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (s,t) (x'-x))
    (c : BiHom (t-s) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (d+1)))
    (W : BiHom (t-s) t (background.nu.functor.obj (T.Y.obj background.auxiliary)))
    (k : ℕ) (_hk : 0<k) (hW : lambdaMultiply k W=0)
    (v : Ambient background T.Y (s+d,t+d)) (P : Submodule ℤ (Ambient background T.Y (s+d,t+d)))
    (hP : permanentCycles background T.Y (s+d,t+d) ≤ P) (hv : v ∈ P)
    (hterminal : ∀ e : Ambient background T.X (s+d,t+d),
      (background.classical.map T.f).pageMap 2 (s+d,t+d) e ∈ P →
      ∃ r : Ambient background T.X (s+d,t+d), r ∈ C (s+d,t+d) ∧
        IsFinalBoundary (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d)
          ((background.classical.map T.f).pageMap 2 (s+d,t+d) e-(background.classical.map T.f).pageMap 2 (s+d,t+d) r))
    (hfirst : c ≫ (background.quotients.tower _).rho 1 (d+1) (by omega)=nativeFirstLabel T.X s t x')
    (hc : c ≫ XModLambdaN.map (background.nu.functor.map T.f) (d+1)=
      W ≫ XModLambdaN.incl _ (d+1)+homotopyRegrade
        (show (t+d)-(s+d)=t-s by omega) (show (t+d)-d=t by omega)
          (finiteTopLabel T.Y d hd (s+d) (t+d) v)) :
    IsPermanentCycle (background.classical.obj (T.Y.obj background.auxiliary)) (s+d,t+d) v ∧
      (∃ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ ∧
        ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
          (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f)) ∧
      (∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ∃ η : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
          η ∈ (background.classicalTower.tower (T.X.obj background.auxiliary)).filtrationSubmodule (s+1) (t-s) ∧
          ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
            (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ (ξ-η) ≫ T.f)) ∧
      ((∀ r : ℤ, s+1≤r → r≤s+d → C (r,t-s+r)=⊥) → ∀ ξ : HomotopyGroup (t-s) (T.X.obj background.auxiliary),
        ClassicalDetects (background.classicalConvergence T.X) (s,t) x ξ →
        ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
          (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f)) := by
  let hcomp := KIP126.Literature.Standard.lambdaInversionAdamsComparison
  let R := KIP126.Literature.Standard.realizationData
  have hT : NormalizedTriangleCompatible background T (by simp [hf,hg,hh]) :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨a₀,ha₀⟩ := permanent_native_source T.X s t x hx
  obtain ⟨a₁,ha₁,_⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
  obtain ⟨a₂,ha₂,hp,hdet₂⟩ := positive_g_source_adjusted_full_permanence R hcomp T hf hg hh hT d hd s t
    Pmid hPmid (by
      intro r hr hr' z hz hzP
      obtain ⟨zH,hzH,u,hu,c,hc,hb⟩ := hmid r hr hr' z hz hzP
      exact ⟨zH,hzH,u,hu,c,hC _ hc,hb⟩)
    a₁ c W k hW v P hP hv (by
      intro e he
      obtain ⟨r,hr,hb⟩ := hterminal e he
      exact ⟨r,hC _ hr,hb⟩) (ha₁.trans hfirst.symm) hc
  let ξ' : HomotopyGroup (t-s) (T.X.obj background.auxiliary) :=
    (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₂ ≫ (hcomp.nu T.X).target.hom
  have hsource' : ClassicalDetects (background.classicalConvergence T.X) (s,t) x' ξ' :=
    full_source_detects_first_label R hcomp T.X s t x' a₂ (ha₂.trans ha₁)
  have hsource := (classical_detects_of_final_boundary_difference T.X (s,t) x' x ξ' hsource' hxx).2
  have himage := ordinary_source_realization_image R hcomp T.X T.Y T.f s t a₂
  have htarget : ClassicalDetects (background.classicalConvergence T.Y) (s+d,t+d) v
      (eqToHom (congrArg (Sphere (C := Spectrum)) (show (t+d)-(s+d)=t-s by omega)) ≫ ξ' ≫ T.f) := by
    simpa only [himage,ξ',Category.assoc] using hdet₂
  refine ⟨hp,⟨ξ',hsource,htarget⟩,?_,?_⟩
  · intro ξ hξ
    refine ⟨ξ-ξ',classical_detects_difference T.X s t x ξ ξ' hξ hsource,?_⟩
    simpa only [sub_sub_cancel] using htarget
  · intro hzero
    have hmid0 : ∀ r : ℤ, s+1≤r → r<s+d →
      ∀ z : Ambient background T.X (r,t-s+r), z ∈ cycles background T.X (d+1-(r-s).toNat:ℕ) (r,t-s+r) →
        (background.classical.map T.f).pageMap 2 (r,t-s+r) z ∈ Pmid r →
        ∃ zH : Ambient background T.Z (r,t-s+r+1),
          zH ∈ cycles background T.Z (d+1-(r-s).toNat:ℕ) (r,t-s+r+1) ∧
          ∃ u : Ambient background T.X (r,t-s+r),
            (background.classicalSuspension T.X).DesuspendsClass r (t-s+r+1)
              ((background.classical.map T.h).pageMap 2 (r,t-s+r+1) zH) (by simpa using u) ∧
            IsFinalBoundary (background.classical.obj (T.X.obj background.auxiliary)) (r,t-s+r) (z-u) := by
      intro r hr hr' z hz hzP
      obtain ⟨zH,hzH,u,hu,c,hc,hb⟩ := hmid r hr hr' z hz hzP
      have hc0 : c=0 := by simpa only [hzero r hr (by omega),Submodule.mem_bot] using hc
      exact ⟨zH,hzH,u,hu,by simpa only [hc0,sub_zero] using hb⟩
    have hterminal0 : ((background.classical.map T.f).pageMap 2 (s+d,t+d)).hom.range ⊓ P ≤
      finalBoundaries T.Y (s+d,t+d) := by
      rintro y ⟨⟨e,rfl⟩,he⟩
      obtain ⟨r,hr,hb⟩ := hterminal e he
      have hCterm0 : C (s+d,t+d)=⊥ := by
        have hdegree : (s+(d:ℤ),t-s+(s+(d:ℤ)))=(s+(d:ℤ),t+(d:ℤ)) := by
          congr 1
          omega
        exact hdegree ▸ hzero (s+d) (by omega) (by omega)
      have hr0 : r=0 := by simpa only [hCterm0,Submodule.mem_bot] using hr
      apply (mem_finalBoundaries_iff T.Y (s+d,t+d) _).mpr
      simpa only [hr0,map_zero,sub_zero] using hb
    intro ξ hdet
    obtain ⟨a₀,ha₀,hreal₀⟩ := prescribed_native_source_nonstrict hcomp T.X s t x ξ hdet
    obtain ⟨a₁,ha₁,hreal₁⟩ := full_source_with_boundary_changed_first_label R T.X s t x x' a₀ ha₀ hxx
    obtain ⟨_,hvdet⟩ := positive_g_affine_full_source_permanence R hcomp T hf hg hh hT d hd s t
      Pmid hPmid hmid0 a₁ c W k hW v P hP hv hterminal0 (ha₁.trans hfirst.symm) hc
    have hsource : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map a₁ ≫
        (hcomp.nu T.X).target.hom=ξ := by
      have h := congrArg (fun z => z ≫ (hcomp.nu T.X).target.hom) hreal₁
      simp only [Category.assoc] at h
      exact h.trans hreal₀
    have himage : (R.sphere (t-s) t).hom ≫ background.recovery.realization.map
        (a₁ ≫ background.nu.functor.map T.f) ≫ (hcomp.nu T.Y).target.hom=ξ ≫ T.f := by
      rw [Functor.map_comp,hcomp.nu_target]
      have hn := background.recovery.nuRealizationIso.hom.naturality T.f
      dsimp only [Functor.comp_map,Functor.id_map] at hn
      simp only [Category.assoc]
      rw [hn,←hcomp.nu_target T.X]
      simpa only [Category.assoc] using congrArg (fun z => z ≫ T.f) hsource
    have himage' := congrArg (fun z => eqToHom (congrArg (Sphere (C := Spectrum))
      (show (t+d)-(s+d)=t-s by omega)) ≫ z) himage
    have heq : eqToHom (congrArg (Sphere (C := Spectrum))
        (show (t+d)-(s+d)=t-s by omega)) ≫
          (R.sphere (t-s) t).hom ≫ background.recovery.realization.map (a₁ ≫ background.nu.functor.map T.f) ≫
            (hcomp.nu T.Y).target.hom =
        eqToHom (congrArg (Sphere (C := Spectrum))
          (show (t+d)-(s+d)=t-s by omega)) ≫ ξ ≫ T.f := by
      simpa only [Category.assoc] using himage'
    exact heq ▸ hvdet

end
end KIP126.ProofTools.Internal.SyntheticCoverage
end
