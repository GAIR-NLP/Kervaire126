module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyTransfer
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyRootComparison
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryPositiveGRootComparison

/-! Ordinary early-boundary endpoints for arbitrary admissible Adams objects.
The original early differential constructs the common finite representative
using the specified normalized triangle and finite-quotient comparison.
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

private theorem ordinary_early_second_zero_first_label
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hg : normalizedExponent background.classicalTower T.g=0) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) :
    nativeFirstLabel T.Y s t c≫XModLambdaN.map (normalizedTriangle background T he).mor₂ 1=
      nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c)≫
        XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 := by
  apply (cancel_mono ((background.quotients.functoriality.functor 1).mapIso (normalizedThirdZeroIso T he hg)).hom).mp
  change _≫XModLambdaN.map (normalizedThirdZeroIso T he hg).hom 1=_≫XModLambdaN.map (normalizedThirdZeroIso T he hg).hom 1
  rw [Category.assoc,←background.quotients.functoriality.map_comp,normalized_second_arrow_zero,
    native_first_label_natural]
  simp only [Category.assoc,←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
    background.quotients.functoriality.map_id,Category.comp_id]

private theorem ordinary_early_long_top_division
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (S V A B : ℤ)
    (hA : A=S+(q-i:ℕ)) (hB : B=V+(q-i:ℕ))
    (u : Ambient background X (S,V)) (v : Ambient background Y (A,B))
    (a : BiHom (V-S) (V-i) (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) (q+1)))
    (hsource : a≫(background.quotients.tower _).rho (i+1) (q+1) (by omega)=finiteTopLabel X i hi S V u)
    (himage : a≫XModLambdaN.map (background.nu.functor.map f) (q+1)=
      homotopyRegrade (show B-A=V-S by omega) (show B-q=V-i by omega)
        (finiteTopLabel Y q (by omega) A B v)) :
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) ((q+1)-i)),
    ∃ u' : Ambient background X (S,V),
    ∃ aHat : BiHom ((V-S)+1) (V-i) (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) V (background.nu.functor.obj (Y.obj background.auxiliary)),
      b≫(background.quotients.tower _).rho 1 ((q+1)-i) (by omega)=nativeFirstLabel X S V u' ∧
      u'-u∈boundaries background X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega) (show (V-i)+i=V by omega)
        (biSuspensionHomEquiv ((V-S)+1) (V-i) i (background.nu.functor.obj (Y.obj background.auxiliary))
          (aHat≫XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      b≫XModLambdaN.map (background.nu.functor.map f) ((q+1)-i)=W≫XModLambdaN.incl _ ((q+1)-i)+
        homotopyRegrade (show B-A=V-S by omega) rfl
          (finiteTopLabelAtWeight Y (q-i) (by omega) ((q+1)-i) (by omega) A B V (by omega) v) := by
  let vshort := homotopyRegrade (show B-A=V-S by omega) rfl
    (finiteTopLabelAtWeight Y (q-i) (by omega) ((q+1)-i) (by omega) A B V (by omega) v)
  have hcoeff : a≫XModLambdaN.map (background.nu.functor.map f) (q+1)=
      finiteCoefficientShiftClass _ (q+1) i (by omega) (V-S) V vshort := by
    rw [himage]
    dsimp only [vshort]
    rw [coefficient_shift_regrade,higher_coefficient_top]
    · rfl
    · exact hiq
  obtain ⟨b,u',aHat,W,_,hb,hu,hW,ht,hbimage⟩ := ordinary_early_top_division_and_torsion
    X Y f (q+1) i hi (by omega) S V u a hsource vshort hcoeff
  exact ⟨b,u',aHat,W,hb,hu,hW,ht,hbimage⟩

private theorem ordinary_compatible_source_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i+1,t+i))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c ((background.classical.map T.f).pageMap 2 (s+i+1,t+i) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (s+q+1,t+q) v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈ boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+(i+1)-1,t+(i+1)-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+(i+1)-1) (t+(i+1)-1) z ∈
          boundaries background (.shift 1 T.X) (i+1) ((s+(i+1)-1)+1,(t+(i+1)-1)+1))
 :
    let S := s+i+1
    let V := t+i
    let K := (q+1)-i
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K),
    ∃ u' : Ambient background T.X (S,V),
    ∃ aHat : BiHom ((V-S)+1) (V-i) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) V (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b≫(background.quotients.tower _).rho 1 K (by dsimp [K];omega)=nativeFirstLabel T.X S V u' ∧
      u'-u∈boundaries background T.X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega) (show (V-i)+i=V by omega)
        (biSuspensionHomEquiv ((V-S)+1) (V-i) i (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (aHat≫XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      b≫XModLambdaN.map (background.nu.functor.map T.f) K=W≫XModLambdaN.incl _ K+
        homotopyRegrade (show (t+q)-(s+q+1)=V-S by dsimp [S,V];omega) rfl
          (finiteTopLabelAtWeight T.Y (q-i) (by omega) K (by dsimp [K];omega)
            (s+q+1) (t+q) V (by dsimp [V];omega) v) := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨ei,hei,R,hRf,hRt⟩ := ordinary_first_and_top_of_differential T he hf i hi s t c u hearly
  rw [ordinary_early_second_zero_first_label T he hg s t c] at hRf
  obtain ⟨a,ha,haf⟩ := ordinary_long_source_positive_h_of_root T he hT hf hg hh i q hi hiq s t
    ((background.classical.map T.g).pageMap 2 (s,t) c) u v hdroot hR hH ei hei R hRf hRt
  let a' := homotopyRegrade (show (t-s)-1=(t+i)-(s+i+1) by omega)
    (show t=(t+i)-i by omega) a
  have ha' : a'≫(background.quotients.tower _).rho (i+1) (q+1) (by omega)=
      finiteTopLabel T.X i hi (s+i+1) (t+i) u := by
    simp only [a',←regrade_comp,ha,ordinaryEarlyTop,normalized_homotopy_regrade_trans,top_target_regrade_self]
  have haf' : a'≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)=
      homotopyRegrade (show (t+q)-(s+q+1)=(t+i)-(s+i+1) by omega)
        (show (t+q)-q=(t+i)-i by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
    simp only [a',←regrade_comp,haf,normalized_homotopy_regrade_trans]
  exact ordinary_early_long_top_division T.X T.Y T.f q i hi hiq (s+i+1) (t+i)
    (s+q+1) (t+q) (by omega) (by omega) u v a' ha' haf'


private theorem ordinary_compatible_source_third_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t B W A V : ℤ) (K d : ℕ)
    (hB : B=s+i) (hW : W=t+i) (hA : A=s+q+1) (hV : V=t+q)
    (hK : K=(q+1)-i) (hd : d=q-i)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (B+1,W))
    (v : Ambient background T.Y (A,V))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (B+1,W) c ((background.classical.map T.f).pageMap 2 (B+1,W) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s,t) (A,V) ((background.classical.map T.g).pageMap 2 (s,t) c)
      ((background.classical.map T.g).pageMap 2 (A,V) v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,t-s+p), z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) →
      ∃ y : Ambient background T.Y (p,t-s+p), y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p,t-s+p), k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p,t-s+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,t-s+p) y-k ∈ boundaries background T.Z ((p-s).toNat+1) (p,t-s+p))
    (hH : ∀ z : Ambient background T.Z (s+(i+1)-1,t+(i+1)-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        (s+(i+1)-1) (t+(i+1)-1) z ∈
          boundaries background (.shift 1 T.X) (i+1) ((s+(i+1)-1)+1,(t+(i+1)-1)+1))
 :
    let S := B+1
    ∃ b : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K),
    ∃ u' : Ambient background T.X (S,W),
    ∃ aHat : BiHom ((W-S)+1) (W-i) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ D : BiHom (W-S) W (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b≫(background.quotients.tower _).rho 1 K (by omega)=nativeFirstLabel T.X S W u' ∧
      u'-u∈boundaries background T.X (i+1) (S,W) ∧
      D=homotopyRegrade (show ((W-S)+1)-1=W-S by omega) (show (W-i)+i=W by omega)
        (biSuspensionHomEquiv ((W-S)+1) (W-i) i (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (aHat≫XModLambdaN.proj _ i)) ∧
      lambdaMultiply i D=0 ∧
      b≫XModLambdaN.map (background.nu.functor.map T.f) K=D≫XModLambdaN.incl _ K+
        homotopyRegrade (show V-A=W-S by dsimp [S];omega) rfl
          (finiteTopLabelAtWeight T.Y d (by omega) K (by omega)
            A V W (by omega) v) := by
  subst B
  subst W
  subst A
  subst V
  subst K
  subst d
  exact ordinary_compatible_source_third T he hf hg hh i q hi hiq s t c u v hearly hdroot hR hH


/-- Original source-side higher early-boundary conclusion. Both original
differentials produce the compatible source internally. -/
public theorem ordinary_early_source_third
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (i d N : ℕ) (hi : 0 < i) (hd : 0 < d) (hKN : d+1≤N) (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (y : Ambient background T.Y (B+d+1,W+d))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (c : Ambient background T.Y (B-i,W-i))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) ((B-i),(W-i)) (B+1,W) c ((background.classical.map T.f).pageMap 2 (B+1,W) x))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) ((B-i),(W-i)) ((B+d+1),(W+d)) ((background.classical.map T.g).pageMap 2 ((B-i),(W-i)) c)
      ((background.classical.map T.g).pageMap 2 ((B+d+1),(W+d)) y))
    (hR : ∀ p : ℤ, (B-i)+1≤p → p<(B-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p,(W-i)-(B-i)+p), z ∈ cycles background T.Z ((i+1)-(p-(B-i)).toNat:ℕ) (p,(W-i)-(B-i)+p) →
      ∃ y : Ambient background T.Y (p,(W-i)-(B-i)+p), y ∈ cycles background T.Y ((i+1)-(p-(B-i)).toNat:ℕ) (p,(W-i)-(B-i)+p) ∧
      ∃ k : Ambient background T.Z (p,(W-i)-(B-i)+p), k ∈ cycles background T.Z ((i+d)+1-(p-(B-i)).toNat:ℕ) (p,(W-i)-(B-i)+p) ∧
        z-(background.classical.map T.g).pageMap 2 (p,(W-i)-(B-i)+p) y-k ∈ boundaries background T.Z ((p-(B-i)).toNat+1) (p,(W-i)-(B-i)+p))
    (hH : ∀ z : Ambient background T.Z ((B-i)+(i+1)-1,(W-i)+(i+1)-1),
      positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
        ((B-i)+(i+1)-1) ((W-i)+(i+1)-1) z ∈
          boundaries background (.shift 1 T.X) (i+1) (((B-i)+(i+1)-1)+1,((W-i)+(i+1)-1)+1))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (d+1)-1 →
      ∀ a : Ambient background T.X ((B+1)+j-1+1,W+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) ((B+1)+j-1+1,W+j) →
        ∃ z' : Ambient background T.Z ((B+1)+j-1,W+j),
          z' ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) ((B+1)+j-1,W+j) ∧
        ∃ u' : Ambient background T.X ((B+1)+j-1+1,W+j),
          (background.classicalSuspension T.X).DesuspendsClass ((B+1)+j-1+1) (W+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((B+1)+j-1) (W+j) z') (by simpa only [add_sub_cancel_right] using u') ∧
          a-u' ∈ boundaries background T.X ((j:ℤ)+1) ((B+1)+j-1+1,W+j))
    (himage : ∀ e : Ambient background T.X (B+d+1,W+d),
      (background.classical.map T.f).pageMap 2 (B+d+1,W+d) e∈cycles background T.Y ((N-d:ℕ)+1) (B+d+1,W+d)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-d:ℕ) (B+d+1,W+d) y ∧
      IsCycle background T.Y (N-d:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-d:ℕ)+1) (B+d+1,W+d) ((B+1)+N+1,W+N) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨a,x',aHat,D,ha,hxx,_,_,himageA⟩ :=
    ordinary_compatible_source_third_at T he hf hg hh
      i (i+d) hi (by omega) (B-i) (W-i) B W (B+d+1) (W+d) (d+1) d
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      c x y hearly hdroot hR hH
  have himg : a≫XModLambdaN.map (background.nu.functor.map T.f) (d+1)-D≫XModLambdaN.incl _ (d+1)=
      homotopyRegrade (show (W+d)-(B+d+1)=W-(B+1) by omega)
        (show (W+d)-d=W by omega) (finiteTopLabel T.Y d hd (B+d+1) (W+d) y) := by
    rw [himageA,add_sub_cancel_left]
    simp only [finiteTopLabelAtWeight,normalized_homotopy_regrade_trans]
  exact ordinary_early_source_of_compatible_source_third T he hT hf hg hh
    d N hd hKN B W (i+1) x x' u y hdx hxx hmid a ha D himg himage


/-- Original target-side higher early-boundary conclusion, retaining the
whole terminal kernel and the displayed page source. -/
public theorem ordinary_early_target_third
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
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j →
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
  exact ordinary_early_target_of_compatible_source_third T he hT hf hg hh
    N i d hi hiN hd s t x y hy u u' hdx hu v Pm hPm hmid a ha aHat D hD himg P hP hv hker

private theorem ordinary_early_second_positive_first_label
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hg : normalizedExponent background.classicalTower T.g=1) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) :
    nativeFirstLabel T.Y s t c≫XModLambdaN.map (normalizedTriangle background T he).mor₂ 1=
      homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1)
            (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) s t c)))≫
        (levelQuotientShiftIso T.Z (-1) 1).inv≫
          XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1 := by
  have hm : (normalizedTriangle background T he).mor₂=
      negativeLift 1 (normalizedSecondPositiveMap T hg)≫(normalizedThirdNegativeIso T he hg).inv := by
    rw [←normalized_second_arrow_positive T he hg,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [hm,background.quotients.functoriality.map_comp,←Category.assoc,
    positive_operation_negative_lift_label,Category.assoc]

private theorem ordinary_compatible_source_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i+1,t+i))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c ((background.classical.map T.f).pageMap 2 (s+i+1,t+i) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) s t c)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+q+1) (t+q) v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p+1,(t-s+p)+1),
        z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) →
      ∃ y : Ambient background T.Y (p,t-s+p),
        y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p+1,(t-s+p)+1),
        k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p (t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p+1,(t-s+p)+1))
    (hH : ∀ z : Ambient background T.Z (s+(i+1),(t+(i+1)-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+(i+1)) (t+(i+1)-1) z ∈
        boundaries background T.X (i+1) (s+(i+1),t+(i+1)-1))
 :
    let S := s+i+1
    let V := t+i
    let K := (q+1)-i
    ∃ b : BiHom (V-S) V (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K),
    ∃ u' : Ambient background T.X (S,V),
    ∃ aHat : BiHom ((V-S)+1) (V-i) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ W : BiHom (V-S) V (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b≫(background.quotients.tower _).rho 1 K (by dsimp [K];omega)=nativeFirstLabel T.X S V u' ∧
      u'-u∈boundaries background T.X (i+1) (S,V) ∧
      W=homotopyRegrade (show ((V-S)+1)-1=V-S by omega) (show (V-i)+i=V by omega)
        (biSuspensionHomEquiv ((V-S)+1) (V-i) i (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (aHat≫XModLambdaN.proj _ i)) ∧
      lambdaMultiply i W=0 ∧
      b≫XModLambdaN.map (background.nu.functor.map T.f) K=W≫XModLambdaN.incl _ K+
        homotopyRegrade (show (t+q)-(s+q+1)=V-S by dsimp [S,V];omega) rfl
          (finiteTopLabelAtWeight T.Y (q-i) (by omega) K (by dsimp [K];omega)
            (s+q+1) (t+q) V (by dsimp [V];omega) v) := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨ei,hei,R,hRf,hRt⟩ := ordinary_first_and_top_of_differential T he hf i hi s t c u hearly
  rw [ordinary_early_second_positive_first_label T he hg s t c] at hRf
  obtain ⟨a,ha,haf⟩ := ordinary_long_source_positive_g_of_root T he hT hf hg hh i q hi hiq s t
    (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) s t c) u v hdroot hR hH ei hei R hRf hRt
  let a' := homotopyRegrade (show (t-s)-1=(t+i)-(s+i+1) by omega)
    (show t=(t+i)-i by omega) a
  have ha' : a'≫(background.quotients.tower _).rho (i+1) (q+1) (by omega)=
      finiteTopLabel T.X i hi (s+i+1) (t+i) u := by
    simp only [a',←regrade_comp,ha,ordinaryEarlyTop,normalized_homotopy_regrade_trans,top_target_regrade_self]
  have haf' : a'≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)=
      homotopyRegrade (show (t+q)-(s+q+1)=(t+i)-(s+i+1) by omega)
        (show (t+q)-q=(t+i)-i by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
    simp only [a',←regrade_comp,haf,normalized_homotopy_regrade_trans]
  exact ordinary_early_long_top_division T.X T.Y T.f q i hi hiq (s+i+1) (t+i)
    (s+q+1) (t+q) (by omega) (by omega) u v a' ha' haf'


private theorem ordinary_compatible_source_second_at
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t B W A V : ℤ) (K d : ℕ)
    (hB : B=s+i) (hW : W=t+i) (hA : A=s+q+1) (hV : V=t+q)
    (hK : K=(q+1)-i) (hd : d=q-i)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (B+1,W))
    (v : Ambient background T.Y (A,V))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (B+1,W) c ((background.classical.map T.f).pageMap 2 (B+1,W) u))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) (A+1,V+1)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) s t c)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) A V v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p+1,(t-s+p)+1),
        z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) →
      ∃ y : Ambient background T.Y (p,t-s+p),
        y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p+1,(t-s+p)+1),
        k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p (t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p+1,(t-s+p)+1))
    (hH : ∀ z : Ambient background T.Z (s+(i+1),(t+(i+1)-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+(i+1)) (t+(i+1)-1) z ∈
        boundaries background T.X (i+1) (s+(i+1),t+(i+1)-1))
 :
    let S := B+1
    ∃ b : BiHom (W-S) W (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) K),
    ∃ u' : Ambient background T.X (S,W),
    ∃ aHat : BiHom ((W-S)+1) (W-i) (XModLambdaN (background.nu.functor.obj (T.Y.obj background.auxiliary)) i),
    ∃ D : BiHom (W-S) W (background.nu.functor.obj (T.Y.obj background.auxiliary)),
      b≫(background.quotients.tower _).rho 1 K (by omega)=nativeFirstLabel T.X S W u' ∧
      u'-u∈boundaries background T.X (i+1) (S,W) ∧
      D=homotopyRegrade (show ((W-S)+1)-1=W-S by omega) (show (W-i)+i=W by omega)
        (biSuspensionHomEquiv ((W-S)+1) (W-i) i (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (aHat≫XModLambdaN.proj _ i)) ∧
      lambdaMultiply i D=0 ∧
      b≫XModLambdaN.map (background.nu.functor.map T.f) K=D≫XModLambdaN.incl _ K+
        homotopyRegrade (show V-A=W-S by dsimp [S];omega) rfl
          (finiteTopLabelAtWeight T.Y d (by omega) K (by omega)
            A V W (by omega) v) := by
  subst B
  subst W
  subst A
  subst V
  subst K
  subst d
  exact ordinary_compatible_source_second T he hf hg hh i q hi hiq s t c u v hearly hdroot hR hH



/-- Source-side endpoint; the early boundary cutoff imposes no inequality with the main page. -/
public theorem ordinary_early_source_second
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i d N : ℕ) (hi : 0 < i) (hd : 0 < d) (hKN : d+1≤N) (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (u : Ambient background T.X ((B+1)+N+1,W+N))
    (y : Ambient background T.Y (B+d+1,W+d))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (N+1) (B+1,W) ((B+1)+N+1,W+N) x u)
    (c : Ambient background T.Y (B-i,W-i))
    (hearly : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) ((B-i),(W-i)) (B+1,W) c ((background.classical.map T.f).pageMap 2 (B+1,W) x))
    (hdroot : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      ((i+d)+1) ((B-i)+1,(W-i)+1) ((B+d+1)+1,(W+d)+1)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (B-i) (W-i) c)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (B+d+1) (W+d) y))
    (hR : ∀ p : ℤ, (B-i)+1≤p → p<(B-i)+(i+1)-1 →
      ∀ z : Ambient background T.Z (p+1,((W-i)-(B-i)+p)+1),
        z ∈ cycles background T.Z ((i+1)-(p-(B-i)).toNat:ℕ) (p+1,((W-i)-(B-i)+p)+1) →
      ∃ y : Ambient background T.Y (p,(W-i)-(B-i)+p),
        y ∈ cycles background T.Y ((i+1)-(p-(B-i)).toNat:ℕ) (p,(W-i)-(B-i)+p) ∧
      ∃ k : Ambient background T.Z (p+1,((W-i)-(B-i)+p)+1),
        k ∈ cycles background T.Z ((i+d)+1-(p-(B-i)).toNat:ℕ) (p+1,((W-i)-(B-i)+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p ((W-i)-(B-i)+p) y-k ∈
          boundaries background T.Z ((p-(B-i)).toNat+1) (p+1,((W-i)-(B-i)+p)+1))
    (hH : ∀ z : Ambient background T.Z ((B-i)+(i+1),((W-i)+(i+1)-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T ((B-i)+(i+1)) ((W-i)+(i+1)-1) z ∈
        boundaries background T.X (i+1) ((B-i)+(i+1),(W-i)+(i+1)-1))
    (hmid : ∀ j : ℕ, 1 ≤ j → j < (d+1)-1 →
      ∀ a : Ambient background T.X (B+1+j,W+j),
        a ∈ cycles background T.X (((d+1:ℕ):ℤ)-j) (B+1+j,W+j) →
        ∃ z' : Ambient background T.Z (B+1+j,W+j+1),
          z' ∈ cycles background T.Z (((d+1:ℕ):ℤ)-j) (B+1+j,W+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (B+1+j) (W+j) z' ∈
            boundaries background T.X ((j:ℤ)+1) (B+1+j,W+j))
    (himage : ∀ e : Ambient background T.X (B+d+1,W+d),
      (background.classical.map T.f).pageMap 2 (B+d+1,W+d) e∈cycles background T.Y ((N-d:ℕ)+1) (B+d+1,W+d)) :
    let v := (background.classical.map T.f).pageMap 2 ((B+1)+N+1,W+N) u
    IsCycle background T.Y (N-d:ℕ) (B+d+1,W+d) y ∧
      IsCycle background T.Y (N-d:ℕ) ((B+1)+N+1,W+N) v ∧
      DifferentialAt background T.Y ((N-d:ℕ)+1) (B+d+1,W+d) ((B+1)+N+1,W+N) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T he
  obtain ⟨a,x',aHat,D,ha,hxx,_,_,himageA⟩ :=
    ordinary_compatible_source_second_at T he hf hg hh
      i (i+d) hi (by omega) (B-i) (W-i) B W (B+d+1) (W+d) (d+1) d
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      c x y hearly hdroot hR hH
  have himg : a≫XModLambdaN.map (background.nu.functor.map T.f) (d+1)-D≫XModLambdaN.incl _ (d+1)=
      homotopyRegrade (show (W+d)-(B+d+1)=W-(B+1) by omega)
        (show (W+d)-d=W by omega) (finiteTopLabel T.Y d hd (B+d+1) (W+d) y) := by
    rw [himageA,add_sub_cancel_left]
    simp only [finiteTopLabelAtWeight,normalized_homotopy_regrade_trans]
  exact ordinary_early_source_of_compatible_source_second T he hT hf hg hh
    d N hd hKN B W (i+1) x x' u y hdx hxx hmid a ha D himg himage



/-- Target-side endpoint with the entire original terminal kernel. -/
public theorem ordinary_early_target_second
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
    (hmid : ∀ j : ℕ, 1≤j → j<(d+1)-1 →
      ∀ x : Ambient background T.X (((s+N)+1)+j-1+1,(t+N)+j),
        x ∈ cycles background T.X (((d+1):ℤ)-j) (((s+N)+1)+j-1+1,(t+N)+j) →
        (background.classical.map T.f).pageMap 2 (((s+N)+1)+j-1+1,(t+N)+j) x ∈ Pm j →
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
  exact ordinary_early_target_of_compatible_source_second T he hT hf hg hh
    N i d hi hiN hd s t x y hy u u' hdx hu v Pm hPm hmid a ha aHat D hD himg P hP hv hker

end
end KIP126.ProofTools.Internal.SyntheticCoverage
