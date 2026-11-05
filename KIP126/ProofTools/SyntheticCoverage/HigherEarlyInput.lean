module

import all KIP126.ProofTools.SyntheticCoverage.HigherEarlyLabel
import all KIP126.ProofTools.SyntheticCoverage.BoundaryPermanence

/-! Actual higher early-boundary inputs. The specified classical
higher differential constructs its finite square and a single root with
both prescribed images. Quotient-length transports retain the actual
selected adjacent delta and lambda maps. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

/-- The original specified higher differential supplies an actual finite
square. Its specified source lift is preserved along with its first label. -/
private theorem higher_classical_positive_finite_square
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i,t+i-1))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c
      (boundaryLabelRegrade rfl (show (t+i-1)+1=t+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+i) (t+i-1) u))) :
    ∃ a : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₂ i),
      a ≫ (background.quotients.tower _).rho 1 i hi=nativeFirstLabel T.Y s t c ∧
      a ≫ ((background.quotients.tower (normalizedTriangle background T he).obj₂).triangle hi
        (Nat.lt_succ_self i)).delta =
        higherPositiveBoundaryInput T he hf i s t u ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((SyntheticCategory.biShift (0,-(i:ℤ))).map
            (XModLambdaN.map (normalizedTriangle background T he).mor₁ (i+1-i))) := by
  obtain ⟨a,ha,hda⟩ := (differential_iff_specified_finite_lift T.Y i hi s t c _).mp hd
  refine ⟨a,ha,?_⟩
  let A := (normalizedTriangle background T he).obj₁
  let B := background.nu.functor.obj (T.Y.obj background.auxiliary)
  let g : A ⟶ B := (normalizedTriangle background T he).mor₁
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let δ : XModLambdaN B i ⟶ (F.obj (XModLambdaN B (i+1-i)))⟦(1:ℤ)⟧ :=
    ((background.quotients.tower B).triangle hi (Nat.lt_succ_self i)).delta
  let δ₁ : XModLambdaN B i ⟶ (F.obj (XModLambdaN B 1))⟦(1:ℤ)⟧ := by
    simpa only [show i+1-i=1 by omega] using δ
  let b₁ := (biSuspensionHomEquiv (t-s) t i (XModLambdaN A 1)).symm
    (homotopyRegrade (show (t+i-1)-(s+i)=(t-s)-1 by omega)
      (show (t+i-1)+1=t+i by omega) (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u))
  have hone : a ≫ δ₁=b₁ ≫ S.map (F.map (XModLambdaN.map g 1)) := by
    apply (biSuspensionHomEquiv (t-s) t i (XModLambdaN B 1)).injective
    rw [bi_susp_natural background.quotients.coherence]
    dsimp only [b₁]
    rw [AddEquiv.apply_symm_apply,←regrade_comp]
    change _ = homotopyRegrade _ _ (earlyNormalizedSourceLabel T he hf (s+i) (t+i-1) u ≫
      XModLambdaN.map (normalizedTriangle background T he).mor₁ 1)
    rw [early_normalized_source_image]
    apply homotopy_regrade_injective (show (t-s)-1=(t+i)-(s+i+1) by omega) rfl
    rw [normalized_homotopy_regrade_trans]
    rw [boundary_label_regrade_native,cofiberFirstQuotientBoundary_native_label,
      normalized_homotopy_regrade_trans] at hda
    convert hda using 1; rfl
  have transport (n : ℕ) (hn : n=1)
      (D : XModLambdaN B i ⟶ (F.obj (XModLambdaN B n))⟦(1:ℤ)⟧)
      (eD : (XModLambdaN B i ⟶ (F.obj (XModLambdaN B n))⟦(1:ℤ)⟧)=
        (XModLambdaN B i ⟶ (F.obj (XModLambdaN B 1))⟦(1:ℤ)⟧))
      (eb : BiHom (t-s) t ((F.obj (XModLambdaN A n))⟦(1:ℤ)⟧)=
        BiHom (t-s) t ((F.obj (XModLambdaN A 1))⟦(1:ℤ)⟧))
      (h : a ≫ eD.mp D=b₁ ≫ S.map (F.map (XModLambdaN.map g 1))) :
      a ≫ D=eb.mpr b₁ ≫ S.map (F.map (XModLambdaN.map g n)) := by
    subst n
    exact h
  exact transport (i+1-i) (by omega) δ (by rw [Nat.add_sub_cancel_left])
    (by rw [Nat.add_sub_cancel_left]) hone

/-- The specified higher early boundary constructs one root. Its first
label and its selected coefficient image both belong to that same root. -/
private theorem higher_positive_rotated_of_differential
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (i : ℕ) (hi : 0 < i) (s t : ℤ)
    (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i,t+i-1))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c
      (boundaryLabelRegrade rfl (show (t+i-1)+1=t+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+i) (t+i-1) u))) :
    ∃ (ex : XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (i+1-i) ≅
      (XModLambdaN (normalizedTriangle background T he).obj₁ (i+1-i))⟦(1:ℤ)⟧),
      XModLambdaN.incl _ (i+1-i) ≫ ex.hom =
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1-i)) ∧
      ∃ R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
        R ≫ (background.quotients.tower _).rho 1 (i+1) (by omega)=
          nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
            XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 ∧
        R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1)=
          higherRotatedInput T he i ex (t-s) t (higherPositiveBoundaryInput T he hf i s t u) ≫
            ((background.quotients.tower ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧)).triangle hi
              (Nat.lt_succ_self i)).lambdaMap := by
  obtain ⟨a,ha,hab⟩ := higher_classical_positive_finite_square T he hf i hi s t c u hd
  obtain ⟨ex,hex,R,hR,hRh⟩ := higher_positive_rotated_of_finite_square T he hT hf hg i hi
    (t-s) t a (higherPositiveBoundaryInput T he hf i s t u) hab
  refine ⟨ex,hex,R,?_,hRh⟩
  have hRfirst := congrArg (fun q => q ≫ (background.quotients.tower _).rho 1 i hi) hR
  rw [Category.assoc,(background.quotients.tower _).rho_comp] at hRfirst
  rw [Category.assoc,←(background.quotients.natural (normalizedTriangle background T he).mor₂).rho_naturality hi,
    ←Category.assoc,ha] at hRfirst
  rw [hRfirst,←native_first_label_natural,Category.assoc,←background.quotients.functoriality.map_comp]
  have hg' : background.nu.functor.map T.g ≫ (normalizedThirdZeroIso T he hg).inv =
      (normalizedTriangle background T he).mor₂ := by
    apply (cancel_mono (normalizedThirdZeroIso T he hg).hom).mp
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      (normalized_second_arrow_zero T he hg).symm
  rw [hg']

/-- The original higher early differential supplies a single finite root
with the literal G₂ first label and literal native top H label. -/
private theorem higher_positive_rotated_first_and_top
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=1)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (i : ℕ) (hi : 0 < i)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (i+1) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1)))
    (hε : XModLambdaN.incl _ (i+1) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (i+1)))
    (s t : ℤ) (c : Ambient background T.Y (s,t)) (u : Ambient background T.X (s+i,t+i-1))
    (hd : HasDifferential (background.classical.obj (T.Y.obj background.auxiliary))
      (i+1) (s,t) (s+i+1,t+i) c
      (boundaryLabelRegrade rfl (show (t+i-1)+1=t+i by omega)
        (KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (s+i) (t+i-1) u))) :
    ∃ R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)),
      R ≫ (background.quotients.tower _).rho 1 (i+1) (by omega)=
        nativeFirstLabel T.Z s t ((background.classical.map T.g).pageMap 2 (s,t) c) ≫
          XModLambdaN.map (normalizedThirdZeroIso T he hg).inv 1 ∧
      rawMaySourceDesuspend T he hf (i+1) i (s+i) (t+i-1) ε
        (homotopyRegrade (show t-s=(t+i-1)-(s+i)+1 by omega)
          (show t=(t+i-1)-i+1 by omega)
          (R ≫ XModLambdaN.map (normalizedTriangle background T he).mor₃ (i+1)))=
        finiteTopLabel T.X i hi (s+i) (t+i-1) u := by
  obtain ⟨ex,hex,R,hR,hRh⟩ := higher_positive_rotated_of_differential T he hT hf hg i hi s t c u hd
  refine ⟨R,hR,?_⟩
  rw [hRh]
  exact higher_rotated_input_top_label T he hf i hi ex hex ε hε s t u

end
end KIP126.ProofTools.Internal.SyntheticCoverage
