module

public import KIP126.ProofTools.Language

import all KIP126.ProofTools.MahowaldLeibniz.Filtration
import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.MahowaldLeibniz.NativeImageSquare
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryImageSquare
import all KIP126.ProofTools.SyntheticCoverage.RawImageComparison
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGSource
import all KIP126.ProofTools.LastLayerComparison.Actual
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionDetection

/-! Finite correction through the complete middle cycle spaces.
The h-image term is retained. Corrections at intermediate grades leave an
explicit residual at the last grade, preserving its image. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.MahowaldLeibniz KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

public def middleLabelRegrade {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ × ℤ}
    (h : p=q) (x : Ambient background X p) : Ambient background X q := h ▸ x

private theorem middle_label_regrade_eq_mpr {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ × ℤ}
    (h : p=q) (e : (Ambient background X q : Type)=(Ambient background X p : Type))
    (x : Ambient background X p) : middleLabelRegrade h x=e.mpr x := by
  subst q
  have he : e=rfl := Subsingleton.elim _ _
  rw [he]
  rfl

private theorem middle_label_regrade_cycles {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ × ℤ}
    (h : p=q) (k : ℤ) (x : Ambient background X p) :
    middleLabelRegrade h x ∈ cycles background X k q ↔ x ∈ cycles background X k p := by
  subst q; rfl

private theorem middle_label_regrade_boundaries {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ × ℤ}
    (h : p=q) (k : ℤ) (x : Ambient background X p) :
    middleLabelRegrade h x ∈ boundaries background X k q ↔ x ∈ boundaries background X k p := by
  subst q; rfl

private theorem middle_label_regrade_sub {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ × ℤ}
    (h : p=q) (x y : Ambient background X p) :
    middleLabelRegrade h (x-y) = middleLabelRegrade h x-middleLabelRegrade h y := by
  subst q; rfl

private theorem middle_label_regrade_inverse {X : (AdamsObject (coefficients := background.coefficients))} {p q : ℤ × ℤ}
    (h : p=q) (x : Ambient background X p) :
    middleLabelRegrade h.symm (middleLabelRegrade h x)=x := by
  subst q; rfl

/-- Cycle surjectivity modulo finite-window boundaries corrects
a representative up to the specified last filtration. -/
private theorem finite_filtered_correction_to_last
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (m w u v : ℤ)
    (huv : u ≤ v) (hwindow : 0 ≤ m+u-w) (hv : v ≤ (q:ℤ)+w-m)
    (hsurj : ∀ s : ℤ, u ≤ s → s < v →
      ∀ y : Ambient background Y (s,m+s),
        y ∈ cycles background Y ((q:ℤ)-(m+s)+w) (s,m+s) →
        ∃ x : Ambient background X (s,m+s),
          x ∈ cycles background X ((q:ℤ)-(m+s)+w) (s,m+s) ∧
          y-(background.classical.map f).pageMap 2 (s,m+s) x ∈
            boundaries background Y (1+(m+s)-w) (s,m+s))
    (z : BiHom m w (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (hz : FiltrationAtLeast background.syntheticTower u z) :
    ∃ a : BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q),
      FiltrationAtLeast background.syntheticTower u a ∧
      FiltrationAtLeast background.syntheticTower v
        (z-a ≫ XModLambdaN.map (background.nu.functor.map f) q) := by
  let SX : SyntheticObject := .quotient q (.nu X)
  let SY : SyntheticObject := .quotient q (.nu Y)
  let fq := XModLambdaN.map (background.nu.functor.map f) q
  let M := background.convergentMap SX SY fq
  induction hd : (v-u).toNat using Nat.strong_induction_on generalizing u z with
  | h d ih =>
    by_cases heq : v ≤ u
    · have huv' : u=v := le_antisymm huv heq
      refine ⟨0,(background.syntheticTower.filtrationSubmodule _ u (m,w)).zero_mem,?_⟩
      simpa only [Limits.zero_comp,sub_zero,←huv'] using hz
    · obtain ⟨zr,hzr⟩ := filtration_representative_exists background.syntheticTower
        (SY.obj background.nu background.auxiliary) (m,w) u z hz
      have hepi := finite_infinity_surjective_of_cycle_surjective X Y f q hq
        u (m+u) w (by omega) (hsurj u le_rfl (by omega))
      have hrange : (infinityGradedIso (background.convergence SY) (m,w) u).inv
          ((background.syntheticTower.filtration (SY.obj background.nu background.auxiliary)).toAssociatedGraded
            u (m,w) zr) ∈ Set.range ((background.family.functor.map fq).eInftyMap
              (u,m+u,w)).hom := hepi _
      obtain ⟨a,ha,hrem⟩ := (infinity_image_iff_lift M (m,w) u zr).mp hrange
      change BiHom m w (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q) at a
      rw [hzr] at hrem
      have hd' : (v-(u+1)).toNat < d := by omega
      obtain ⟨a',ha',hfinal⟩ := ih (v-(u+1)).toNat hd' (u+1) (by omega) (by omega)
        (fun s hs ht => hsurj s (by omega) ht) (z-a≫fq) hrem rfl
      refine ⟨a+a',?_,?_⟩
      · exact (background.syntheticTower.filtrationSubmodule _ u (m,w)).add_mem ha
          (background.syntheticTower.filtrationSubmodule_antitone _ (m,w) (by omega) ha')
      · simpa only [Preadditive.add_comp,sub_add_eq_sub_sub] using hfinal

/-- The middle condition concerns full classical cycle spaces modulo
the specified boundaries, transported through suspension
to the ordinary h-image condition. -/
private theorem middle_ordinary_h_cycle_coverage
    (T : TriangleData background.auxiliary) (c K : ℕ) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (j : ℕ) (hj : 1 ≤ j) (hjK : j < K-1)
    (y : Ambient background (.shift 1 T.X) (S+j,V+j+1))
    (hy : y ∈ cycles background (.shift 1 T.X) ((K:ℤ)-j) (S+j,V+j+1)) :
    ∃ z : Ambient background T.Z (S+j,V+j+1),
      z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
      y-(background.classical.map T.h).pageMap 2 (S+j,V+j+1) z ∈
        boundaries background (.shift 1 T.X) ((c:ℤ)+j+1) (S+j,V+j+1) := by
  obtain ⟨a,ha⟩ := exists_desuspendsClass T.X (S+j) (V+j+1) y
  have hp : (S+(j:ℤ),V+j+1-1)=(S+j,V+j) := by congr 1; omega
  let a' : Ambient background T.X (S+j,V+j) := middleLabelRegrade hp a
  have hac : a' ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) :=
    (middle_label_regrade_cycles hp _ a).mpr
      ((desuspendsClass_cycle_iff T.X _ _ _ y a ha).mp hy)
  obtain ⟨z,hz,haz⟩ := hmid j hj hjK a' hac
  refine ⟨z,hz,?_⟩
  have hhz := KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T (S+j) (V+j) z
  have hsub := suspension_desuspends_sub T.X (S+j) (V+j+1) _ _ _ _ ha hhz
  apply (desuspendsClass_boundary_iff T.X _ _ _ _ _ hsub).mpr
  have haz' := (middle_label_regrade_boundaries hp.symm ((c:ℤ)+j+1) _).mpr haz
  rw [middle_label_regrade_sub] at haz'
  have haid : middleLabelRegrade hp.symm a'=a := middle_label_regrade_inverse hp a
  rw [haid] at haz'
  convert haz' using 1
  congr 1
  exact (middle_label_regrade_eq_mpr hp.symm _ _).symm

/-- The M_j conditions retain their h-cycle term and correct the actual
finite representative only as far as the final visible grade. -/
private theorem middle_ordinary_h_filtered_correction
    (T : TriangleData background.auxiliary) (c K : ℕ) (hK : 2 ≤ K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN (background.nu.functor.obj ((AdamsObject.shift 1 T.X).obj background.auxiliary)) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1) a) :
    ∃ b : BiHom (V-S+1) (V-c+1)
      (XModLambdaN (background.nu.functor.obj (T.Z.obj background.auxiliary)) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+1) b ∧
      FiltrationAtLeast background.syntheticTower (S+K-1)
        (a-b≫XModLambdaN.map (background.nu.functor.map T.h) (c+K)) := by
  apply finite_filtered_correction_to_last T.Z (.shift 1 T.X) T.h
    (c+K) (by omega) (V-S+1) (V-c+1) (S+1) (S+K-1)
    (by omega) (by omega) (by omega) ?_ a ha
  intro k hk hktop
  let j := (k-S).toNat
  have hj : (j:ℤ)=k-S := by dsimp [j]; omega
  have hj1 : 1 ≤ j := by omega
  have hjK : j < K-1 := by omega
  have h := middle_ordinary_h_cycle_coverage T c K S V hmid j hj1 hjK
  have hs : S+(j:ℤ)=k := by omega
  have ht : V+(j:ℤ)+1=V-S+1+k := by omega
  have hc : (c+K:ℕ)-(V-S+1+k)+(V-(c:ℤ)+1)=(K:ℤ)-j := by omega
  have hb : 1+(V-S+1+k)-(V-(c:ℤ)+1)=(c:ℤ)+(j:ℤ)+1 := by omega
  rw [hs,ht] at h
  rw [hc,hb]
  exact h

/-- In the positive-f normalization, the complete M_j conditions correct
only by actual third-arrow images. The corrected residual lies in the last
filtration and has exactly the same actual suspended first-arrow image. -/
private theorem middle_normalized_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2 ≤ K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1)
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+K))) :
    ∃ e : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1)
        (e ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+K)) ∧
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+K) =
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+K) := by
  let N := normalizedTriangle background T he
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  obtain ⟨b,_,hb⟩ := middle_ordinary_h_filtered_correction T c K hK S V hmid
    (a ≫ XModLambdaN.map E.hom (c+K)) ha
  have hcomm : XModLambdaN.map N.mor₃ (c+K) ≫ XModLambdaN.map E.hom (c+K) =
      XModLambdaN.map EZ.hom (c+K) ≫
        XModLambdaN.map (background.nu.functor.map T.h) (c+K) := by
    rw [←background.quotients.functoriality.map_comp,←background.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f (c+K))
      (normalized_third_arrow_zero T he hf hg hh)
  let correction := (b ≫ XModLambdaN.map EZ.inv (c+K)) ≫ XModLambdaN.map N.mor₃ (c+K)
  have hcorrection : correction ≫ XModLambdaN.map E.hom (c+K) =
      b ≫ XModLambdaN.map (background.nu.functor.map T.h) (c+K) := by
    dsimp only [correction]
    rw [Category.assoc,Category.assoc,hcomm]
    rw [←Category.assoc (XModLambdaN.map EZ.inv (c+K)),
      ←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id,Category.id_comp]
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (c+K) (by omega)
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ (c+K) ≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K) ≫
      ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ (c+K) ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K)=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  refine ⟨a-correction,?_,?_⟩
  · rw [Preadditive.sub_comp,hcorrection]
    exact hb
  · rw [Preadditive.sub_comp]
    have hz : correction ≫ XModLambdaN.map
        ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K)=0 := by
      dsimp only [correction]
      rw [Category.assoc,hzero',comp_zero]
    rw [hz,sub_zero]

/-- Native desuspension preserves filtration, complementing filtration
reflection for the same finite May quotient comparison. -/
private theorem raw_may_source_desuspend_preserves_filtration
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (N c : ℕ) (S V j : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : FiltrationAtLeast background.syntheticTower j
      (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom N)) :
    FiltrationAtLeast background.syntheticTower j
      (rawMaySourceDesuspend T he hf N c S V ε a) := by
  have hm := map_preserves_filtration
    (background.convergentMap (.quotient N (.nu (.shift 1 T.X)))
      (.quotient N (.shift (1,1) (.nu T.X)))
      (XModLambdaN.map (background.nu.suspensionIso (T.X.obj background.auxiliary)).hom N))
    (V-S+1,V-c+1) j _ ha
  apply quotient_unshift_preserves_filtration T.X (1,1) (V-S,V-c) N ε j
  exact (regrade_filtration_iff rfl rfl j _).mpr (by simpa only [Category.assoc,SyntheticObject.obj,FiltrationAtLeast,Prod.fst_add,Prod.snd_add] using hm)

/-- Middle h-cycle correction together with the actual final F-boundary
condition annihilates finite May ambiguity. The middle hypothesis retains
all h-images; only the final condition kills their remaining F-image. -/
private theorem middle_and_last_boundary_annihilation
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g +
      normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 1)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2 ≤ K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (hε : XModLambdaN.incl _ (c+K) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+K)))
    (εp : XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (0,1)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (hεp : XModLambdaN.incl _ (c+K) ≫ εp.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl _ (c+K)))
    (hlast : ∀ x : Ambient background T.X (S+K-1,V+K-1),
      KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf (S+K-1) (V+K-1) x ∈
        boundaries background T.Y (c+K) (S+K-1+1,V+K-1+1))
    (a : BiHom (V-S+1) (V-c+1)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1)
      (rawMaySourceDesuspend T he hf (c+K) c S V ε a)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+K) = 0 := by
  have hat := raw_may_source_desuspend_reflects_filtration
    T he hf (c+K) c S V (S+1) ε a ha
  obtain ⟨e,hefil,heimage⟩ := middle_normalized_residual_same_image
    T he hf hg hh hT c K hK S V hmid a hat
  let en := rawMaySourceDesuspend T he hf (c+K) c S V ε e
  have hen : FiltrationAtLeast background.syntheticTower (S+K-1) en :=
    raw_may_source_desuspend_preserves_filtration T he hf (c+K) c S V
      (S+K-1) ε e hefil
  let en' := homotopyRegrade (show V-S=(V+K-1)-(S+K-1) by omega)
    (show V-c=(V+K-1)-(c+K-1:ℕ) by omega) en
  have hen' : FiltrationAtLeast background.syntheticTower (S+K-1) en' :=
    (regrade_filtration_iff _ _ (S+K-1) en).mpr hen
  have hz := last_layer_positive_image_zero_q T hf (c+K) (by omega)
    (S+K-1) (V+K-1) εp hεp hlast en' hen'
  rw [←positiveFiniteImage_regrade] at hz
  have hz' : positiveFiniteImage T hf (c+K) εp (V-S) (V-c) en=0 :=
    (last_layer_regrade_zero_iff _ _ _).mp hz
  have hezero := native_positive_image_zero_implies_raw_zero T he hf (c+K) c (by omega)
    S V ε εp hε hεp e hz'
  exact heimage.symm.trans hezero

/-- Unshifting the same finite ordinary map commutes with its actual
homotopy map, for any inclusion-compatible quotient shift comparisons. -/
private theorem middle_quotient_unshift_ordinary_natural
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (δ p : ℤ × ℤ)
    (εX : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (εY : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (Y.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (hεX : XModLambdaN.incl _ q ≫ εX.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (hεY : XModLambdaN.incl _ q ≫ εY.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom (p+δ).1 (p+δ).2 (XModLambdaN ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q)) :
    quotientUnshift Y δ p q εY
      (a ≫ XModLambdaN.map ((SyntheticCategory.biShift δ).map (background.nu.functor.map f)) q) =
      quotientUnshift X δ p q εX a ≫ XModLambdaN.map (background.nu.functor.map f) q := by
  have hn := shifted_ordinary_quotient_map_on_spheres X Y f q hq δ εX εY hεX hεY _ _ a
  apply (SyntheticCategory.biShift_fullyFaithful δ).map_injective
  simp only [quotientUnshift,Functor.map_comp,Functor.FullyFaithful.map_preimage,Category.assoc]
  rw [hn]

/-- The finite middle correction after a bigraded shift, transporting
the ordinary h map through the quotient comparisons. -/
private theorem finite_shifted_filtered_correction_to_last
    (X Y : (AdamsObject (coefficients := background.coefficients))) (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary)
    (q : ℕ) (hq : 0 < q) (δ : ℤ × ℤ) (m w u v : ℤ)
    (huv : u ≤ v) (hwindow : 0 ≤ m+u-w) (hv : v ≤ (q:ℤ)+w-m)
    (hsurj : ∀ s : ℤ, u ≤ s → s < v →
      ∀ y : Ambient background Y (s,m+s),
        y ∈ cycles background Y ((q:ℤ)-(m+s)+w) (s,m+s) →
        ∃ x : Ambient background X (s,m+s),
          x ∈ cycles background X ((q:ℤ)-(m+s)+w) (s,m+s) ∧
          y-(background.classical.map f).pageMap 2 (s,m+s) x ∈
            boundaries background Y (1+(m+s)-w) (s,m+s))
    (εX : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (X.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (εY : XModLambdaN ((SyntheticCategory.biShift δ).obj
      (background.nu.functor.obj (Y.obj background.auxiliary))) q ≅
      (SyntheticCategory.biShift δ).obj
        (XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q))
    (hεX : XModLambdaN.incl _ q ≫ εX.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (hεY : XModLambdaN.incl _ q ≫ εY.hom =
      (SyntheticCategory.biShift δ).map (XModLambdaN.incl _ q))
    (a : BiHom ((m,w)+δ).1 ((m,w)+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (Y.obj background.auxiliary))) q))
    (ha : FiltrationAtLeast background.syntheticTower u a) :
    ∃ b : BiHom ((m,w)+δ).1 ((m,w)+δ).2
      (XModLambdaN ((SyntheticCategory.biShift δ).obj
        (background.nu.functor.obj (X.obj background.auxiliary))) q),
      FiltrationAtLeast background.syntheticTower u b ∧
      FiltrationAtLeast background.syntheticTower v
        (a-b ≫ XModLambdaN.map ((SyntheticCategory.biShift δ).map
          (background.nu.functor.map f)) q) := by
  let a₀ := quotientUnshift Y δ (m,w) q εY a
  have ha₀ : FiltrationAtLeast background.syntheticTower u a₀ :=
    quotient_unshift_preserves_filtration Y δ (m,w) q εY u a ha
  obtain ⟨b₀,hb₀,hrem⟩ := finite_filtered_correction_to_last
    X Y f q hq m w u v huv hwindow hv hsurj a₀ ha₀
  let b := shiftHomotopyClass δ (m,w) b₀ ≫ εX.inv
  have hb : quotientUnshift X δ (m,w) q εX b=b₀ :=
    quotient_unshift_shift X δ (m,w) q εX b₀
  refine ⟨b,?_,?_⟩
  · apply quotient_unshift_reflects_filtration X δ (m,w) q εX u
    rw [hb]
    exact hb₀
  · apply quotient_unshift_reflects_filtration Y δ (m,w) q εY v
    rw [quotient_unshift_sub,middle_quotient_unshift_ordinary_natural X Y f q hq
      δ (m,w) εX εY hεX hεY,hb]
    exact hrem

/-- In the positive-g branch the actual third object has weight -1.
This comparison retains that shift and the chosen suspension of νX. -/
private def middlePositiveGTargetIso
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0) :
    ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) ≅
      (SyntheticCategory.biShift (0,-1)).obj
        (background.nu.functor.obj ((AdamsObject.shift 1 T.X).obj background.auxiliary)) :=
  normalizedSuspensionZeroIso T he hf ≪≫
    (biShiftAddIso (1,1) (0,-1) (1,0) (by decide)).symm.app _ ≪≫
      (SyntheticCategory.biShift (0,-1)).mapIso
        (background.nu.suspensionIso (T.X.obj background.auxiliary)).symm

private theorem middle_positive_g_third_map
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0) :
    (normalizedTriangle background T he).mor₃ ≫ (middlePositiveGTargetIso T he hf).hom =
      (normalizedThirdNegativeIso T he hg).hom ≫
        (SyntheticCategory.biShift (0,-1)).map (background.nu.functor.map T.h) := by
  simp only [middlePositiveGTargetIso,AdamsObject.obj,Iso.trans_hom,Functor.mapIso_hom]
  rw [←Category.assoc,←Category.assoc,normalized_third_arrow_positive_g T he hf hg hh]
  simp only [zeroHShiftedRaw,Category.assoc,Iso.app_hom,Iso.symm_hom,
    Iso.hom_inv_id_app_assoc,Functor.map_comp]
  simp only [←Functor.map_comp,Iso.hom_inv_id,Category.comp_id]

private theorem middle_positive_g_native_filtration_iff
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (N c : ℕ) (s t j : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (a : BiHom (t-s) (t-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N)) :
    FiltrationAtLeast background.syntheticTower j
        (positiveHSourceDesuspend T he hf N c s t ε a) ↔
      FiltrationAtLeast background.syntheticTower j
        (a ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom N) := by
  let E := normalizedSuspensionZeroIso T he hf
  let D := middlePositiveGTargetIso T he hf
  let J := E.symm ≪≫ D
  have hforward : XModLambdaN.map E.hom N ≫ XModLambdaN.map J.hom N =
      XModLambdaN.map D.hom N := by
    rw [←background.quotients.functoriality.map_comp]
    simp only [J,Iso.trans_hom,Iso.symm_hom,Iso.hom_inv_id_assoc]
  have hback : XModLambdaN.map D.hom N ≫ XModLambdaN.map J.inv N =
      XModLambdaN.map E.hom N := by
    rw [←background.quotients.functoriality.map_comp]
    simp only [J,Iso.trans_inv,Iso.symm_inv,Iso.hom_inv_id_assoc]
  constructor
  · intro ha
    have hu := quotient_unshift_reflects_filtration T.X (1,0) (t-(s+1),t-c) N ε j _ ha
    have hzero : FiltrationAtLeast background.syntheticTower j (a ≫ XModLambdaN.map E.hom N) :=
      (regrade_filtration_iff _ _ j _).mp hu
    have hm := map_preserves_filtration
      (background.convergentMap (.quotient N (.shift (1,0) (.nu T.X)))
        (.quotient N (.shift (0,-1) (.nu (.shift 1 T.X)))) (XModLambdaN.map J.hom N))
      (t-s,t-c) j _ hzero
    change FiltrationAtLeast background.syntheticTower j
      ((a ≫ XModLambdaN.map E.hom N) ≫ XModLambdaN.map J.hom N) at hm
    rw [Category.assoc,hforward] at hm
    exact hm
  · intro ha
    have hm := map_preserves_filtration
      (background.convergentMap (.quotient N (.shift (0,-1) (.nu (.shift 1 T.X))))
        (.quotient N (.shift (1,0) (.nu T.X))) (XModLambdaN.map J.inv N))
      (t-s,t-c) j _ ha
    change FiltrationAtLeast background.syntheticTower j
      ((a ≫ XModLambdaN.map D.hom N) ≫ XModLambdaN.map J.inv N) at hm
    rw [Category.assoc,hback] at hm
    apply quotient_unshift_preserves_filtration T.X (1,0) (t-(s+1),t-c) N ε j
    exact (regrade_filtration_iff _ _ j _).mpr hm

/-- General M_j correction in the positive-g branch. The connecting map
is the shifted ordinary h map, with its negative weight shift retained. -/
private theorem middle_positive_g_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2 ≤ K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (a : BiHom (V-S+1) (V-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1)
      (a ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (c+K))) :
    ∃ e : BiHom (V-S+1) (V-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1)
        (e ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (c+K)) ∧
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+K) =
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+K) := by
  let N := normalizedTriangle background T he
  let E := middlePositiveGTargetIso T he hf
  let EZ := normalizedThirdNegativeIso T he hg
  have hsurj : ∀ k : ℤ, S+1 ≤ k → k < S+K-1 →
      ∀ y : Ambient background (.shift 1 T.X) (k,V-S+1+k),
        y ∈ cycles background (.shift 1 T.X) ((c+K:ℕ)-(V-S+1+k)+(V-c+1)) (k,V-S+1+k) →
        ∃ x : Ambient background T.Z (k,V-S+1+k),
          x ∈ cycles background T.Z ((c+K:ℕ)-(V-S+1+k)+(V-c+1)) (k,V-S+1+k) ∧
          y-(background.classical.map T.h).pageMap 2 (k,V-S+1+k) x ∈
            boundaries background (.shift 1 T.X) (1+(V-S+1+k)-(V-c+1)) (k,V-S+1+k) := by
    intro k hk hktop
    let j := (k-S).toNat
    have hj : (j:ℤ)=k-S := by dsimp [j]; omega
    have h := middle_ordinary_h_cycle_coverage T c K S V hmid j (by omega) (by omega)
    have hs : S+(j:ℤ)=k := by omega
    have ht : V+(j:ℤ)+1=V-S+1+k := by omega
    have hc : (c+K:ℕ)-(V-S+1+k)+(V-(c:ℤ)+1)=(K:ℤ)-j := by omega
    have hb : 1+(V-S+1+k)-(V-(c:ℤ)+1)=(c:ℤ)+(j:ℤ)+1 := by omega
    rw [hs,ht] at h
    rw [hc,hb]
    exact h
  have H := finite_shifted_filtered_correction_to_last T.Z (.shift 1 T.X) T.h
    (c+K) (by omega) (0,-1) (V-S+1) (V-c+1) (S+1) (S+K-1)
    (by omega) (by omega) (by omega) hsurj
    (levelQuotientShiftIso T.Z (-1) (c+K))
    (levelQuotientShiftIso (.shift 1 T.X) (-1) (c+K))
    (level_quotient_shift_incl T.Z (-1) (c+K))
    (level_quotient_shift_incl (.shift 1 T.X) (-1) (c+K))
  let aa := homotopyRegrade
    (show V-S+1=((V-S+1,V-(c:ℤ)+1)+(0,-1)).1 by dsimp; omega)
    (show V-(c:ℤ)=((V-S+1,V-(c:ℤ)+1)+(0,-1)).2 by dsimp; omega)
    (a ≫ XModLambdaN.map E.hom (c+K))
  have haa : FiltrationAtLeast background.syntheticTower (S+1) aa :=
    (regrade_filtration_iff _ _ _ _).mpr ha
  obtain ⟨b₀,_,hb₀⟩ := H aa haa
  let b := homotopyRegrade
    (show ((V-S+1,V-(c:ℤ)+1)+(0,-1)).1=V-S+1 by dsimp; omega)
    (show ((V-S+1,V-(c:ℤ)+1)+(0,-1)).2=V-(c:ℤ) by dsimp; omega) b₀
  have hb : FiltrationAtLeast background.syntheticTower (S+K-1)
      (a ≫ XModLambdaN.map E.hom (c+K) -
        b ≫ XModLambdaN.map ((SyntheticCategory.biShift (0,-1)).map
          (background.nu.functor.map T.h)) (c+K)) := by
    have h := (regrade_filtration_iff
      (show ((V-S+1,V-(c:ℤ)+1)+(0,-1)).1=V-S+1 by dsimp; omega)
      (show ((V-S+1,V-(c:ℤ)+1)+(0,-1)).2=V-(c:ℤ) by dsimp; omega) _ _).mpr hb₀
    simp only [aa,b,homotopy_regrade_sub,regrade_comp,regrade_transitive] at h ⊢
    have hrefl : homotopyRegrade (rfl : V-S+1=V-S+1) (rfl : V-(c:ℤ)=V-c) a = a := rfl
    rw [hrefl] at h
    exact h
  have hcomm : XModLambdaN.map N.mor₃ (c+K) ≫ XModLambdaN.map E.hom (c+K) =
      XModLambdaN.map EZ.hom (c+K) ≫
        XModLambdaN.map ((SyntheticCategory.biShift (0,-1)).map (background.nu.functor.map T.h)) (c+K) := by
    rw [←background.quotients.functoriality.map_comp,←background.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f (c+K))
      (middle_positive_g_third_map T he hf hg hh)
  let correction := (b ≫ XModLambdaN.map EZ.inv (c+K)) ≫ XModLambdaN.map N.mor₃ (c+K)
  have hcorrection : correction ≫ XModLambdaN.map E.hom (c+K) =
      b ≫ XModLambdaN.map ((SyntheticCategory.biShift (0,-1)).map (background.nu.functor.map T.h)) (c+K) := by
    dsimp only [correction]
    rw [Category.assoc,Category.assoc,hcomm]
    rw [←Category.assoc (XModLambdaN.map EZ.inv (c+K)),
      ←background.quotients.functoriality.map_comp,Iso.inv_hom_id,
      background.quotients.functoriality.map_id,Category.id_comp]
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he (c+K) (by omega)
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ (c+K) ≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K) ≫
      ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ (c+K) ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K)=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  refine ⟨a-correction,?_,?_⟩
  · rw [Preadditive.sub_comp,hcorrection]
    exact hb
  · rw [Preadditive.sub_comp]
    have hz : correction ≫ XModLambdaN.map
        ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) (c+K)=0 := by
      dsimp only [correction]
      rw [Category.assoc,hzero',comp_zero]
    rw [hz,sub_zero]

/-- The positive-g middle condition plus the whole last ordinary f-image
boundary condition annihilates every higher raw May ambiguity. -/
private theorem middle_positive_g_raw_annihilation
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2 ≤ K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1 ≤ j → j < K-1 →
      ∀ a : Ambient background T.X (S+j,V+j),
        a ∈ cycles background T.X ((K:ℤ)-j) (S+j,V+j) →
        ∃ z : Ambient background T.Z (S+j,V+j+1),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j,V+j+1) ∧
          a-KIP126.ProofTools.Standard.classicalTriangleHMapHom T (S+j) (V+j) z ∈
            boundaries background T.X ((c:ℤ)+j+1) (S+j,V+j))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (hε : XModLambdaN.incl _ (c+K) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+K)))
    (hlast : ∀ x : Ambient background T.X (S+K-1,V+K-1),
      (background.classical.map T.f).pageMap 2 (S+K-1,V+K-1) x ∈
        boundaries background T.Y (c+K) (S+K-1,V+K-1))
    (a : BiHom (V-(S-1)) (V-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1)
      (positiveHSourceDesuspend T he hf (c+K) c (S-1) V ε a)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+K) = 0 := by
  have ha' := (middle_positive_g_native_filtration_iff T he hf (c+K) c
    (S-1) V (S+1) ε a).mp ha
  let a' := homotopyRegrade (show V-(S-1)=V-S+1 by omega) rfl a
  have haf : FiltrationAtLeast background.syntheticTower (S+1)
      (a' ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (c+K)) := by
    dsimp only [a']
    rw [←regrade_comp]
    exact (regrade_filtration_iff _ _ _ _).mpr ha'
  obtain ⟨e,hefil,heimage⟩ := middle_positive_g_residual_same_image
    T he hf hg hh hT c K hK S V hmid a' haf
  let e' := homotopyRegrade (show V-S+1=V-(S-1) by omega) rfl e
  have hef : FiltrationAtLeast background.syntheticTower (S+K-1)
      (e' ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (c+K)) := by
    dsimp only [e']
    rw [←regrade_comp]
    exact (regrade_filtration_iff _ _ _ _).mpr hefil
  let en := positiveHSourceDesuspend T he hf (c+K) c (S-1) V ε e'
  have hen : FiltrationAtLeast background.syntheticTower (S+K-1) en :=
    (middle_positive_g_native_filtration_iff T he hf (c+K) c
      (S-1) V (S+K-1) ε e').mpr hef
  let b := homotopyRegrade (show V-(S-1+1)=(V+K-1)-(S+K-1) by omega) rfl en
  have hb : FiltrationAtLeast background.syntheticTower (S+K-1) b :=
    (regrade_filtration_iff _ _ _ _).mpr hen
  have hz := ordinary_map_top_filtration_zero T.X T.Y T.f (c+K) (by omega)
    (S+K-1) (V+K-1) (V-c) (by omega) hlast b hb
  have henz : en ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=0 := by
    apply (ordinary_regrade_zero_iff (show V-(S-1+1)=(V+K-1)-(S+K-1) by omega) rfl _).mp
    simpa only [b,regrade_comp] using hz
  have heraw := native_ordinary_image_zero_implies_raw_zero T he hf (c+K) c (by omega)
    (S-1) V ε hε e' henz
  have hezero : e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+K)=0 := by
    apply (ordinary_regrade_zero_iff (show V-S+1=V-(S-1) by omega) rfl _).mp
    simpa only [e',regrade_comp] using heraw
  have hazero := heimage.symm.trans hezero
  apply (ordinary_regrade_zero_iff (show V-(S-1)=V-S+1 by omega) rfl _).mp
  simpa only [a',regrade_comp] using hazero

/-- A positive h cycle supplies an actual finite h-image, with the same
specified first-quotient label. The subsequent coefficient insertion retains
its zero image under the following normalized f map. -/
private theorem middle_positive_h_cycle_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (k q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s,t))
    (hz : z ∈ cycles background T.Z q (s,t))
    (u : Ambient background T.X (s+1,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa only [add_sub_cancel_right] using u))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (k+q) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)))
    (hε : XModLambdaN.incl _ (k+q) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (k+q))) :
    ∃ a : BiHom (t-s) (t-k)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (k+q)),
      Detects (background.convergence (.quotient (k+q) (.nu T.X))) (s+1,t,t-k)
        (finiteTargetLabel background T.X (k+q) (s+1) t k u)
        (positiveHSourceDesuspend T he hf (k+q) k s t ε a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (k+q)=0 := by
  let N := normalizedTriangle background T he
  let EZ := normalizedThirdZeroIso T he hg
  obtain ⟨z₀,hz₀⟩ := (KIP126.Literature.Standard.finite_lift_criterion T.Z q hq s t z).mp
    ((isCycle_iff_reaches background T.Z (q+1) (by omega) (s,t) z).mp
      ⟨by omega,by simpa only [add_sub_cancel_right] using hz⟩)
  let b := (z₀ ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) ≫
    XModLambdaN.map EZ.inv q
  have hzNu : (z₀ ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) q) ≫
      (background.quotients.tower (background.nu.functor.obj (T.Z.obj background.auxiliary))).rho 1 q (by omega) =
      nativeFirstLabel T.Z s t z := by
    erw [Category.assoc,
      ←(background.quotients.natural (SyntheticCategory.biShift_zero.hom.app
        (background.nu.functor.obj (T.Z.obj background.auxiliary)))).rho_naturality (show 1≤q by omega),
      ←Category.assoc,hz₀]
    rfl
  have hb : b ≫ (background.quotients.tower N.obj₃).rho 1 q (by omega) =
      nativeFirstLabel T.Z s t z ≫ XModLambdaN.map EZ.inv 1 := by
    dsimp only [b]
    rw [Category.assoc,←(background.quotients.natural EZ.inv).rho_naturality (show 1≤q by omega),
      ←Category.assoc,hzNu]
  let a₀ := b ≫ XModLambdaN.map N.mor₃ q
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨εq,hεq,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) q
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  have ha₀ := (positive_h_may_source_first_label T he hf hg hh q q hq le_rfl
    s t z u hu εq hεq b a₀ hb (by
      rw [(background.quotients.tower _).rho_id,Category.comp_id])).2.1
  let a := finiteCoefficientInsert _ k q hq (t-s) t a₀
  refine ⟨a,positive_h_coefficient_source_detects T he hf k q hq s t u
    εq ε hεq hε a₀ ha₀,?_⟩
  obtain ⟨ey,_,hrow⟩ := KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row
    T he q hq
  have hzero := comp_distTriang_mor_zero₂₃ _ hrow
  change XModLambdaN.map N.mor₃ q ≫
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫ ey.hom))=0 at hzero
  rw [Preadditive.comp_neg,neg_eq_zero] at hzero
  have hzero' : XModLambdaN.map N.mor₃ q ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 := by
    apply (cancel_mono ey.hom).mp
    simpa only [Category.assoc,zero_comp] using hzero
  dsimp only [a]
  rw [finite_coefficient_insert_natural]
  have ha₀zero : a₀ ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 := by
    dsimp only [a₀]
    rw [Category.assoc,hzero',comp_zero]
  rw [ha₀zero]
  have insert_zero (A : SyntheticSpectrum) (k q : ℕ) (hq : 0<q) (m w : ℤ) :
      finiteCoefficientInsert A k q hq m w 0=0 := by
    have cast_zero {n n' : ℕ} (h : n=n') :
        (congrArg (fun v => BiHom m w (XModLambdaN A v)) h).mp
          (0 : BiHom m w (XModLambdaN A n))=0 := by
      subst n'; rfl
    unfold finiteCoefficientInsert
    change finiteCoefficientShiftClass A (k+q) k _ m w
      ((congrArg (fun v => BiHom m w (XModLambdaN A v))
        (show q=k+q-k by omega)).mp 0)=0
    rw [cast_zero (show q=k+q-k by omega)]
    have rz {A : SyntheticSpectrum} {m m' w w' : ℤ}
        (hm : m=m') (hw : w=w') :
        homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
      subst m'; subst w'; rfl
    by_cases hk : k=0
    · subst k
      simp only [finiteCoefficientShiftClass,dite_true,rz]
    · simp only [finiteCoefficientShiftClass,dif_neg hk,shiftHomotopyClass,
        Functor.map_zero,comp_zero,rz,zero_comp]
  exact insert_zero _ k q hq (t-s) t

private theorem middle_finite_label_as_weight (X : (AdamsObject (coefficients := background.coefficients)))
    (q k : ℕ) (s t : ℤ) (x : Ambient background X (s,t)) :
    (background.family.quotientProjection (background.nu.functor.obj (X.obj background.auxiliary)) q).pageMap
      2 (s,t,t-k) (nuWeightLabel background X s t (t-k) (by omega) x) =
      finiteTargetLabel background X q s t k x := by
  have hlabel : nuWeightLabel background X s t (t-k) (by omega) x = targetNuLabel background X s t k x := by
    have htransport (n n' : ℕ) (h : n=n')
        (hp : (s,t,t-n)=(s,t,t-n')) :
        regradeE2 hp (targetNuLabel background X s t n x)=targetNuLabel background X s t n' x := by
      subst n'; rfl
    exact htransport _ k (by omega) _
  rw [hlabel]
  rfl

/-- Every actual finite filtered element has a classical label in the exact
finite cycle window. The label may be zero or a true boundary. -/
private theorem middle_finite_filtration_label (X : (AdamsObject (coefficients := background.coefficients)))
    (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (a : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    ∃ x : Ambient background X (s,t), x ∈ cycles background X (q-k:ℕ) (s,t) ∧
      Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
        (finiteTargetLabel background X q s t k x) a := by
  let A : SyntheticObject := .quotient q (.nu X)
  obtain ⟨ar,har⟩ := filtration_representative_exists background.syntheticTower
    (A.obj background.nu background.auxiliary) (t-s,t-k) s a ha
  let e := ((background.convergence A).identification (s,t,t-k)).inv
    ((background.syntheticTower.filtration (A.obj background.nu background.auxiliary)).toAssociatedGraded
      s (t-s,t-k) ar)
  obtain ⟨x,hx,hrep,_⟩ := CrossingLabels.finite_grade_label X q (by omega)
    s t (t-k) (by omega) e
  rw [middle_finite_label_as_weight] at hrep
  refine ⟨x,?_,e,hrep,ar,har,?_⟩
  · convert hx using 1
    congr 1
    omega
  · exact ((background.convergence A).identification (s,t,t-k)).toLinearEquiv.apply_symm_apply _

/-- Finite labels congruent modulo precisely B_(k+1) detect the same actual
grade, hence their representative difference lies one filtration higher. -/
private theorem middle_finite_congruent_difference (X : (AdamsObject (coefficients := background.coefficients)))
    (q k : ℕ) (hkq : k<q) (s t : ℤ)
    (x u : Ambient background X (s,t))
    (hxu : x-u ∈ boundaries background X (k+1) (s,t))
    (a b : BiHom (t-s) (t-k)
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q))
    (ha : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X q s t k x) a)
    (hb : Detects (background.convergence (.quotient q (.nu X))) (s,t,t-k)
      (finiteTargetLabel background X q s t k u) b) :
    FiltrationAtLeast background.syntheticTower (s+1) (a-b) := by
  obtain ⟨ex,hx,ar,har,hae⟩ := ha
  obtain ⟨eu,hu,br,hbr,hbe⟩ := hb
  have hxw := hx
  have huw := hu
  rw [←middle_finite_label_as_weight] at hxw huw
  obtain ⟨hxc,hxe⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
    s t (t-k) (by omega) x ex).mp hxw
  obtain ⟨huc,hue⟩ := (KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
    s t (t-k) (by omega) u eu).mp huw
  have heq : ex=eu := by
    apply (KIP126.Literature.Standard.infinityFiniteWindow X q (by omega)
      (s,t) (t-k) (by omega)).injective
    rw [hxe,hue]
    apply sub_eq_zero.mp
    rw [←map_sub]
    exact (CrossingLabels.subquotient_zero_iff _ _ _).mpr (by
      change x-u ∈ boundaries background X (1+t-(t-k)) (s,t)
      convert hxu using 1
      congr 1
      omega)
  exact detects_sub_filtration (background.convergence (.quotient q (.nu X)))
    (s,t,t-k) ⟨ex,hx,ar,har,hae⟩
    ⟨ex,hx,br,hbr,by rw [heq]; exact hbe⟩

private theorem middle_positive_h_one_step
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (k q : ℕ) (hq : 0<q) (s t : ℤ)
    (hmid : ∀ x : Ambient background T.X (s+1,t), x ∈ cycles background T.X q (s+1,t) →
      ∃ z : Ambient background T.Z (s,t), z ∈ cycles background T.Z q (s,t) ∧
      ∃ u : Ambient background T.X (s+1,t),
        (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
          (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s+1,t))
    (a : BiHom (t-s) (t-k)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (k+q)))
    (ha : FiltrationAtLeast background.syntheticTower (s+1)
      (a ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (k+q))) :
    ∃ b : BiHom (t-s) (t-k)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (k+q)),
      FiltrationAtLeast background.syntheticTower (s+2)
        (b ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (k+q)) ∧
      b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (k+q)=
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (k+q) := by
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) (k+q)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  let an := positiveHSourceDesuspend T he hf (k+q) k s t ε a
  have han : FiltrationAtLeast background.syntheticTower (s+1) an :=
    (middle_positive_g_native_filtration_iff T he hf (k+q) k s t (s+1) ε a).mpr ha
  obtain ⟨x,hxc,hxd⟩ := middle_finite_filtration_label T.X (k+q) k (by omega)
    (s+1) t an han
  obtain ⟨z,hz,u,hu,hxu⟩ := hmid x (by simpa only [Nat.add_sub_cancel_left] using hxc)
  obtain ⟨b,hb,hbz⟩ := middle_positive_h_cycle_image T he hf hg hh hT k q hq
    s t z hz u hu ε hε
  have hnext := middle_finite_congruent_difference T.X (k+q) k (by omega)
    (s+1) t x u hxu an (positiveHSourceDesuspend T he hf (k+q) k s t ε b) hxd hb
  refine ⟨a-b,?_,?_⟩
  · apply (middle_positive_g_native_filtration_iff T he hf (k+q) k s t (s+2) ε (a-b)).mp
    rw [positive_h_source_desuspend_sub]
    simpa only [an,show (s+1)+1=s+2 by omega] using hnext
  · rw [Preadditive.sub_comp,hbz,sub_zero]

private theorem middle_positive_h_one_step_regraded
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (N k q : ℕ) (hq : 0<q) (hN : N=k+q) (s t m w : ℤ)
    (hm : m=t-s) (hw : w=t-k)
    (hmid : ∀ x : Ambient background T.X (s+1,t), x ∈ cycles background T.X q (s+1,t) →
      ∃ z : Ambient background T.Z (s,t), z ∈ cycles background T.Z q (s,t) ∧
      ∃ u : Ambient background T.X (s+1,t),
        (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
          (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
          (by simpa only [add_sub_cancel_right] using u) ∧
        x-u ∈ boundaries background T.X (k+1) (s+1,t))
    (a : BiHom m w
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (ha : FiltrationAtLeast background.syntheticTower (s+1)
      (a ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom N)) :
    ∃ b : BiHom m w
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N),
      FiltrationAtLeast background.syntheticTower (s+2)
        (b ≫ XModLambdaN.map (middlePositiveGTargetIso T he hf).hom N) ∧
      b ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) N=
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) N := by
  subst N; subst m; subst w
  exact middle_positive_h_one_step T he hf hg hh hT k q hq s t hmid a ha

/-- In the positive-h branch the complete middle condition corrects the
same finite representative to the last layer, using the actual positive
first-quotient h operation at every step. -/
private theorem middle_positive_h_residual_same_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2≤K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ x : Ambient background T.X (S+j-1+1,V+j),
        x ∈ cycles background T.X ((K:ℤ)-j) (S+j-1+1,V+j) →
        ∃ z : Ambient background T.Z (S+j-1,V+j),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j-1,V+j) ∧
        ∃ u : Ambient background T.X (S+j-1+1,V+j),
          (background.classicalSuspension T.X).DesuspendsClass (S+j-1+1) (V+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (S+j-1) (V+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((c:ℤ)+j+1) (S+j-1+1,V+j))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (a : BiHom (V-(S-1)) (V-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1)
      (positiveHSourceDesuspend T he hf (c+K) c (S-1) V ε a)) :
    ∃ e : BiHom (V-(S-1)) (V-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)),
      FiltrationAtLeast background.syntheticTower (S+K-1)
        (positiveHSourceDesuspend T he hf (c+K) c (S-1) V ε e) ∧
      e ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+K)=
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle background T he).mor₁) (c+K) := by
  let A := XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)
  let d := XModLambdaN.map (middlePositiveGTargetIso T he hf).hom (c+K)
  let f := XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
    (normalizedTriangle background T he).mor₁) (c+K)
  have hstep (j : ℕ) (hj : 1≤j) (hjK : j<K-1)
      (a : BiHom (V-(S-1)) (V-c) A)
      (ha : FiltrationAtLeast background.syntheticTower (S+j) (a≫d)) :
      ∃ b : BiHom (V-(S-1)) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+(j+1:ℕ)) (b≫d) ∧ b≫f=a≫f := by
    have H := middle_positive_h_one_step_regraded T he hf hg hh hT
      (c+K) (c+j) (K-j) (by omega) (by omega)
      (S+j-1) (V+j) (V-(S-1)) (V-c) (by omega) (by omega)
      (by
        simpa only [Nat.cast_sub (show j≤K by omega),Nat.cast_add,Nat.cast_one]
          using hmid j hj hjK) a
    obtain ⟨b,hb,hi⟩ := H (by simpa only [sub_add_cancel] using ha)
    refine ⟨b,?_,hi⟩
    have hs : (S+(j:ℤ)-1)+2=S+(j+1:ℕ) := by omega
    simpa only [hs] using hb
  have hrec (j : ℕ) (hj : 1≤j) (hjK : j≤K-1)
      (a : BiHom (V-(S-1)) (V-c) A)
      (ha : FiltrationAtLeast background.syntheticTower (S+j) (a≫d)) :
      ∃ e : BiHom (V-(S-1)) (V-c) A,
        FiltrationAtLeast background.syntheticTower (S+K-1) (e≫d) ∧ e≫f=a≫f := by
    induction hlen : K-1-j using Nat.strong_induction_on generalizing j a with
    | h n ih =>
      by_cases hend : K-1≤j
      · refine ⟨a,?_,rfl⟩
        convert ha using 1
        omega
      · obtain ⟨b,hb,hi⟩ := hstep j hj (by omega) a ha
        obtain ⟨e,he,hei⟩ := ih (K-1-(j+1)) (by omega) (j+1)
          (by omega) (by omega) b hb rfl
        exact ⟨e,he,hei.trans hi⟩
  have ha' := (middle_positive_g_native_filtration_iff T he hf (c+K) c
    (S-1) V (S+1) ε a).mp ha
  obtain ⟨e,hefil,heimage⟩ := hrec 1 (by omega) (by omega) a (by simpa only [Nat.cast_one] using ha')
  exact ⟨e,(middle_positive_g_native_filtration_iff T he hf (c+K) c
    (S-1) V (S+K-1) ε e).mpr hefil,heimage⟩

/-- General positive-h middle conditions and the last ordinary f boundary
condition annihilate every higher finite ambiguity. -/
private theorem middle_positive_h_raw_annihilation
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (c K : ℕ) (hK : 2 ≤ K) (S V : ℤ)
    (hmid : ∀ j : ℕ, 1≤j → j<K-1 →
      ∀ x : Ambient background T.X (S+j-1+1,V+j),
        x ∈ cycles background T.X ((K:ℤ)-j) (S+j-1+1,V+j) →
        ∃ z : Ambient background T.Z (S+j-1,V+j),
          z ∈ cycles background T.Z ((K:ℤ)-j) (S+j-1,V+j) ∧
        ∃ u : Ambient background T.X (S+j-1+1,V+j),
          (background.classicalSuspension T.X).DesuspendsClass (S+j-1+1) (V+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              (S+j-1) (V+j) z) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((c:ℤ)+j+1) (S+j-1+1,V+j))
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) (c+K) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (c+K)))
    (hε : XModLambdaN.incl _ (c+K) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+K)))
    (hlast : ∀ x : Ambient background T.X (S+K-1,V+K-1),
      (background.classical.map T.f).pageMap 2 (S+K-1,V+K-1) x ∈
        boundaries background T.Y (c+K) (S+K-1,V+K-1))
    (a : BiHom (V-(S-1)) (V-c)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) (c+K)))
    (ha : FiltrationAtLeast background.syntheticTower (S+1)
      (positiveHSourceDesuspend T he hf (c+K) c (S-1) V ε a)) :
    a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) (c+K) = 0 := by
  obtain ⟨e,hefil,heimage⟩ := middle_positive_h_residual_same_image
    T he hf hg hh hT c K hK S V hmid ε a ha
  let en := positiveHSourceDesuspend T he hf (c+K) c (S-1) V ε e
  let b := homotopyRegrade (show V-(S-1+1)=(V+K-1)-(S+K-1) by omega) rfl en
  have hb : FiltrationAtLeast background.syntheticTower (S+K-1) b :=
    (regrade_filtration_iff _ _ _ _).mpr hefil
  have hz := ordinary_map_top_filtration_zero T.X T.Y T.f (c+K) (by omega)
    (S+K-1) (V+K-1) (V-c) (by omega) hlast b hb
  have henz : en ≫ XModLambdaN.map (background.nu.functor.map T.f) (c+K)=0 := by
    apply (ordinary_regrade_zero_iff (show V-(S-1+1)=(V+K-1)-(S+K-1) by omega) rfl _).mp
    simpa only [b,regrade_comp] using hz
  have heraw := native_ordinary_image_zero_implies_raw_zero T he hf (c+K) c (by omega)
    (S-1) V ε hε e henz
  exact heimage.symm.trans heraw

/-- The actual ordinary image square also reflects zero from the raw
suspended representative to its fixed native ν-coordinate. -/
private theorem middle_raw_ordinary_image_zero_implies_native_zero
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (N k : ℕ) (hN : 0<N) (s t : ℤ)
    (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (background.nu.functor.obj (T.X.obj background.auxiliary))) N ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) N))
    (hε : XModLambdaN.incl _ N ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ N))
    (a : BiHom (t-s) (t-k)
      (XModLambdaN ((normalizedTriangle background T he).obj₁⟦(1:ℤ)⟧) N))
    (hz : a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle background T he).mor₁) N=0) :
    positiveHSourceDesuspend T he hf N k s t ε a ≫
      XModLambdaN.map (background.nu.functor.map T.f) N=0 := by
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (background.nu.functor.obj (T.Y.obj background.auxiliary)) N
  have h := native_ordinary_image_eq_raw_image T he hf N k hN s t ε hε ey hey a
  rw [←Category.assoc,hz,zero_comp] at h
  rw [ordinary_suspended_eq_source_iso] at h
  have hm : (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
        (positiveHSourceDesuspend T he hf N k s t ε a ≫
          XModLambdaN.map (background.nu.functor.map T.f) N))=0 := by
    apply (cancel_epi (ordinarySphereIso (t-s) (t-k)).hom).mp
    simpa only [comp_zero] using h.symm
  have hr : homotopyRegrade (show t-(s+1)=(t-s)-1 by omega) rfl
      (positiveHSourceDesuspend T he hf N k s t ε a ≫
        XModLambdaN.map (background.nu.functor.map T.f) N)=0 := by
    apply (shiftFunctor SyntheticSpectrum (1:ℤ)).map_injective
    simpa only [Functor.map_zero] using hm
  exact (ordinary_regrade_zero_iff (show t-(s+1)=(t-s)-1 by omega) rfl _).mp hr

/-- The positive-h finite image in native νX coordinates. Its detected
class is the specified positive H label and its actual νf-image is zero. -/
private theorem middle_positive_h_native_cycle_image
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=0)
    (hh : normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (k q : ℕ) (hq : 0<q) (s t : ℤ)
    (z : Ambient background T.Z (s,t))
    (hz : z ∈ cycles background T.Z q (s,t))
    (u : Ambient background T.X (s+1,t))
    (hu : (background.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) s t z)
      (by simpa only [add_sub_cancel_right] using u)) :
    ∃ b : BiHom (t-(s+1)) (t-k)
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (k+q)),
      Detects (background.convergence (.quotient (k+q) (.nu T.X))) (s+1,t,t-k)
        (finiteTargetLabel background T.X (k+q) (s+1) t k u) b ∧
      b ≫ XModLambdaN.map (background.nu.functor.map T.f) (k+q)=0 := by
  letI := background.exactness.shiftCommShift (1,0)
  letI := background.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists background.quotients.coherence (1,0) (k+q)
    (background.nu.functor.obj (T.X.obj background.auxiliary))
  obtain ⟨a,ha,haz⟩ := middle_positive_h_cycle_image T he hf hg hh hT
    k q hq s t z hz u hu ε hε
  exact ⟨positiveHSourceDesuspend T he hf (k+q) k s t ε a,ha,
    middle_raw_ordinary_image_zero_implies_native_zero T he hf (k+q) k (by omega)
      s t ε hε a haz⟩

end
end KIP126.ProofTools.Internal.SyntheticCoverage
