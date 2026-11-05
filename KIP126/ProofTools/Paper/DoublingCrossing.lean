module
import all KIP126.ProofTools.Paper.DoublingNumericalExtensions
import all KIP126.ProofTools.Paper.Crossing

/-! Crossing and inessentiality for the actual multiplication-by-two map.
The zero target below means zero in the specified associated grade. -/
@[expose] section
namespace KIP126.ProofTools.Paper.DoublingCrossing
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
open KIP126.ProofTools.Paper.NumericalExamples
open KIP126.ProofTools.Paper.NuNumericalExtensions
open KIP126.ProofTools.Paper.DoublingNumericalExtensions
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem infinite_target_zero (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (n s t : ℤ)
    (hn : normalizedExponent background.classicalTower f≤n) :
    infiniteTargetForExtension background X Y f n s t hn 0=0 := by
  have h := infinite_target_nuWeight_heq X Y f n s t hn 0
  rw [nu_weight_zero_label] at h
  have H (i j : Tridegree) (hij : i=j) :
      HEq (0 : (background.family.obj (background.nu.functor.obj (Y.obj background.auxiliary))).E₂ i)
        (0 : (background.family.obj (background.nu.functor.obj (Y.obj background.auxiliary))).E₂ j) := by
    subst j
    rfl
  apply eq_of_heq
  exact h.trans (H _ _ (by ext <;> dsimp; omega))

/-- The two full relations have the same prescribed source infinity class.
Consequently every length-two witness with target h0d0 is inessential. -/
private theorem paper6_8_long_inessential
    (W : InfiniteExtensionWitness background .sphere .sphere twoMap 2 3 17 h0h3Square h0d0) :
    ¬W.Essential := by
  obtain ⟨W0⟩ := paper6_8_long_zero_extension
  have hsource : W.source=W0.source := W.source_rep.unique W0.source_rep
  have hrep := W0.target_rep
  rw [infinite_target_zero .sphere .sphere twoMap 2 3 17 W0.length_lower] at hrep
  have htarget : W0.target=0 := hrep.unique
    (HasInfinityRepresentative.zero _ 2 (by decide) _)
  have hzero := W0.equation
  rw [←hsource,htarget] at hzero
  intro hess
  exact ((tower_essential_iff_no_zero
    (E:=background.family) (P:=background.syntheticTower)
    (cx:=background.convergence (extensionSourceObject background .sphere .sphere twoMap))
    (cy:=background.convergence (.nu .sphere))
    (background.convergentMap (extensionSourceObject background .sphere .sphere twoMap) (.nu .sphere)
      (background.normalizedMap .sphere .sphere twoMap).map)
    (17-3,17+normalizedExponent background.classicalTower twoMap) 3 2
    W.source W.target W.equation).mp hess) hzero

private theorem paper6_8_inessential_extension :
    ∃ W : InfiniteExtensionWitness background .sphere .sphere twoMap 2 3 17 h0h3Square h0d0,
      ¬W.Essential := by
  obtain ⟨W⟩ := paper6_8_long_nonzero_extension
  exact ⟨W,paper6_8_long_inessential W⟩


private theorem h0d0_not_second_boundaries :
    h0d0∉boundaries background .sphere 2 (5,19) :=
  KIP126.ProofTools.Paper.nonzero_differential_target_not_boundary .sphere 3 2
    (2,17) (5,19) (by decide) (by decide)
    (KIP126.Literature.Standard.hiProduct 0 4) h0d0 paper6_8_classical_d3

/-- The paper's displacement-one crossing, retaining the required B2
exclusion for the shorter target. -/
private theorem paper6_8_has_paper_crossing :
    InfiniteHasCrossing background .sphere .sphere twoMap 2 3 17 := by
  obtain ⟨W,hess⟩ := paper6_8_short_essential
  refine ⟨1,0,by decide,?_,?_,d0,h0d0,W,hess,?_⟩
  · rw [twoMap_exponent]
    norm_num
  · rw [twoMap_exponent]
    norm_num
  · change h0d0∉boundaries background .sphere
      (1+2-(0:ℕ)-normalizedExponent background.classicalTower twoMap) (5,19)
    have hi : (1+2-(0:ℕ)-normalizedExponent background.classicalTower twoMap : ℤ)=2 := by
      rw [twoMap_exponent]
      norm_num
    rw [hi]
    exact h0d0_not_second_boundaries

private theorem infinite_target_nonzero_of_not_boundary (X Y : AdamsObject (coefficients := background.coefficients))
    (f : X.obj background.auxiliary ⟶ Y.obj background.auxiliary) (n s t : ℤ)
    (x : Ambient background X (s,t)) (y : Ambient background Y (s+n,t+n))
    (W : InfiniteExtensionWitness background X Y f n s t x y)
    (hy : y∉boundaries background Y (1+n-normalizedExponent background.classicalTower f) (s+n,t+n)) :
    W.target≠0 := by
  intro hz
  have hi : (s+n,(t-s)+(s+n),t+normalizedExponent background.classicalTower f)=
      (s+n,t+n,t+normalizedExponent background.classicalTower f) := by
    ext <;> dsimp; omega
  have hr := representative_transport hi _ _ W.target_rep
  have hlabel : regradeE2 hi (infiniteTargetForExtension background X Y f n s t W.length_lower y)=
      nuWeightLabel background Y (s+n) (t+n) (t+normalizedExponent background.classicalTower f)
        (by have := W.length_lower; omega) y := by
    exact eq_of_heq ((regradeE2_heq hi _).trans
      (infinite_target_nuWeight_heq X Y f n s t W.length_lower y))
  rw [hlabel] at hr
  have hc := (KIP126.Literature.Standard.eInfinity_nu_labels Y (s+n) (t+n)
    (t+normalizedExponent background.classicalTower f) (by have := W.length_lower; omega) y _).mp hr
  have hb : y∈boundaries background Y (1+(t+n)-(t+normalizedExponent background.classicalTower f))
      (s+n,t+n) := by
    apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hc.1⟩).mp
    rw [←hc.2]
    simp only [hz,map_zero]
  exact hy (by convert hb using 1; congr 1; omega)


private theorem paper6_8_long_target_nonzero
    (W : InfiniteExtensionWitness background .sphere .sphere twoMap 2 3 17 h0h3Square h0d0) :
    W.target≠0 := by
  apply infinite_target_nonzero_of_not_boundary .sphere .sphere twoMap 2 3 17
    h0h3Square h0d0 W
  have hi : (1+2-normalizedExponent background.classicalTower twoMap : ℤ)=2 := by
    rw [twoMap_exponent]
    norm_num
  rw [hi]
  exact h0d0_not_second_boundaries

/-- The inessential relation has a genuinely nonzero specified infinity
output; inessentiality concerns source ambiguity. -/
private theorem paper6_8_nonzero_inessential_output :
    ∃ W : InfiniteExtensionWitness background .sphere .sphere twoMap 2 3 17 h0h3Square h0d0,
      ¬W.Essential ∧ W.target≠0 := by
  obtain ⟨W⟩ := paper6_8_long_nonzero_extension
  exact ⟨W,paper6_8_long_inessential W,paper6_8_long_target_nonzero W⟩


private theorem lambda_multiply_preserves_filtration
    (A : SyntheticObject (coefficients := background.coefficients)) (m w s : ℤ) (k : ℕ)
    (a : BiHom m w (A.obj background.nu background.auxiliary))
    (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (lambdaMultiply k a) := by
  obtain ⟨c,hc⟩ := ha
  change c≫(background.syntheticTower.tower _).projection s=a at hc
  refine ⟨lambdaMultiply k c,?_⟩
  change lambdaMultiply k c≫(background.syntheticTower.tower _).projection s=lambdaMultiply k a
  rw [←hc]
  simp only [lambdaMultiply,Category.assoc]

/-- A lambda-lowered relation is essential when its target label
is nonzero in the lower-weight infinity window. -/
private theorem lowered_relation_essential_with_ncc
    (X Y : AdamsObject (coefficients := background.coefficients)) (e : ℕ)
    (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)) ⟶
        background.nu.functor.obj (Y.obj background.auxiliary))
    (m w s n : ℤ) (k : ℕ) (hn0 : 0≤n)
    (a : BiHom m w ((SyntheticCategory.biShift (0,(e:ℤ))).obj (background.nu.functor.obj (X.obj background.auxiliary))))
    (b : BiHom m w (background.nu.functor.obj (Y.obj background.auxiliary)))
    (ha : FiltrationAtLeast background.syntheticTower s a)
    (hab : a≫F=b)
    (y : Ambient background Y (s+n,m+(s+n)))
    (hw : w-(k:ℤ)≤m+(s+n))
    (hb : Detects (background.convergence (.nu Y)) (s+n,m+(s+n),w-k)
      (nuWeightLabel background Y (s+n) (m+(s+n)) (w-k) hw y)
      (homotopyRegrade (by dsimp; omega) rfl (lambdaMultiply k b)))
    (hy : y∉boundaries background Y (1+(m+(s+n))-(w-k)) (s+n,m+(s+n)))
    (hnc : TowerNoCrossing (background.convergentMap (.shift (0,(e:ℤ)) (.nu X)) (.nu Y) F)
      (m,w-k) s n) :
    ∃ source target,
      HasInfinityRepresentative _ 2 (s+n,m+(s+n),w-k)
        (nuWeightLabel background Y (s+n) (m+(s+n)) (w-k) hw y) target ∧
      TowerEssentialExtension (F:=background.family) (P:=background.syntheticTower)
        (cx:=background.convergence (.shift (0,(e:ℤ)) (.nu X))) (cy:=background.convergence (.nu Y))
        (background.convergentMap (.shift (0,(e:ℤ)) (.nu X)) (.nu Y)
        F) (m,w-k) s n source target ∧
      ∃ ar : (Subobject.underlying.obj ((background.syntheticTower.filtration
          ((SyntheticCategory.biShift (0,(e:ℤ))).obj (background.nu.functor.obj (X.obj background.auxiliary)))).F s (m,w-k)) : ModuleCat.{0} ℤ),
        ((background.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj (background.nu.functor.obj (X.obj background.auxiliary)))).F s (m,w-k)).arrow ar=lambdaMultiply k a ∧
        (background.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj (background.nu.functor.obj (X.obj background.auxiliary)))).toAssociatedGraded s (m,w-k) ar=
          (infinityGradedIso (background.convergence (.shift (0,(e:ℤ)) (.nu X))) (m,w-k) s).hom source := by
  let AS : SyntheticObject (coefficients := background.coefficients) := .shift (0,(e:ℤ)) (.nu X)
  let SF := background.syntheticTower.filtration (AS.obj background.nu background.auxiliary)
  have haLow := lambda_multiply_preserves_filtration AS m w s k a ha
  obtain ⟨ar,har⟩ := filtration_representative_exists background.syntheticTower
    (AS.obj background.nu background.auxiliary) (m,w-k) s (lambdaMultiply k a) haLow
  let source := (infinityGradedIso (background.convergence AS) (m,w-k) s).inv
    (SF.toAssociatedGraded s (m,w-k) ar)
  have hsource : SF.toAssociatedGraded s (m,w-k) ar=
      (infinityGradedIso (background.convergence AS) (m,w-k) s).hom source := by
    exact ((infinityGradedIso (background.convergence AS) (m,w-k) s).toLinearEquiv.apply_symm_apply _).symm
  obtain ⟨target,htarget,br,hbr,hgr⟩ := frame_of_source_detects
    (background.convergence (.nu Y)) (m,w-k) (s+n) _ (lambdaMultiply k b) hb
  have habLow : lambdaMultiply k a≫F=lambdaMultiply k b := by
    rw [←hab]
    simp only [lambdaMultiply,Category.assoc]
  have he : TowerExtensionEquation (background.convergentMap AS (.nu Y)
      F) (m,w-k) s n source target := by
    apply (tower_extension_iff _ _ _ _ _ _).mpr
    exact ⟨hn0,ar,br,by rw [har,hbr]; exact habLow,hsource,hgr⟩
  have htne : target≠0 := by
    intro hz
    obtain ⟨hyp,hwindow⟩ := (KIP126.Literature.Standard.eInfinity_nu_labels Y
      (s+n) (m+(s+n)) (w-k) hw y target).mp htarget
    apply hy
    apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hyp⟩).mp
    rw [←hwindow,hz,map_zero]
  refine ⟨source,target,htarget,?_,ar,har,hsource⟩
  exact (tower_essential_iff_target_nonzero_of_no_crossing
    (E:=background.family) (P:=background.syntheticTower)
    (cx:=background.convergence AS) (cy:=background.convergence (.nu Y))
    (background.convergentMap AS (.nu Y) F)
    (m,w-k) s n source target he hnc).mpr htne

private def specificLoweredCrossAt
    (e : ℕ) (he : e=1)
    (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
      (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) ⟶
        background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) : Prop :=
  ∃ a : BiHom 14 19 ((SyntheticCategory.biShift (0,(e:ℤ))).obj
      (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary))),
    ∃ b : BiHom 14 19 (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)),
      ∃ source target,
        Detects (background.convergence (.shift (0,(e:ℤ)) (.nu .sphere))) (4,18,19)
          (regradeE2 (by rw [he]; norm_num)
            (background.comparison.nuE2 .sphere e 4 18 0 d0)) a ∧
        a≫F=b ∧
        HasInfinityRepresentative _ 2 (5,19,18)
          (nuWeightLabel background .sphere 5 19 18 (by decide) h0d0) target ∧
        TowerEssentialExtension (F:=background.family) (P:=background.syntheticTower)
          (cx:=background.convergence (.shift (0,(e:ℤ)) (.nu .sphere))) (cy:=background.convergence (.nu .sphere))
          (background.convergentMap (.shift (0,(e:ℤ)) (.nu .sphere))
          (.nu .sphere) F) (14,18) 4 1 source target ∧
        ∃ ar : (Subobject.underlying.obj ((background.syntheticTower.filtration
          ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)))).F 4 (14,18)) : ModuleCat.{0} ℤ),
          ((background.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)))).F 4 (14,18)).arrow ar=
              lambdaMultiply 1 a ∧
          (background.syntheticTower.filtration ((SyntheticCategory.biShift (0,(e:ℤ))).obj
            (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)))).toAssociatedGraded 4 (14,18) ar=
            (infinityGradedIso (background.convergence (.shift (0,(e:ℤ)) (.nu .sphere))) (14,18) 4).hom source

private theorem paper6_8_lowered_positive_crossing :
    specificLoweredCrossAt 1 rfl selectedTwoNormalized := by
  have hncActual := minimal_length_full_nu_tower_no_crossing .sphere .sphere twoMap
    (14,18) 4 1 (by rw [twoMap_exponent]; norm_num)
  have transportNCC (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) ⟶
          background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) :
      TowerNoCrossing (background.convergentMap (.shift (0,(e:ℤ)) (.nu .sphere))
        (.nu .sphere) F) (14,18) 4 1 →
        TowerNoCrossing (background.convergentMap (.shift (0,1) (.nu .sphere))
          (.nu .sphere) (by
            change (SyntheticCategory.biShift (0,1)).obj
              (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) ⟶
                background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)
            simpa only [he,Nat.cast_one] using F)) (14,18) 4 1 := by
    subst e
    exact id
  have hnc := transportNCC _ twoMap_exponent (background.normalizedMap .sphere .sphere twoMap).map hncActual
  change TowerNoCrossing (background.convergentMap (.shift (0,1) (.nu .sphere)) (.nu .sphere)
    (normalizedMapInPositiveCoordinates .sphere .sphere twoMap twoMap_exponent)) (14,18) 4 1 at hnc
  rw [←selectedTwoNormalized_eq_positive] at hnc
  obtain ⟨D,hD⟩ := d0_full_lift
  let a : BiHom 14 19 ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary))) :=
    shiftHomotopyClass (0,1) (14,18) D
  let b : BiHom 14 19 (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) :=
    a≫selectedTwoNormalized
  have hdPerm := permanent_member_of_cycle .sphere (4,18) d0 (every_d0_degree_label_permanent d0)
  have has := positive_shift_full_source_detects .sphere 4 18 d0 hdPerm D hD
  have hafil := detects_filtration (.shift (0,1) (.nu .sphere)) (4,18,19) _ a has
  have hbfirst := d0_positive_normalized_image D hD
  have hbperm := first_label_lift_permanent .sphere 5 19 h0d0 b hbfirst
  have hbt := nu_lambda_detects .sphere 1 (by decide) 5 19 h0d0 hbperm b hbfirst
  have hboundary : h0d0∉boundaries background .sphere 2 (5,19) :=
    KIP126.ProofTools.Paper.nonzero_differential_target_not_boundary .sphere 3 2
      (2,17) (5,19) (by decide) (by decide)
      (KIP126.Literature.Standard.hiProduct 0 4) h0d0 paper6_8_classical_d3
  obtain ⟨source,target,htarget,hess,ar,har,hgr⟩ := lowered_relation_essential_with_ncc
    .sphere .sphere 1 selectedTwoNormalized 14 19 4 1 1 (by decide)
    a b hafil rfl h0d0 (by decide)
    (by
      change Detects (background.convergence (.nu .sphere)) (5,19,18)
        (nuWeightLabel background .sphere 5 19 18 (by decide) h0d0) (lambdaMultiply 1 b)
      exact hbt) hboundary hnc
  exact ⟨a,b,source,target,has,rfl,htarget,hess,ar,har,hgr⟩

private theorem paper6_8_lowered_actual_crossing :
    specificLoweredCrossAt (normalizedExponent background.classicalTower twoMap) twoMap_exponent
      (background.normalizedMap .sphere .sphere twoMap).map := by
  have transport (e : ℕ) (he : e=1)
      (F : (SyntheticCategory.biShift (0,(e:ℤ))).obj
        (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) ⟶
          background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) :
      specificLoweredCrossAt 1 rfl (by simpa only [he,Nat.cast_one] using F) →
        specificLoweredCrossAt e he F := by
    subst e
    exact id
  apply transport _ twoMap_exponent (background.normalizedMap .sphere .sphere twoMap).map
  change specificLoweredCrossAt 1 rfl
    (normalizedMapInPositiveCoordinates .sphere .sphere twoMap twoMap_exponent)
  rw [←selectedTwoNormalized_eq_positive]
  exact paper6_8_lowered_positive_crossing


end
end KIP126.ProofTools.Paper.DoublingCrossing