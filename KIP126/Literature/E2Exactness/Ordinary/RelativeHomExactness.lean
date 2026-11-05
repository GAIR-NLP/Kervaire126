module
import all KIP126.Literature.E2Exactness.Ordinary.FixedTensorComplex
import all KIP126.Literature.E2Exactness.Ordinary.E2MapComparison

@[expose] section
namespace KIP126.Literature.Standard.ShiftedResolutionExact
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Completed
open KIP126.Literature.Standard.FixedTensorE2 KIP126.Literature.Standard.E2MapComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem mapped_yoneda_exact₂ (T : Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (n : ℤ) {J : Spectrum}
    (e : T.obj₂⟦n⟧ ⟶ J)
    (he : (shiftFunctor Spectrum n).map T.mor₁ ≫ e = 0) :
    ∃ q : T.obj₃⟦n⟧ ⟶ J, e = (shiftFunctor Spectrum n).map T.mor₂ ≫ q := by
  let F := shiftFunctor Spectrum n
  let i := F.objObjPreimageIso J
  let g := F.preimage (e ≫ i.inv)
  have hg : F.map g = e ≫ i.inv := F.map_preimage _
  have hz : T.mor₁ ≫ g = 0 := by
    apply F.map_injective
    rw [Functor.map_comp, hg, ← Category.assoc, he, zero_comp, Functor.map_zero]
  obtain ⟨q,hq⟩ := T.yoneda_exact₂ hT g hz
  refine ⟨F.map q ≫ i.hom, ?_⟩
  apply (cancel_mono i.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hg, hq, Functor.map_comp]

private theorem mapped_yoneda_exact₃ (T : Triangle Spectrum)
    (hT : T ∈ distTriang Spectrum) (n : ℤ) {J : Spectrum}
    (e : T.obj₃⟦n⟧ ⟶ J)
    (he : (shiftFunctor Spectrum n).map T.mor₂ ≫ e = 0) :
    ∃ q : (T.obj₁⟦(1:ℤ)⟧)⟦n⟧ ⟶ J,
      e = (shiftFunctor Spectrum n).map T.mor₃ ≫ q :=
  mapped_yoneda_exact₂ T.rotate (rot_of_distTriang T hT) n e he

private def stepTriangleAt {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) : Triangle Spectrum :=
  Triangle.mk (T.mapAt (show s ≤ s+1 by omega))
    (HasFunctorialCofiber.cofibι (T.mapAt (show s ≤ s+1 by omega)))
    (HasFunctorialCofiber.cofibδ (T.mapAt (show s ≤ s+1 by omega)))

private theorem stepTriangleAt_distinguished {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) :
    stepTriangleAt T s ∈ distTriang Spectrum := HasFunctorialCofiber.cofib_distinguished _

private theorem stepAt_tensor_zero {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) (hs : 0 ≤ s) :
    coefficients.object ◁ T.mapAt (show s ≤ s+1 by omega) = 0 := by
  lift s to ℕ using hs
  exact HUnitConsequences.actual_adams_step_tensor_zero T s

private theorem into_shifted_layer_annihilates {A B Y : Spectrum}
    (U : AbstractAdamsTower coefficients.unit Y) (k m : ℤ)
    (f : A ⟶ B) (hf : coefficients.object ◁ f = 0)
    (g : B ⟶ (U.layer k)⟦m⟧) : f ≫ g = 0 := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    exact shifted_layer_annihilates U k m f hf g
  · exact ((shiftFunctor Spectrum m).map_isZero
      (layer_negative_isZero U k (by omega))).eq_of_tgt _ _

private def shiftedInclusion {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) :
    (T.stageAt s)⟦s⟧ ⟶ (T.layer s)⟦s⟧ :=
  (shiftFunctor Spectrum s).map
    (HasFunctorialCofiber.cofibι (T.mapAt (show s ≤ s+1 by omega)))

private def shiftedConnecting {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) :
    (T.layer s)⟦s⟧ ⟶ (T.stageAt (s+1))⟦s+1⟧ :=
  (shiftFunctor Spectrum s).map
    (HasFunctorialCofiber.cofibδ (T.mapAt (show s ≤ s+1 by omega))) ≫
    (shiftFunctorAdd' Spectrum (1:ℤ) s (s+1) (by omega)).inv.app (T.stageAt (s+1))

private theorem shiftedDifferential_eq {X : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X) (s : ℤ) :
    shiftedLayerDifferential T s = shiftedConnecting T s ≫ shiftedInclusion T (s+1) := by
  dsimp only [shiftedLayerDifferential, layerBoundary, shiftedConnecting, shiftedInclusion]
  rw [Functor.map_comp]
  simpa only [AbstractAdamsTower.layer, Functor.comp_map, Category.assoc] using congrArg
    (fun z => (shiftFunctor Spectrum s).map
      (HasFunctorialCofiber.cofibδ (T.mapAt (show s ≤ s+1 by omega))) ≫ z)
    ((shiftFunctorAdd' Spectrum (1:ℤ) s (s+1) (by omega)).inv.naturality
      (HasFunctorialCofiber.cofibι (T.mapAt (show s+1 ≤ s+1+1 by omega))))

private theorem factor_through_next_layer {X Y : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X)
    (U : AbstractAdamsTower coefficients.unit Y) (s k m : ℤ) (hs : 0 ≤ s+1)
    (e : (T.layer s)⟦s⟧ ⟶ (U.layer k)⟦m⟧)
    (he : shiftedInclusion T s ≫ e = 0) :
    ∃ q : (T.layer (s+1))⟦s+1⟧ ⟶ (U.layer k)⟦m⟧,
      shiftedLayerDifferential T s ≫ q = e := by
  obtain ⟨v,hv⟩ := mapped_yoneda_exact₃ (stepTriangleAt T s)
    (stepTriangleAt_distinguished T s) s e he
  let c := (shiftFunctorAdd' Spectrum (1:ℤ) s (s+1) (by omega)).app (T.stageAt (s+1))
  let v' := c.hom ≫ v
  have hz : (shiftFunctor Spectrum (s+1)).map (stepTriangleAt T (s+1)).mor₁ ≫ v' = 0 :=
    into_shifted_layer_annihilates U k m _
      (shifted_tensor_zero _ (stepAt_tensor_zero T (s+1) hs) (s+1)) v'
  obtain ⟨q,hq⟩ := mapped_yoneda_exact₂ (stepTriangleAt T (s+1))
    (stepTriangleAt_distinguished T (s+1)) (s+1) v' hz
  refine ⟨q, ?_⟩
  rw [shiftedDifferential_eq, Category.assoc]
  change shiftedConnecting T s ≫
    ((shiftFunctor Spectrum (s+1)).map (stepTriangleAt T (s+1)).mor₂ ≫ q) = e
  rw [← hq]
  change ((shiftFunctor Spectrum s).map (stepTriangleAt T s).mor₃ ≫ c.inv) ≫
    (c.hom ≫ v) = e
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hv.symm

private theorem relative_exact_zero {X Y : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X)
    (U : AbstractAdamsTower coefficients.unit Y) (k m : ℤ)
    (e : (T.layer 0)⟦(0:ℤ)⟧ ⟶ (U.layer k)⟦m⟧)
    (he : shiftedInclusion T 0 ≫ e = 0) :
    ∃ q : (T.layer 1)⟦(1:ℤ)⟧ ⟶ (U.layer k)⟦m⟧,
      shiftedLayerDifferential T 0 ≫ q = e :=
  factor_through_next_layer T U 0 k m (by omega) e he

private theorem relative_exact_succ {X Y : Spectrum}
    (T : AbstractAdamsTower coefficients.unit X)
    (U : AbstractAdamsTower coefficients.unit Y) (s k m : ℤ) (hs : 0 ≤ s)
    (e : (T.layer (s+1))⟦s+1⟧ ⟶ (U.layer k)⟦m⟧)
    (he : shiftedLayerDifferential T s ≫ e = 0) :
    ∃ q : (T.layer (s+1+1))⟦s+1+1⟧ ⟶ (U.layer k)⟦m⟧,
      shiftedLayerDifferential T (s+1) ≫ q = e := by
  apply factor_through_next_layer T U (s+1) k m (by omega) e
  let c := (shiftFunctorAdd' Spectrum (1:ℤ) s (s+1) (by omega)).app (T.stageAt (s+1))
  let g := c.inv ≫ shiftedInclusion T (s+1) ≫ e
  have hgδ : (shiftFunctor Spectrum s).map (stepTriangleAt T s).mor₃ ≫ g = 0 := by
    rw [shiftedDifferential_eq] at he
    change (shiftFunctor Spectrum s).map (HasFunctorialCofiber.cofibδ
      (T.mapAt (show s ≤ s+1 by omega))) ≫ g = 0
    simpa only [g, shiftedConnecting, c, Iso.app_inv, Category.assoc] using he
  obtain ⟨v,hv⟩ := mapped_yoneda_exact₃ (stepTriangleAt T s).rotate
    (rot_of_distTriang _ (stepTriangleAt_distinguished T s)) s g hgδ
  have hz : (shiftFunctor Spectrum s).map
      ((shiftFunctor Spectrum (1:ℤ)).map (stepTriangleAt T s).mor₁) ≫ v = 0 :=
    into_shifted_layer_annihilates U k m _
      (shifted_tensor_zero _ (shifted_tensor_zero _ (stepAt_tensor_zero T s hs) 1) s) v
  have hg : g = 0 := by
    change g = (shiftFunctor Spectrum s).map
      (-((shiftFunctor Spectrum (1:ℤ)).map (stepTriangleAt T s).mor₁)) ≫ v at hv
    rw [Functor.map_neg, Preadditive.neg_comp, hz, neg_zero] at hv
    exact hv
  apply (cancel_epi c.inv).mp
  simpa only [g, Category.assoc, comp_zero] using hg


end
end KIP126.Literature.Standard.ShiftedResolutionExact
end
