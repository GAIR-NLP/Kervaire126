module

public import KIP126.AdamsSynthetic.ModelFoundation.Generation

/-! Functorial cofibers on the point-set arrow category. The functorial small object
construction replaces an arrow by a cofibration between cofibrant objects; pushing
out its source to zero gives the cofiber. The functor laws follow from pushout
uniqueness. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (G : CofibrantGeneration C)

/-- The strict functor on the point-set arrow category obtained by replacing both
endpoints and factoring the arrow. -/
public noncomputable def cofibrantArrowReplacement : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (G.cofibrationTrivialFibrationFactorization.i.app
    (G.cofibrantReplacementFunctor.mapArrow.obj f))
  map φ := Arrow.homMk (G.cofibrantReplacementFunctor.map φ.left)
    (G.cofibrationTrivialFibrationFactorization.Z.map
      (G.cofibrantReplacementFunctor.mapArrow.map φ))
    (G.cofibrationTrivialFibrationFactorization.i.naturality
      (G.cofibrantReplacementFunctor.mapArrow.map φ))
  map_id f := by
    ext
    · exact G.cofibrantReplacementFunctor.map_id _
    · change G.cofibrationTrivialFibrationFactorization.Z.map
        (G.cofibrantReplacementFunctor.mapArrow.map (𝟙 f)) = 𝟙 _
      exact (G.cofibrantReplacementFunctor.mapArrow ⋙
        G.cofibrationTrivialFibrationFactorization.Z).map_id f
  map_comp φ ψ := by
    ext
    · exact G.cofibrantReplacementFunctor.map_comp _ _
    · change G.cofibrationTrivialFibrationFactorization.Z.map
        (G.cofibrantReplacementFunctor.mapArrow.map (φ ≫ ψ)) =
          G.cofibrationTrivialFibrationFactorization.Z.map
            (G.cofibrantReplacementFunctor.mapArrow.map φ) ≫
          G.cofibrationTrivialFibrationFactorization.Z.map
            (G.cofibrantReplacementFunctor.mapArrow.map ψ)
      simp only [Functor.map_comp]

/-- The replacement arrow is a cofibration. -/
public theorem cofibrantArrowReplacement_cofibration (f : Arrow C) :
    cofibrations C (G.cofibrantArrowReplacement.obj f).hom :=
  G.cofibrationTrivialFibrationFactorization.hi _

/-- The source of a replacement arrow is cofibrant. -/
public theorem cofibrantArrowReplacement_source (f : Arrow C) :
    IsCofibrant (G.cofibrantArrowReplacement.obj f).left :=
  G.cofibrantReplacement_isCofibrant f.left

/-- The target of a replacement arrow is cofibrant. -/
public theorem cofibrantArrowReplacement_target (f : Arrow C) :
    IsCofibrant (G.cofibrantArrowReplacement.obj f).right := by
  letI : Cofibration (G.cofibrantArrowReplacement.obj f).hom :=
    (cofibration_iff _).2 (G.cofibrantArrowReplacement_cofibration f)
  letI := G.cofibrantArrowReplacement_source f
  exact isCofibrant_of_cofibration (G.cofibrantArrowReplacement.obj f).hom

/-- The comparison to the given arrow is natural at both endpoints. -/
public noncomputable def cofibrantArrowComparison :
    G.cofibrantArrowReplacement ⟶ 𝟭 (Arrow C) where
  app f := Arrow.homMk (G.cofibrantReplacementCounit.app f.left)
    (G.cofibrationTrivialFibrationFactorization.p.app
        (G.cofibrantReplacementFunctor.mapArrow.obj f) ≫
      G.cofibrantReplacementCounit.app f.right) (by
        change G.cofibrantReplacementCounit.app f.left ≫ f.hom =
          G.cofibrationTrivialFibrationFactorization.i.app
              (G.cofibrantReplacementFunctor.mapArrow.obj f) ≫
            (G.cofibrationTrivialFibrationFactorization.p.app
                (G.cofibrantReplacementFunctor.mapArrow.obj f) ≫
              G.cofibrantReplacementCounit.app f.right)
        rw [MorphismProperty.FunctorialFactorizationData.fac_app_assoc]
        exact (G.cofibrantReplacementCounit.naturality f.hom).symm)
  naturality f g φ := by
    ext
    · exact G.cofibrantReplacementCounit.naturality φ.left
    · change G.cofibrationTrivialFibrationFactorization.Z.map
          (G.cofibrantReplacementFunctor.mapArrow.map φ) ≫
            (G.cofibrationTrivialFibrationFactorization.p.app
                (G.cofibrantReplacementFunctor.mapArrow.obj g) ≫
              G.cofibrantReplacementCounit.app g.right) =
          (G.cofibrationTrivialFibrationFactorization.p.app
              (G.cofibrantReplacementFunctor.mapArrow.obj f) ≫
            G.cofibrantReplacementCounit.app f.right) ≫ φ.right
      rw [← Category.assoc,
        G.cofibrationTrivialFibrationFactorization.p.naturality,
        Category.assoc]
      change G.cofibrationTrivialFibrationFactorization.p.app
          (G.cofibrantReplacementFunctor.mapArrow.obj f) ≫
          (G.cofibrantReplacementFunctor.map φ.right ≫
            G.cofibrantReplacementCounit.app g.right) = _
      rw [G.cofibrantReplacementCounit.naturality]
      exact (Category.assoc _ _ _).symm

/-- Both endpoint comparisons are weak equivalences. -/
public theorem cofibrantArrowComparison_weakEquivalences (f : Arrow C) :
    weakEquivalences C (G.cofibrantArrowComparison.app f).left ∧
      weakEquivalences C (G.cofibrantArrowComparison.app f).right := by
  constructor
  · exact G.cofibrantReplacementCounit_weakEquivalence f.left
  · exact (weakEquivalences C).comp_mem _ _
      (G.cofibrationTrivialFibrationFactorization.hp _).2
      (G.cofibrantReplacementCounit_weakEquivalence f.right)

variable [HasZeroMorphisms C] [HasZeroObject C]
attribute [local instance] HasZeroObject.zero'

/-- The point-set cofiber functor obtained from the chosen cofibrant arrow
replacement. Its domain retains actual commutative squares. -/
public noncomputable def cofiberFunctor : Arrow C ⥤ C where
  obj f := pushout (G.cofibrantArrowReplacement.obj f).hom
    (0 : (G.cofibrantArrowReplacement.obj f).left ⟶ 0)
  map {f g} φ := pushout.map _ _ _ _
    (G.cofibrantArrowReplacement.map φ).right (𝟙 (0 : C))
    (G.cofibrantArrowReplacement.map φ).left
    (G.cofibrantArrowReplacement.map φ).w.symm (by simp)
  map_id f := by
    apply pushout.hom_ext
    · simp
    · exact (isZero_zero C).eq_of_src _ _
  map_comp φ ψ := by
    apply pushout.hom_ext <;> simp [Category.assoc]

/-- The inclusion of the replacement target into its cofiber is natural. -/
public noncomputable def cofiberInclusion :
    G.cofibrantArrowReplacement ⋙ Arrow.rightFunc ⟶ G.cofiberFunctor where
  app f := pushout.inl _ _
  naturality f g φ := by simp [cofiberFunctor]

/-- The replacement arrow followed by the cofiber inclusion is zero. -/
public theorem cofiberInclusion_comp (f : Arrow C) :
    (G.cofibrantArrowReplacement.obj f).hom ≫ G.cofiberInclusion.app f = 0 := by
  simpa [cofiberInclusion] using
    (pushout.condition (f := (G.cofibrantArrowReplacement.obj f).hom)
      (g := (0 : (G.cofibrantArrowReplacement.obj f).left ⟶ (0 : C))))

/-- The displayed square is the actual chosen pushout square. -/
public theorem cofiber_isPushout (f : Arrow C) :
    IsPushout (G.cofibrantArrowReplacement.obj f).hom
      (0 : (G.cofibrantArrowReplacement.obj f).left ⟶ (0 : C))
      (G.cofiberInclusion.app f) (0 : (0 : C) ⟶ G.cofiberFunctor.obj f) := by
  change IsPushout (G.cofibrantArrowReplacement.obj f).hom
    (0 : (G.cofibrantArrowReplacement.obj f).left ⟶ (0 : C))
    (pushout.inl _ _) 0
  have hz : pushout.inr (G.cofibrantArrowReplacement.obj f).hom
      (0 : (G.cofibrantArrowReplacement.obj f).left ⟶ (0 : C)) = 0 :=
    (isZero_zero C).eq_of_src _ _
  simpa only [hz] using IsPushout.of_hasPushout
    (G.cofibrantArrowReplacement.obj f).hom
    (0 : (G.cofibrantArrowReplacement.obj f).left ⟶ (0 : C))

/-- The point-set cofiber is cofibrant, as a pushout of a cofibration along
its source-to-zero map. -/
public theorem cofiber_isCofibrant (f : Arrow C) :
    IsCofibrant (G.cofiberFunctor.obj f) := by
  apply (isCofibrant_iff_of_isInitial (0 : (0 : C) ⟶ G.cofiberFunctor.obj f)
    (isZero_zero C).isInitial).2
  rw [cofibration_iff]
  exact MorphismProperty.of_isPushout (G.cofiber_isPushout f).flip
    (G.cofibrantArrowReplacement_cofibration f)

end KIP126.StableHomotopy.CofibrantGeneration
