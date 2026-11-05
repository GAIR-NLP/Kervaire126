module

public import KIP126.AdamsSynthetic.ModelFoundation.CofiberInvariance
public import KIP126.AdamsSynthetic.ModelFoundation.Localization
public import KIP126.AdamsSynthetic.ModelFoundation.ShiftFromEquivalence

/-! Suspension and boundary maps from the point-set cofiber functor.

The suspension of X is the derived cofiber of the actual arrow X → 0.
The boundary of f is induced by the strictly commutative square from f to
its source-to-zero arrow. These maps are natural before localization. No
triangulation, invertibility of suspension, or functor on Arrow(Ho C) is
assumed by these constructions.
-/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.CofibrantGeneration
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasZeroMorphisms C] [HasZeroObject C]
attribute [local instance] HasZeroObject.zero'
noncomputable section

/-- The actual point-set arrow from an object to the chosen zero object. -/
public def sourceZeroArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (0 : X ⟶ 0)
  map f := Arrow.homMk f (𝟙 (0 : C)) (by simp)
  map_id X := by ext <;> simp
  map_comp f g := by ext <;> simp

/-- The square from f to its source-to-zero arrow, natural in strict
commutative squares. Its left component is the identity on the same source. -/
public def arrowToSourceZero :
    𝟭 (Arrow C) ⟶ Arrow.leftFunc ⋙ sourceZeroArrowFunctor where
  app f := Arrow.homMk (𝟙 f.left) (0 : f.right ⟶ 0)
    (by simp [sourceZeroArrowFunctor])
  naturality f g φ := by ext <;> simp [sourceZeroArrowFunctor]

variable (G : CofibrantGeneration C)

/-- Point-set suspension constructed by the same functorial cofibrant
replacement and pushout as the cofiber functor. -/
public noncomputable def suspensionFunctor : C ⥤ C :=
  sourceZeroArrowFunctor ⋙ G.cofiberFunctor

/-- The boundary into suspension, constructed using the same cofiber
functor on the actual source-to-zero square. -/
public noncomputable def cofiberBoundary :
    G.cofiberFunctor ⟶ Arrow.leftFunc ⋙ G.suspensionFunctor where
  app f := G.cofiberFunctor.map (arrowToSourceZero.app f)
  naturality f g φ := by
    change G.cofiberFunctor.map φ ≫
        G.cofiberFunctor.map (arrowToSourceZero.app g) =
      G.cofiberFunctor.map (arrowToSourceZero.app f) ≫
        G.cofiberFunctor.map (sourceZeroArrowFunctor.map φ.left)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun z => G.cofiberFunctor.map z)
      (arrowToSourceZero.naturality φ)

/-- Boundary naturality is induced by the point-set functor and its replacement maps. -/
public theorem cofiberBoundary_naturality {f g : Arrow C} (φ : f ⟶ g) :
    G.cofiberFunctor.map φ ≫ G.cofiberBoundary.app g =
      G.cofiberBoundary.app f ≫ G.suspensionFunctor.map φ.left :=
  G.cofiberBoundary.naturality φ

/-- Suspension takes cofibrant values because it is this actual cofiber. -/
public theorem suspension_isCofibrant (X : C) :
    IsCofibrant (G.suspensionFunctor.obj X) :=
  G.cofiber_isCofibrant (Arrow.mk (0 : X ⟶ 0))

/-- The cofiber of a point-set identity is weakly zero. -/
public theorem cofiberIdentity_weakZero (X : C) :
    weakEquivalences C (0 : (0 : C) ⟶ G.cofiberFunctor.obj (Arrow.mk (𝟙 X))) := by
  let f := G.cofibrantReplacementFunctor.mapArrow.obj (Arrow.mk (𝟙 X))
  haveI : WeakEquivalence (G.cofibrationTrivialFibrationFactorization.p.app f) :=
    (weakEquivalence_iff _).2 (G.cofibrationTrivialFibrationFactorization.hp f).2
  haveI : WeakEquivalence f.hom := by
    change WeakEquivalence (G.cofibrantReplacementFunctor.map (𝟙 X))
    rw [G.cofibrantReplacementFunctor.map_id]
    infer_instance
  haveI : WeakEquivalence (G.cofibrationTrivialFibrationFactorization.i.app f) :=
    weakEquivalence_of_postcomp_of_fac G.cofibrationTrivialFibrationFactorization.fac_app
  have hi : trivialCofibrations C
      (G.cofibrantArrowReplacement.obj (Arrow.mk (𝟙 X))).hom :=
    ⟨G.cofibrantArrowReplacement_cofibration _, by
      change weakEquivalences C (G.cofibrationTrivialFibrationFactorization.i.app f)
      exact mem_weakEquivalences _⟩
  exact (MorphismProperty.of_isPushout (G.cofiber_isPushout (Arrow.mk (𝟙 X))).flip hi).2

/-- The actual suspension, built as a cofiber of X → 0, preserves weak equivalences. -/
public theorem suspensionFunctor_weakEquivalences {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) : weakEquivalences C (G.suspensionFunctor.map f) := by
  apply G.cofiberFunctor_weakEquivalences (sourceZeroArrowFunctor.map f)
  exact ⟨hf, mem_weakEquivalences (𝟙 _)⟩

variable {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

/-- Suspension followed by localization inverts weak equivalences. -/
public theorem suspensionFunctor_inverts :
    (weakEquivalences C).IsInvertedBy (G.suspensionFunctor ⋙ L) := by
  intro X Y f hf
  exact Localization.inverts L (weakEquivalences C) _
    (G.suspensionFunctor_weakEquivalences f hf)

/-- Suspension on the homotopy category induced by the point-set model. -/
public noncomputable def derivedSuspensionFunctor : H ⥤ H :=
  Localization.lift (G.suspensionFunctor ⋙ L) (G.suspensionFunctor_inverts L) L

/-- The natural comparison to the actual point-set suspension. -/
public noncomputable def derivedSuspensionFunctorComparison :
    L ⋙ G.derivedSuspensionFunctor L ≅ G.suspensionFunctor ⋙ L :=
  Localization.fac (G.suspensionFunctor ⋙ L) (G.suspensionFunctor_inverts L) L

omit [HasZeroMorphisms C] [HasZeroObject C] in
/-- Source evaluation inverts levelwise weak equivalences of actual arrows. -/
public theorem arrowSource_inverts :
    (weakEquivalences C).arrow.IsInvertedBy (Arrow.leftFunc ⋙ L) := by
  intro f g φ hφ
  exact Localization.inverts L (weakEquivalences C) _ hφ.1

/-- Source evaluation on the localization of the actual arrow category. -/
public noncomputable def derivedSourceFunctor :
    (weakEquivalences C).arrow.Localization ⥤ H :=
  Localization.lift (Arrow.leftFunc ⋙ L) (arrowSource_inverts L)
    (weakEquivalences C).arrow.Q

/-- The natural comparison for source evaluation. -/
public noncomputable def derivedSourceFunctorComparison :
    (weakEquivalences C).arrow.Q ⋙ derivedSourceFunctor L ≅ Arrow.leftFunc ⋙ L :=
  Localization.fac (Arrow.leftFunc ⋙ L) (arrowSource_inverts L)
    (weakEquivalences C).arrow.Q

/-- The actual cofiber boundary, with its suspension target identified with
 the derived suspension of the original source. -/
public noncomputable def localizedCofiberBoundary :
    G.cofiberFunctor ⋙ L ⟶ Arrow.leftFunc ⋙ L ⋙ G.derivedSuspensionFunctor L :=
  whiskerRight G.cofiberBoundary L ≫
    whiskerLeft Arrow.leftFunc (G.derivedSuspensionFunctorComparison L).inv

/-- The boundary on each point-set arrow is the same actual boundary,
 followed by the inverse suspension comparison. -/
public theorem localizedCofiberBoundary_app (f : Arrow C) :
    (G.localizedCofiberBoundary L).app f =
      L.map (G.cofiberBoundary.app f) ≫
        (G.derivedSuspensionFunctorComparison L).inv.app f.left := rfl

/-- The comparison for the suspension of the source, on localized arrows. -/
public noncomputable def derivedSuspendedSourceComparison :
    (weakEquivalences C).arrow.Q ⋙
        (derivedSourceFunctor L ⋙ G.derivedSuspensionFunctor L) ≅
      Arrow.leftFunc ⋙ L ⋙ G.derivedSuspensionFunctor L :=
  isoWhiskerRight (derivedSourceFunctorComparison L) (G.derivedSuspensionFunctor L)

/-- The cofiber boundary descends naturally to localized actual arrows.
The target is the derived suspension of their derived source. -/
public noncomputable def derivedCofiberBoundary :
    G.derivedCofiberFunctor L ⟶ derivedSourceFunctor L ⋙ G.derivedSuspensionFunctor L := by
  letI : Localization.Lifting (weakEquivalences C).arrow.Q (weakEquivalences C).arrow
      (G.cofiberFunctor ⋙ L) (G.derivedCofiberFunctor L) :=
    ⟨G.derivedCofiberFunctorComparison L⟩
  letI : Localization.Lifting (weakEquivalences C).arrow.Q (weakEquivalences C).arrow
      (Arrow.leftFunc ⋙ L ⋙ G.derivedSuspensionFunctor L)
      (derivedSourceFunctor L ⋙ G.derivedSuspensionFunctor L) :=
    ⟨G.derivedSuspendedSourceComparison L⟩
  exact Localization.liftNatTrans (weakEquivalences C).arrow.Q (weakEquivalences C).arrow
    (G.cofiberFunctor ⋙ L) (Arrow.leftFunc ⋙ L ⋙ G.derivedSuspensionFunctor L)
    (G.derivedCofiberFunctor L) (derivedSourceFunctor L ⋙ G.derivedSuspensionFunctor L)
    (G.localizedCofiberBoundary L)

/-- On the image of a point-set arrow, the descended boundary is conjugate
 to its actual point-set boundary by the displayed comparison isomorphisms. -/
public theorem derivedCofiberBoundary_app (f : Arrow C) :
    (G.derivedCofiberBoundary L).app ((weakEquivalences C).arrow.Q.obj f) =
      (G.derivedCofiberFunctorComparison L).hom.app f ≫
        ((G.localizedCofiberBoundary L).app f ≫
          (G.derivedSuspendedSourceComparison L).inv.app f) := by
  simp [derivedCofiberBoundary, Localization.liftNatTrans_app,
    Localization.Lifting.iso]

/-- The cofiber of an identity is a zero object after localization. -/
public theorem localizedCofiberIdentity_isZero (X : C) :
    IsZero (L.obj (G.cofiberFunctor.obj (Arrow.mk (𝟙 X)))) := by
  haveI : IsIso (L.map (0 : (0 : C) ⟶ G.cofiberFunctor.obj (Arrow.mk (𝟙 X)))) :=
    Localization.inverts L (weakEquivalences C) _ (G.cofiberIdentity_weakZero X)
  exact (localization_isZero L (weakEquivalences C)).of_iso
    (asIso (L.map (0 : (0 : C) ⟶ G.cofiberFunctor.obj (Arrow.mk (𝟙 X))))).symm

/-- The cofiber inclusion followed by the actual point-set boundary is zero
 after localization. -/
public theorem localizedInclusion_boundary_zero [HasZeroMorphisms H] (f : Arrow C) :
    (G.localizedCofiberInclusion L).app f ≫ L.map (G.cofiberBoundary.app f) = 0 := by
  letI := localization_preservesZeroMorphisms L (weakEquivalences C)
  have h := (G.localizedCofiberInclusion L).naturality (arrowToSourceZero.app f)
  change L.map (0 : f.right ⟶ (0 : C)) ≫
      (G.localizedCofiberInclusion L).app (sourceZeroArrowFunctor.obj f.left) =
    (G.localizedCofiberInclusion L).app f ≫ L.map (G.cofiberBoundary.app f) at h
  simpa only [Functor.map_zero, zero_comp] using h.symm

/-- The boundary followed by suspension of the original arrow factors
 through the cofiber of the target identity. -/
private theorem boundary_suspension_factorization (f : Arrow C) :
    G.cofiberBoundary.app f ≫ G.suspensionFunctor.map f.hom =
      G.cofiberFunctor.map (Arrow.homMk f.hom (𝟙 f.right)
        (by simp) : f ⟶ Arrow.mk (𝟙 f.right)) ≫
      G.cofiberBoundary.app (Arrow.mk (𝟙 f.right)) := by
  change G.cofiberFunctor.map (arrowToSourceZero.app f) ≫
      G.cofiberFunctor.map (sourceZeroArrowFunctor.map f.hom) =
    G.cofiberFunctor.map _ ≫ G.cofiberFunctor.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext <;> simp [arrowToSourceZero, sourceZeroArrowFunctor]

/-- The next composite in the localized Puppe sequence is zero. -/
public theorem localizedBoundary_suspension_zero [HasZeroMorphisms H] (f : Arrow C) :
    L.map (G.cofiberBoundary.app f) ≫ L.map (G.suspensionFunctor.map f.hom) = 0 := by
  rw [← L.map_comp, G.boundary_suspension_factorization, L.map_comp]
  rw [(G.localizedCofiberIdentity_isZero L f.right).eq_of_src
    (L.map (G.cofiberBoundary.app (Arrow.mk (𝟙 f.right)))) 0]
  simp


/-- The localized inclusion followed by the derived cofiber boundary is zero. -/
public theorem localizedCofiberInclusion_boundary_comp [HasZeroMorphisms H] (f : Arrow C) :
    (G.localizedCofiberInclusion L).app f ≫ (G.localizedCofiberBoundary L).app f = 0 := by
  rw [localizedCofiberBoundary_app, ← Category.assoc,
    G.localizedInclusion_boundary_zero L f, zero_comp]

/-- The derived boundary followed by the derived suspension of the original
arrow is zero. Both maps come from the same point-set cofiber construction. -/
public theorem localizedCofiberBoundary_suspension_comp [HasZeroMorphisms H] (f : Arrow C) :
    (G.localizedCofiberBoundary L).app f ≫
      (G.derivedSuspensionFunctor L).map (L.map f.hom) = 0 := by
  rw [localizedCofiberBoundary_app, Category.assoc]
  have h := (G.derivedSuspensionFunctorComparison L).inv.naturality f.hom
  change L.map (G.suspensionFunctor.map f.hom) ≫
      (G.derivedSuspensionFunctorComparison L).inv.app f.right =
    (G.derivedSuspensionFunctorComparison L).inv.app f.left ≫
      (G.derivedSuspensionFunctor L).map (L.map f.hom) at h
  rw [← h, ← Category.assoc, G.localizedBoundary_suspension_zero L f, zero_comp]


/-- Stability means that the actual suspension derived from this model is an
 equivalence. Under precisely that hypothesis it supplies a coherent integer
 shift on the specified localization. -/
@[implicit_reducible]
public noncomputable def derivedSuspensionHasShift
    [(G.derivedSuspensionFunctor L).IsEquivalence] : HasShift H ℤ :=
  ModelFoundation.hasShiftFromEquivalence (G.derivedSuspensionFunctor L).asEquivalence

/-- The shift by one just constructed is identified with the suspension
 derived from this same model and localization. -/
public noncomputable def derivedSuspensionShiftOneIso
    [(G.derivedSuspensionFunctor L).IsEquivalence] :
    letI := G.derivedSuspensionHasShift L
    shiftFunctor H (1 : ℤ) ≅ G.derivedSuspensionFunctor L :=
  ModelFoundation.shiftOneIsoFromEquivalence (G.derivedSuspensionFunctor L).asEquivalence

end
end KIP126.StableHomotopy.CofibrantGeneration
