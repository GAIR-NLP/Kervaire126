module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! A localization preserves a zero object. This gives the pointed comparison
needed to transport point-set cofiber pushouts to the specified homotopy
category without adding a separate zero-object compatibility assumption. -/

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy
open CategoryTheory CategoryTheory.Limits
universe u v w z
variable {P : Type u} [Category.{v} P] [HasZeroMorphisms P] [HasZeroObject P]
  {C : Type w} [Category.{z} C]
attribute [local instance] HasZeroObject.zero'

/-- A localization sends the zero object to a zero object. The two universal
maps descend using full faithfulness of precomposition with the localization. -/
public theorem localization_isZero (L : P ⥤ C) (W : MorphismProperty P)
    [L.IsLocalization W] : IsZero (L.obj (0 : P)) := by
  let F : C ⥤ C := (Functor.const C).obj (L.obj (0 : P))
  let τ : L ⋙ F ⟶ L ⋙ 𝟭 C :=
    { app X := L.map (0 : (0 : P) ⟶ X)
      naturality X Y f := by
        change 𝟙 _ ≫ L.map (0 : (0 : P) ⟶ Y) = L.map (0 : (0 : P) ⟶ X) ≫ L.map f
        rw [Category.id_comp, ← L.map_comp, zero_comp] }
  let σ : F ⟶ 𝟭 C :=
    (Localization.fullyFaithfulWhiskeringLeft L W C).preimage τ
  have hσ (X : P) : σ.app (L.obj X) = L.map (0 : (0 : P) ⟶ X) :=
    congr_app ((Localization.fullyFaithfulWhiskeringLeft L W C).map_preimage τ) X
  have hσ₀ : σ.app (L.obj (0 : P)) = 𝟙 _ := by
    rw [hσ, show (0 : (0 : P) ⟶ (0 : P)) = 𝟙 _ from (isZero_zero P).eq_of_src _ _]
    exact L.map_id _
  let τ' : L ⋙ 𝟭 C ⟶ L ⋙ F :=
    { app X := L.map (0 : X ⟶ (0 : P))
      naturality X Y f := by
        change L.map f ≫ L.map (0 : Y ⟶ (0 : P)) = L.map (0 : X ⟶ (0 : P)) ≫ 𝟙 _
        rw [Category.comp_id, ← L.map_comp, comp_zero] }
  let σ' : 𝟭 C ⟶ F :=
    (Localization.fullyFaithfulWhiskeringLeft L W C).preimage τ'
  have hσ' (X : P) : σ'.app (L.obj X) = L.map (0 : X ⟶ (0 : P)) :=
    congr_app ((Localization.fullyFaithfulWhiskeringLeft L W C).map_preimage τ') X
  have hσ'₀ : σ'.app (L.obj (0 : P)) = 𝟙 _ := by
    rw [hσ', show (0 : (0 : P) ⟶ (0 : P)) = 𝟙 _ from (isZero_zero P).eq_of_src _ _]
    exact L.map_id _
  constructor
  · intro Y
    exact ⟨{ default := σ.app Y
             uniq := fun f => by
               have h := σ.naturality f
               change 𝟙 _ ≫ σ.app Y = σ.app (L.obj (0 : P)) ≫ f at h
               rw [hσ₀, Category.id_comp, Category.id_comp] at h
               exact h.symm }⟩
  · intro Y
    exact ⟨{ default := σ'.app Y
             uniq := fun f => by
               have h := σ'.naturality f
               change f ≫ σ'.app (L.obj (0 : P)) = σ'.app Y ≫ 𝟙 _ at h
               rw [hσ'₀] at h
               change f ≫ 𝟙 (L.obj (0 : P)) = σ'.app Y ≫ 𝟙 (L.obj (0 : P)) at h
               exact (Category.comp_id f).symm.trans (h.trans (Category.comp_id _)) }⟩

/-- The homotopy localization is pointed as a consequence of its universal
property; no zero-object structure on the target is assumed. -/
public theorem localization_hasZeroObject (L : P ⥤ C) (W : MorphismProperty P)
    [L.IsLocalization W] : HasZeroObject C :=
  ⟨⟨L.obj (0 : P), localization_isZero L W⟩⟩

/-- The canonical zero comparison for a localization into a pointed category. -/
public noncomputable def localizationZeroIso [HasZeroObject C]
    (L : P ⥤ C) (W : MorphismProperty P) [L.IsLocalization W] :
    L.obj (0 : P) ≅ (0 : C) :=
  (localization_isZero L W).isoZero

/-- A localization between pointed categories preserves zero morphisms. -/
public theorem localization_preservesZeroMorphisms [HasZeroMorphisms C]
    (L : P ⥤ C) (W : MorphismProperty P) [L.IsLocalization W] :
    L.PreservesZeroMorphisms := by
  constructor
  intro X Y
  rw [show (0 : X ⟶ Y) = (0 : X ⟶ (0 : P)) ≫ (0 : (0 : P) ⟶ Y) by simp]
  rw [L.map_comp]
  have hz := localization_isZero L W
  rw [hz.eq_of_src (L.map (0 : (0 : P) ⟶ Y)) 0]
  simp

end KIP126.StableHomotopy
