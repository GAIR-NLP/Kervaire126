module
public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.ModelFoundation
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]
  (X Y : C) [IsCofibrant X] [IsCofibrant Y]

private theorem localizedCoprod_hom_ext {Z : H}
    (f g : L.obj (X ⨿ Y) ⟶ Z)
    (hx : L.map coprod.inl ≫ f = L.map coprod.inl ≫ g)
    (hy : L.map coprod.inr ≫ f = L.map coprod.inr ≫ g) : f = g := by
  letI := Localization.essSurj (BifibrantObject.ι ⋙ L)
    (weakEquivalences (BifibrantObject C))
  let T := (BifibrantObject.ι ⋙ L).objPreimage Z
  let e : L.obj T.obj ≅ Z := (BifibrantObject.ι ⋙ L).objObjPreimageIso Z
  letI : IsCofibrant (X ⨿ Y) := isCofibrant_of_cofibration (coprod.inl : X ⟶ X ⨿ Y)
  obtain ⟨f', hf⟩ := map_surjective_of_isLocalization L (X ⨿ Y) T.obj (f ≫ e.inv)
  obtain ⟨g', hg⟩ := map_surjective_of_isLocalization L (X ⨿ Y) T.obj (g ≫ e.inv)
  have hxl : L.map (coprod.inl ≫ f') = L.map (coprod.inl ≫ g') := by
    rw [L.map_comp, L.map_comp, hf, hg, ← Category.assoc, ← Category.assoc, hx]
  have hyl : L.map (coprod.inr ≫ f') = L.map (coprod.inr ≫ g') := by
    rw [L.map_comp, L.map_comp, hf, hg, ← Category.assoc, ← Category.assoc, hy]
  have hx' := (RightHomotopyRel.iff_map_eq L X T.obj).2 hxl
  have hy' := (RightHomotopyRel.iff_map_eq L Y T.obj).2 hyl
  obtain ⟨P, hP⟩ := PathObject.exists_very_good T.obj
  letI := hP
  let hxP := hx'.rightHomotopy P
  let hyP := hy'.rightHomotopy P
  have hfg : P.RightHomotopy f' g' :=
    { h := coprod.desc hxP.h hyP.h
      h₀ := by apply coprod.hom_ext <;> simp
      h₁ := by apply coprod.hom_ext <;> simp }
  have heq : L.map f' = L.map g' :=
    (RightHomotopyRel.iff_map_eq L (X ⨿ Y) T.obj).1 hfg.rightHomotopyRel
  apply (cancel_mono e.inv).1
  exact hf.symm.trans (heq.trans hg)

private theorem localizedCoprod_exists_desc {Z : H}
    (f : L.obj X ⟶ Z) (g : L.obj Y ⟶ Z) :
    ∃ h : L.obj (X ⨿ Y) ⟶ Z,
      L.map coprod.inl ≫ h = f ∧ L.map coprod.inr ≫ h = g := by
  letI := Localization.essSurj (BifibrantObject.ι ⋙ L)
    (weakEquivalences (BifibrantObject C))
  let T := (BifibrantObject.ι ⋙ L).objPreimage Z
  let e : L.obj T.obj ≅ Z := (BifibrantObject.ι ⋙ L).objObjPreimageIso Z
  obtain ⟨f', hf⟩ := map_surjective_of_isLocalization L X T.obj (f ≫ e.inv)
  obtain ⟨g', hg⟩ := map_surjective_of_isLocalization L Y T.obj (g ≫ e.inv)
  refine ⟨L.map (coprod.desc f' g') ≫ e.hom, ?_, ?_⟩
  · rw [← Category.assoc, ← L.map_comp, coprod.inl_desc, hf]
    simp
  · rw [← Category.assoc, ← L.map_comp, coprod.inr_desc, hg]
    simp

/-- A point-set coproduct of cofibrant objects is a coproduct after model
localization. -/
private noncomputable def localizedCoprodIsColimit :
    IsColimit (BinaryCofan.mk (L.map (coprod.inl : X ⟶ X ⨿ Y))
      (L.map (coprod.inr : Y ⟶ X ⨿ Y))) := by
  apply BinaryCofan.IsColimit.mk _
    (fun f g => (localizedCoprod_exists_desc L X Y f g).choose)
  · intro Z f g
    exact (localizedCoprod_exists_desc L X Y f g).choose_spec.1
  · intro Z f g
    exact (localizedCoprod_exists_desc L X Y f g).choose_spec.2
  · intro Z f g m hm₁ hm₂
    apply localizedCoprod_hom_ext L X Y
    · exact hm₁.trans (localizedCoprod_exists_desc L X Y f g).choose_spec.1.symm
    · exact hm₂.trans (localizedCoprod_exists_desc L X Y f g).choose_spec.2.symm

end KIP126.StableHomotopy.ModelFoundation

end


@[expose] section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace KIP126.StableHomotopy.ModelFoundation
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
universe u v w z
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type w} [Category.{z} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

include L in
private theorem modelLocalization_hasBinaryCoproduct (X Y : H) :
    HasBinaryCoproduct X Y := by
  letI := Localization.essSurj (BifibrantObject.ι ⋙ L)
    (weakEquivalences (BifibrantObject C))
  let X' := (BifibrantObject.ι ⋙ L).objPreimage X
  let Y' := (BifibrantObject.ι ⋙ L).objPreimage Y
  let eX : L.obj X'.obj ≅ X := (BifibrantObject.ι ⋙ L).objObjPreimageIso X
  let eY : L.obj Y'.obj ≅ Y := (BifibrantObject.ι ⋙ L).objObjPreimageIso Y
  let c := BinaryCofan.mk (L.map (coprod.inl : X'.obj ⟶ X'.obj ⨿ Y'.obj))
    (L.map (coprod.inr : Y'.obj ⟶ X'.obj ⨿ Y'.obj))
  let h := BinaryCofan.isColimitCompLeftIso c eX.inv
    (localizedCoprodIsColimit L X'.obj Y'.obj)
  let c' := BinaryCofan.mk (eX.inv ≫ c.inl) c.inr
  let h' := BinaryCofan.isColimitCompRightIso c' eY.inv h
  exact HasColimit.mk ⟨_, h'⟩

include L in
private theorem modelLocalization_hasBinaryCoproducts : HasBinaryCoproducts H := by
  letI : ∀ {X Y : H}, HasBinaryCoproduct X Y := fun {X Y} =>
    modelLocalization_hasBinaryCoproduct L X Y
  exact hasBinaryCoproducts_of_hasColimit_pair H

end KIP126.StableHomotopy.ModelFoundation

end
