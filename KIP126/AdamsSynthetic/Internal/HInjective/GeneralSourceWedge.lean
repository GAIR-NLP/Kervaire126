module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.HInjective.StrictWedge
import all KIP126.AdamsSynthetic.Internal.HInjective.LocalizedStrictWedge
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Replacement.Cubical.Cofibrant.Proofs
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.HomotopyGroup.Functor.Proofs

/-! Actual arbitrary source coproducts, constructed from the explicit strict
wedge of the cubical replacements. No separation condition is imposed
on the original spectra. -/
@[expose] section
namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

private abbrev wedgeReplacement (X : SourceCategory.{u}) : Prespectrum.{u} :=
  cubicalReplacementFunctor.obj X.as.obj

private def wedgeReplacementIso (X : SourceCategory.{u}) :
    sourceLocalization.obj (wedgeReplacement X) ≅ X := by
  letI := stableEquivalences.Q_inverts (cubicalReplacementComparison.app X.as.obj)
    (cubicalReplacementComparison_stableEquivalence X.as.obj)
  exact asIso (sourceLocalization.map (cubicalReplacementComparison.app X.as.obj))

private def derivedWedgeCofan {J : Type u} (X : J → SourceCategory.{u}) : Cofan X :=
  Cofan.mk (sourceLocalization.obj (strictWedge (fun j => wedgeReplacement (X j))))
    (fun j => (wedgeReplacementIso (X j)).inv ≫
      sourceLocalization.map (strictWedgeι (fun j => wedgeReplacement (X j)) j))

@[reassoc (attr := simp)]
private theorem derivedWedge_inclusion_comparison {J : Type u}
    (X : J → SourceCategory.{u}) (j : J) :
    (wedgeReplacementIso (X j)).hom ≫ (derivedWedgeCofan X).inj j =
      sourceLocalization.map (strictWedgeι (fun j => wedgeReplacement (X j)) j) := by
  simp only [derivedWedgeCofan,Cofan.mk_ι_app,Cofan.inj,Iso.hom_inv_id_assoc]

private def derivedWedgeIsColimit {J : Type u} (X : J → SourceCategory.{u}) :
    IsColimit (derivedWedgeCofan X) := by
  let h := source_strictWedge_isColimit (fun j => wedgeReplacement (X j))
    (fun j => cubicalReplacement_initial_hasLiftingProperty_of_level (X j).as.obj)
  let c' (c : Cofan X) := Cofan.mk c.pt
    (fun j => (wedgeReplacementIso (X j)).hom ≫ c.inj j)
  refine Cofan.IsColimit.mk _ (fun c => h.desc (c' c)) ?_ ?_
  · intro c j
    change ((wedgeReplacementIso (X j)).inv ≫
      sourceLocalization.map (strictWedgeι (fun j => wedgeReplacement (X j)) j)) ≫
        h.desc (c' c) = _
    have hf : sourceLocalization.map (strictWedgeι (fun j => wedgeReplacement (X j)) j) ≫
        h.desc (c' c) = (wedgeReplacementIso (X j)).hom ≫ c.inj j :=
      h.fac (c' c) ⟨j⟩
    rw [Category.assoc, hf]
    exact Iso.inv_hom_id_assoc _ _
  · intro c m hm
    apply h.hom_ext
    rintro ⟨j⟩
    rw [h.fac]
    apply (cancel_epi (wedgeReplacementIso (X j)).inv).mp
    simpa only [c', Cofan.mk_ι_app, derivedWedgeCofan, Cofan.inj,
      Category.assoc, Iso.inv_hom_id_assoc] using hm j

private instance sourceSmallCoproducts : HasCoproducts.{u} SourceCategory.{u} :=
  hasCoproducts_of_colimit_cofans derivedWedgeCofan derivedWedgeIsColimit

private theorem source_coproduct_finite_support {J : Type u}
    (X : J → SourceCategory.{u}) (d : ℤ)
    (a : (sourceStableHomotopyAddFunctor d).obj (∐ X)) :
    ∃ (s : Finset J)
      (b : (sourceStableHomotopyAddFunctor d).obj (∐ fun j : (s : Set J) => X j.val)),
      (sourceStableHomotopyAddFunctor d).map
        (Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val)) b = a := by
  classical
  let F := sourceStableHomotopyAddFunctor d
  let Q (j : J) := wedgeReplacement (X j)
  let e := (derivedWedgeIsColimit X).coconePointUniqueUpToIso (coproductIsCoproduct X)
  obtain ⟨s,b,hb⟩ := strictWedge_stableHomotopy_finite_support Q d (F.map e.inv a)
  let Y (j : (s : Set J)) := X j.val
  let e' := (derivedWedgeIsColimit Y).coconePointUniqueUpToIso (coproductIsCoproduct Y)
  refine ⟨s,F.map e'.hom b,?_⟩
  have hc : e'.hom ≫ Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val) =
      sourceLocalization.map (strictWedgeSubfamily Q (s : Set J)) ≫ e.hom := by
    apply (derivedWedgeIsColimit Y).hom_ext
    rintro ⟨j⟩
    have he' : (derivedWedgeCofan Y).inj j ≫ e'.hom = Sigma.ι Y j :=
      (derivedWedgeIsColimit Y).fac _ ⟨j⟩
    have he : (derivedWedgeCofan X).inj j.val ≫ e.hom = Sigma.ι X j.val :=
      (derivedWedgeIsColimit X).fac _ ⟨j.val⟩
    change (derivedWedgeCofan Y).inj j ≫ (e'.hom ≫ _) =
      (derivedWedgeCofan Y).inj j ≫ _
    rw [← Category.assoc, he', Sigma.ι_desc]
    apply (cancel_epi (wedgeReplacementIso (Y j)).hom).mp
    rw [derivedWedge_inclusion_comparison_assoc,
      ← Category.assoc, ← sourceLocalization.map_comp]
    have hsub : strictWedgeι (fun j => wedgeReplacement (Y j)) j ≫
        strictWedgeSubfamily Q (s : Set J) = strictWedgeι Q j.val := by
      exact strictWedgeι_desc (fun j : (s : Set J) => Q j.val)
        (fun j => strictWedgeι Q j.val) j
    rw [hsub]
    change (wedgeReplacementIso (X j.val)).hom ≫ Sigma.ι X j.val =
      sourceLocalization.map (strictWedgeι (fun j => wedgeReplacement (X j)) j.val) ≫ e.hom
    rw [← derivedWedge_inclusion_comparison X j.val, Category.assoc, he]
  change (F.map e'.hom ≫ F.map _) b = a
  rw [← F.map_comp, hc, F.map_comp]
  change F.map e.hom ((sourceStableHomotopyAddFunctor d).map
    (sourceLocalization.map (strictWedgeSubfamily Q (s : Set J))) b) = a
  rw [sourceStableHomotopyAddFunctor_map]
  change F.map e.hom (stableHomotopyMap (strictWedgeSubfamily Q (s : Set J)) d b) = a
  rw [hb]
  change (F.map e.inv ≫ F.map e.hom) a = a
  simp only [← F.map_comp, Iso.inv_hom_id, F.map_id]
  rfl

end
end KIP126.AdamsSynthetic.Source.Prespectrum
end
