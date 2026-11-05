module

import KIP126.Literature.Standard

/-! Relative divisibility criteria for the selected finite quotient maps.
Preservation of a general distinguished triangle requires its own comparison. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The inclusion square puts the difference from the actual selected map
in the image of the actual boundary. The factor is retained explicitly. -/
private theorem finite_quotient_map_difference_factors
    {A B : Syn} (f : A ⟶ B) (q : ℕ)
    (u : XModLambdaN A q ⟶ XModLambdaN B q)
    (hι : XModLambdaN.incl A q ≫ u = f ≫ XModLambdaN.incl B q) :
    ∃ z : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶
        XModLambdaN B q,
      u - XModLambdaN.map f q = XModLambdaN.proj A q ≫ z := by
  have hz : XModLambdaN.incl A q ≫ (u - XModLambdaN.map f q) = 0 := by
    rw [Preadditive.comp_sub, hι, ← XModLambdaN.incl_naturality, sub_self]
  exact (XModLambdaN.cofiberTriangle A q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished A q) (u - XModLambdaN.map f q) hz

/-- The projection square constrains the boundary factor
supplied by the inclusion square. -/
private theorem finite_quotient_map_difference_with_projection
    {A B : Syn} (f : A ⟶ B) (q : ℕ)
    (u : XModLambdaN A q ⟶ XModLambdaN B q)
    (hι : XModLambdaN.incl A q ≫ u = f ≫ XModLambdaN.incl B q)
    (hδ : u ≫ XModLambdaN.proj B q = XModLambdaN.proj A q ≫
      (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-(q:ℤ))).map f)) :
    ∃ z : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶
        XModLambdaN B q,
      u - XModLambdaN.map f q = XModLambdaN.proj A q ≫ z ∧
      XModLambdaN.proj A q ≫ z ≫ XModLambdaN.proj B q = 0 := by
  obtain ⟨z,hz⟩ := finite_quotient_map_difference_factors f q u hι
  refine ⟨z,hz,?_⟩
  rw [←Category.assoc,←hz,Preadditive.sub_comp,hδ,
    XModLambdaN.proj_naturality,sub_self]

/-- The kernel of precomposition with the quotient boundary consists of
factors through the suspended lambda power, with the rotation sign
absorbed by negating the witness. -/
private theorem finite_quotient_boundary_factor_zero_iff
    (A : Syn) (q : ℕ) {Z : Syn}
    (z : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶ Z) :
    XModLambdaN.proj A q ≫ z = 0 ↔
      ∃ v : A⟦(1:ℤ)⟧ ⟶ Z,
        z = (shiftFunctor Syn (1:ℤ)).map (lambdaPow q A) ≫ v := by
  constructor
  · intro hz
    obtain ⟨v,hv⟩ := (XModLambdaN.cofiberTriangle A q).rotate.yoneda_exact₃
      (rot_of_distTriang _ (XModLambdaN.cofiberTriangle_distinguished A q)) z hz
    refine ⟨-v,?_⟩
    simpa only [XModLambdaN.cofiberTriangle,Triangle.rotate,Triangle.mk,
      Preadditive.neg_comp,Preadditive.comp_neg] using hv
  · rintro ⟨v,rfl⟩
    rw [←Category.assoc]
    have hzero := comp_distTriang_mor_zero₃₁ (XModLambdaN.cofiberTriangle A q)
      (XModLambdaN.cofiberTriangle_distinguished A q)
    change XModLambdaN.proj A q ≫
      (shiftFunctor Syn (1:ℤ)).map (lambdaPow q A) = 0 at hzero
    rw [hzero,zero_comp]

/-- For a fixed boundary factor of the comparison error, agreement with
the quotient map is equivalent to relative lambda divisibility of that factor. -/
private theorem finite_quotient_map_eq_iff_relative_divisible
    {A B : Syn} (f : A ⟶ B) (q : ℕ)
    (u : XModLambdaN A q ⟶ XModLambdaN B q)
    (z : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶
      XModLambdaN B q)
    (hz : u - XModLambdaN.map f q = XModLambdaN.proj A q ≫ z) :
    u = XModLambdaN.map f q ↔
      ∃ v : A⟦(1:ℤ)⟧ ⟶ XModLambdaN B q,
        z = (shiftFunctor Syn (1:ℤ)).map (lambdaPow q A) ≫ v := by
  rw [←finite_quotient_boundary_factor_zero_iff A q z,←hz,sub_eq_zero]

section LightningTriangles
variable {C : Type u} [StableHomotopyCategory.{u,v} C]

/-- The two endpoint equations give successive factorizations of the
defect and its boundary obstruction. -/
private theorem endpoint_defect_double_factor
    (T U : Triangle C) (hT : T ∈ distTriang C)
    (e : T.obj₃ ⟶ U.obj₃) (hleft : T.mor₂≫e=0) (hright : e≫U.mor₃=0) :
    ∃ (z : T.obj₁⟦(1:ℤ)⟧ ⟶ U.obj₃)
      (w : T.obj₂⟦(1:ℤ)⟧ ⟶ U.obj₁⟦(1:ℤ)⟧),
      e=T.mor₃≫z ∧ z≫U.mor₃=T.rotate.mor₃≫w := by
  obtain ⟨z,hz⟩ := T.yoneda_exact₃ hT e hleft
  have hz0 : T.mor₃≫(z≫U.mor₃)=0 := by
    rw [←Category.assoc,←hz,hright]
  obtain ⟨w,hw⟩ := T.rotate.yoneda_exact₃ (rot_of_distTriang T hT) (z≫U.mor₃) hz0
  exact ⟨z,w,hz,hw⟩

/-- The defect is a lightning flash exactly when a lift across the
target projection corrects the boundary of a source factor. -/
private theorem lightning_iff_boundary_lift
    (T U : Triangle C) (hT : T ∈ distTriang C) (hU : U ∈ distTriang C)
    (e : T.obj₃ ⟶ U.obj₃) (z : T.obj₁⟦(1:ℤ)⟧ ⟶ U.obj₃)
    (hz : e=T.mor₃≫z) :
    (∃ a : T.obj₁⟦(1:ℤ)⟧ ⟶ U.obj₂, e=T.mor₃≫a≫U.mor₂) ↔
      ∃ v : T.obj₂⟦(1:ℤ)⟧ ⟶ U.obj₃,
        z≫U.mor₃=(-(shiftFunctor C (1:ℤ)).map T.mor₁)≫v≫U.mor₃ := by
  let β : T.obj₁⟦(1:ℤ)⟧ ⟶ T.obj₂⟦(1:ℤ)⟧ :=
    -(shiftFunctor C (1:ℤ)).map T.mor₁
  constructor
  · rintro ⟨a,ha⟩
    have hzero : T.mor₃≫(z-a≫U.mor₂)=0 := by
      rw [Preadditive.comp_sub,←hz,ha,sub_self]
    obtain ⟨v,hv⟩ := T.rotate.yoneda_exact₃ (rot_of_distTriang T hT)
      (z-a≫U.mor₂) hzero
    change z-a≫U.mor₂=β≫v at hv
    refine ⟨v,?_⟩
    have h := congrArg (fun f => f≫U.mor₃) hv
    simpa only [Preadditive.sub_comp,Category.assoc,
      comp_distTriang_mor_zero₂₃ U hU,comp_zero,sub_zero] using h
  · rintro ⟨v,hv⟩
    change z≫U.mor₃=β≫v≫U.mor₃ at hv
    have hzero : (z-β≫v)≫U.mor₃=0 := by
      rw [Preadditive.sub_comp,Category.assoc,hv,sub_self]
    obtain ⟨a,ha⟩ := U.coyoneda_exact₃ hU (z-β≫v) hzero
    refine ⟨a,?_⟩
    have h := congrArg (fun f => T.mor₃≫f) ha
    have hβ : T.mor₃≫β=0 :=
      comp_distTriang_mor_zero₂₃ T.rotate (rot_of_distTriang T hT)
    simpa only [Preadditive.comp_sub,←Category.assoc,hβ,zero_comp,sub_zero,←hz] using h

end LightningTriangles

/-- Double factorization of the quotient-map defect through the
source boundary and the suspended lambda power. -/
private theorem selected_quotient_double_obstruction {A B : Syn} (f : A ⟶ B) (q : ℕ)
    (u : XModLambdaN A q ⟶ XModLambdaN B q)
    (hι : XModLambdaN.incl A q≫u=f≫XModLambdaN.incl B q)
    (hδ : u≫XModLambdaN.proj B q=XModLambdaN.proj A q≫
      (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-(q:ℤ))).map f)) :
    ∃ (z : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶ XModLambdaN B q)
      (w : A⟦(1:ℤ)⟧ ⟶ (((SyntheticCategory.biShift (0,-(q:ℤ))).obj B)⟦(1:ℤ)⟧)),
      u-XModLambdaN.map f q=XModLambdaN.proj A q≫z ∧
      z≫XModLambdaN.proj B q=(-(shiftFunctor Syn (1:ℤ)).map (lambdaPow q A))≫w := by
  have hleft : XModLambdaN.incl A q≫(u-XModLambdaN.map f q)=0 := by
    rw [Preadditive.comp_sub,hι,←XModLambdaN.incl_naturality,sub_self]
  have hright : (u-XModLambdaN.map f q)≫XModLambdaN.proj B q=0 := by
    rw [Preadditive.sub_comp,hδ,XModLambdaN.proj_naturality,sub_self]
  exact endpoint_defect_double_factor (XModLambdaN.cofiberTriangle A q)
    (XModLambdaN.cofiberTriangle B q) (XModLambdaN.cofiberTriangle_distinguished A q)
    (u-XModLambdaN.map f q) hleft hright

/-- The exact lightning-flash criterion on the same selected quotient
map, with every source, target and sign retained. -/
private theorem selected_quotient_lightning_iff {A B : Syn} (f : A ⟶ B) (q : ℕ)
    (u : XModLambdaN A q ⟶ XModLambdaN B q)
    (z : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶ XModLambdaN B q)
    (hz : u-XModLambdaN.map f q=XModLambdaN.proj A q≫z) :
    (∃ a : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶ B,
      u-XModLambdaN.map f q=XModLambdaN.proj A q≫a≫XModLambdaN.incl B q) ↔
      ∃ v : A⟦(1:ℤ)⟧ ⟶ XModLambdaN B q,
        z≫XModLambdaN.proj B q=
          (-(shiftFunctor Syn (1:ℤ)).map (lambdaPow q A))≫v≫XModLambdaN.proj B q := by
  exact lightning_iff_boundary_lift (XModLambdaN.cofiberTriangle A q)
    (XModLambdaN.cofiberTriangle B q) (XModLambdaN.cofiberTriangle_distinguished A q)
    (XModLambdaN.cofiberTriangle_distinguished B q) (u-XModLambdaN.map f q) z hz


end
end KIP126.Literature.Standard.Internal
