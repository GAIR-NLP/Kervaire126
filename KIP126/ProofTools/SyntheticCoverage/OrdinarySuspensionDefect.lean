module

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryFiniteCellRows
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! Defects of ordinary suspension comparisons for the selected quotient maps.
The lemmas establish factorization and finite-source comparison uniqueness
under their stated hypotheses. -/
@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
attribute [local instance] HasZeroObject.zero'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The defect of an inclusion-compatible comparison factors through
the specified coefficient projection. -/
private theorem ordinary_suspension_defect_factors_projection
    {A B : SyntheticSpectrum} (f : A ⟶ B) (q : ℕ)
    (eA : XModLambdaN (A⟦(1:ℤ)⟧) q ≅ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (B⟦(1:ℤ)⟧) q ≅ (XModLambdaN B q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl _ q≫eA.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q))
    (heB : XModLambdaN.incl _ q≫eB.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl B q)) :
    ∃ z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (A⟦(1:ℤ)⟧))⟦(1:ℤ)⟧ ⟶
        (XModLambdaN B q)⟦(1:ℤ)⟧,
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map f) q≫eB.hom-
        eA.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map f q)=
          XModLambdaN.proj (A⟦(1:ℤ)⟧) q≫z := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let d := XModLambdaN.map (S.map f) q≫eB.hom-eA.hom≫S.map (XModLambdaN.map f q)
  have hd : XModLambdaN.incl _ q≫d=0 := by
    dsimp only [d]
    rw [Preadditive.comp_sub,←Category.assoc,←XModLambdaN.incl_naturality,
      Category.assoc,heB,←Functor.map_comp,XModLambdaN.incl_naturality,
      Functor.map_comp,←heA,Category.assoc,sub_self]
  exact (XModLambdaN.cofiberTriangle (A⟦(1:ℤ)⟧) q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished _ _) d hd

/-- The suspension defect factors through the last arrow of the rotated row. -/
private theorem ordinary_suspension_defect_factors_row
    (N : Triangle SyntheticSpectrum) (hN : N∈distTriang SyntheticSpectrum) (q : ℕ)
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
    (hrow : Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
      (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom))
        ∈distTriang SyntheticSpectrum) :
    ∃ t : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ⟶ XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q,
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom-
        eA.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map N.mor₁ q)=
          t≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom := by
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let Q := background.quotients.functoriality.functor q
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  letI := background.exactness.shiftAdditive (0,-(q:ℤ))
  have hF : IsZero (F.obj (0:SyntheticSpectrum)) := F.map_isZero (isZero_zero _)
  have hQ : IsZero (Q.obj (0:SyntheticSpectrum)) :=
    (XModLambdaN.cofiberTriangle _ q).isZero₃_of_isZero₁₂
      (XModLambdaN.cofiberTriangle_distinguished _ q) hF (isZero_zero _)
  letI : Q.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_map_zero_object hQ.isoZero
  let l := XModLambdaN.map (S.map N.mor₁) q≫eB.hom
  let d := l-eA.hom≫S.map (XModLambdaN.map N.mor₁ q)
  let U := Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q) (-l)
  have hU : U∈distTriang SyntheticSpectrum := hrow
  have hl : l≫S.map (XModLambdaN.map N.mor₂ q)=0 := by
    have h := comp_distTriang_mor_zero₁₂ U.rotate.rotate (rot_of_distTriang _ (rot_of_distTriang U hU))
    change (-l)≫(-(S.map (XModLambdaN.map N.mor₂ q)))=0 at h
    simpa only [Preadditive.neg_comp,Preadditive.comp_neg,neg_neg] using h
  have hf : XModLambdaN.map N.mor₁ q≫XModLambdaN.map N.mor₂ q=0 := by
    change Q.map N.mor₁≫Q.map N.mor₂=0
    rw [←Functor.map_comp,comp_distTriang_mor_zero₁₂ _ hN,Functor.map_zero]
  have hd : d≫S.map (XModLambdaN.map N.mor₂ q)=0 := by
    dsimp only [d]
    rw [Preadditive.sub_comp,hl,Category.assoc,←Functor.map_comp,hf,Functor.map_zero,comp_zero,sub_zero]
  obtain ⟨t,ht⟩ := U.rotate.rotate.coyoneda_exact₂
    (rot_of_distTriang _ (rot_of_distTriang U hU)) d (by
      change d≫(-(S.map (XModLambdaN.map N.mor₂ q)))=0
      rw [Preadditive.comp_neg,hd,neg_zero])
  refine ⟨-t,?_⟩
  change d=(-t)≫XModLambdaN.map (S.map N.mor₁) q≫eB.hom
  change d=t≫(-l) at ht
  simpa only [Preadditive.comp_neg,Preadditive.neg_comp,Category.assoc,l] using ht


/-- Finite-cell source coordinates annihilate every map in the negative
coefficient window. -/
private theorem finite_cell_native_negative_hom_zero
    (X Y : (AdamsObject (coefficients := background.coefficients)))
    (hX : (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅
        (ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0 < q)
    (z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj
      (background.nu.functor.obj (X.obj background.auxiliary)))⟦(1:ℤ)⟧ ⟶
        XModLambdaN (background.nu.functor.obj (Y.obj background.auxiliary)) q) : z=0 := by
  rcases hX with ⟨n,⟨e⟩⟩ | ⟨n,⟨e⟩⟩
  · let E : background.nu.functor.obj (X.obj background.auxiliary)≅Smn (Syn:=SyntheticSpectrum) n n :=
      background.nu.functor.mapIso e ≪≫nu_row_nu_int_iso SphereSpectrum n ≪≫
        (SyntheticCategory.biShift (n,n)).mapIso background.nu.unitIso
    exact sphere_source_obstruction_zero Y q hq n n (by omega) E z
  · let E : background.nu.functor.obj (X.obj background.auxiliary)≅
        (SyntheticCategory.biShift (n,n)).obj
          (background.nu.functor.obj (ClassicalObject.nuCofiber.obj background.auxiliary)) :=
      background.nu.functor.mapIso e ≪≫
        nu_row_nu_int_iso (ClassicalObject.nuCofiber.obj background.auxiliary) n
    exact nu_cofiber_source_obstruction_zero Y q hq n n (by omega) E z

/-- Vanishing of the displayed Hom group makes inclusion-compatible
suspension comparison maps equal. -/
private theorem ordinary_suspension_comparison_unique_of_negative_hom_zero
    (A : SyntheticSpectrum) (q : ℕ)
    (hzero : ∀ z : ((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧ ⟶
      XModLambdaN A q, z=0)
    (k l : XModLambdaN (A⟦(1:ℤ)⟧) q ⟶ (XModLambdaN A q)⟦(1:ℤ)⟧)
    (hk : XModLambdaN.incl _ q≫k=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q))
    (hl : XModLambdaN.incl _ q≫l=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl A q)) :
    k=l := by
  letI := background.exactness.shiftCommShift (0,-(q:ℤ))
  let S := shiftFunctor SyntheticSpectrum (1:ℤ)
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(q:ℤ))
  have hi : XModLambdaN.incl _ q≫(k-l)=0 := by
    rw [Preadditive.comp_sub,hk,hl,sub_self]
  obtain ⟨z,hz⟩ := (XModLambdaN.cofiberTriangle (A⟦(1:ℤ)⟧) q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished _ _) (k-l) hi
  let χ := S.mapIso ((F.commShiftIso (1:ℤ)).app A)
  let ff := Functor.FullyFaithful.ofFullyFaithful S
  let z₀ := ff.preimage (χ.inv≫z)
  have hz₀ : z₀=0 := hzero z₀
  have hzmap : S.map z₀=χ.inv≫z := ff.map_preimage _
  have hz0 : z=0 := (cancel_epi χ.inv).mp (by rw [←hzmap,hz₀,S.map_zero]; simp)
  exact sub_eq_zero.mp (by rw [hz,hz0,comp_zero])

/-- For a finite second vertex, any comparison supplied by the public row
is the same map as any independently constructed inclusion-compatible one.
Thus additional properties of the latter can be transferred literally. -/
private theorem finite_cell_native_suspension_comparison_unique
    (X : (AdamsObject (coefficients := background.coefficients)))
    (hX : (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅Sphere (C:=Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (X.obj background.auxiliary≅
        (ClassicalObject.nuCofiber.obj background.auxiliary)⟦n⟧)))
    (q : ℕ) (hq : 0 < q)
    (k l : XModLambdaN ((background.nu.functor.obj (X.obj background.auxiliary))⟦(1:ℤ)⟧) q ⟶
      (XModLambdaN (background.nu.functor.obj (X.obj background.auxiliary)) q)⟦(1:ℤ)⟧)
    (hk : XModLambdaN.incl _ q≫k=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q))
    (hl : XModLambdaN.incl _ q≫l=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ q)) :
    k=l := by
  exact ordinary_suspension_comparison_unique_of_negative_hom_zero _ q
    (finite_cell_native_negative_hom_zero X X hX q hq) k l hk hl

end
end KIP126.ProofTools.Internal.SyntheticCoverage
