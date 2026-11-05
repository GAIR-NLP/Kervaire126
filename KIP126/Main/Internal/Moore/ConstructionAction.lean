module

import all KIP126.Main.Internal.Moore.ConstructionAnnihilation
import all KIP126.Main.Internal.Moore.PrivateTensorFiltration
import all KIP126.Main.Internal.Moore.PrivateTensorFiltrationReflection
import all KIP126.Main.Internal.Moore.ConstructionCrossing

/-! The actual fourth-quotient h₀ map and a representative with the same
leading detector. All comparisons refer to the fixed quotient algebra. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.Main.Internal KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

private theorem action_filtration_zero {X : SyntheticSpectrum} {m w : ℤ} (a : BiHom m w X) :
    FiltrationAtLeast background.syntheticTower 0 a := by
  let T := background.syntheticTower.tower X
  refine ⟨a ≫ T.zeroIso.inv, ?_⟩
  change (a ≫ T.zeroIso.inv) ≫ T.projection 0 = a
  dsimp only [AbstractAdamsTower.projection]
  rw [T.map_self]
  change (a ≫ T.zeroIso.inv) ≫ (𝟙 (T.stage 0) ≫ T.zeroIso.hom) = a
  rw [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem q4_algebra_filler
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4))
    (hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≫ κ.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4)) :
    ∃ e : (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4) ≅
        Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 4,
      letI := Standard.quotientSyntheticSymmetric
      ∀ h : BiHom 0 1 (S_0_0:SyntheticSpectrum),
        κ.hom ≫ e.hom ≫ (quotientClass 4 h ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) ≫
          (Standard.quotientAlgebra 4 (by decide)).mul = XModLambdaN.map h 4 := by
  classical
  have tensorLeft_sphere_faithful (m n:ℤ) : (tensorLeft (Smn (Syn:=SyntheticSpectrum) m n)).Faithful := by
    let e : Smn (Syn:=SyntheticSpectrum) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ SyntheticSpectrum) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:SyntheticSpectrum) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:SyntheticSpectrum)
    let f : tensorLeft (Smn (Syn:=SyntheticSpectrum) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 SyntheticSpectrum :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
    exact Functor.Faithful.of_comp_iso f
  let tensorLeft_sphere_fullyFaithful (m n:ℤ) : (tensorLeft (Smn (Syn:=SyntheticSpectrum) m n)).FullyFaithful := by
    let e : Smn (Syn:=SyntheticSpectrum) (-m) (-n) ⊗ Smn m n ≅ (𝟙_ SyntheticSpectrum) :=
      (biShift_eq_tensor_Smn (-m) (-n) (Smn m n)).symm ≪≫
        (SyntheticCategory.biShift_comp (m,n) (-m,-n)).app (S_0_0:SyntheticSpectrum) ≪≫
          eqToIso (by simp [S_0_0]) ≪≫ SyntheticCategory.biShift_zero.app (S_0_0:SyntheticSpectrum)
    let f : tensorLeft (Smn (Syn:=SyntheticSpectrum) m n) ⋙ tensorLeft (Smn (-m) (-n)) ≅ 𝟭 SyntheticSpectrum :=
      (tensorLeftTensor _ _).symm ≪≫ (tensoringLeft SyntheticSpectrum).mapIso e ≪≫ leftUnitorNatIso SyntheticSpectrum
    letI := tensorLeft_sphere_faithful (-m) (-n)
    exact Functor.FullyFaithful.ofCompFaithful ((Functor.FullyFaithful.ofFullyFaithful (𝟭 SyntheticSpectrum)).ofIso f.symm)
  have lambda_fourth_kills_unit_hom
      (f:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 4) :
      lambdaPow 4 (S_0_0:SyntheticSpectrum)≫f=0 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.mayData.leftShift
    letI:=Standard.mayData.leftExact
    let l:BiHom 0 (-4) (S_0_0:SyntheticSpectrum):=lambdaPow 4 (S_0_0:SyntheticSpectrum)
    let z:BiHom 0 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 4):=SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)≫f
    have hl:quotientClass 4 l=0 := by
      change lambdaPow 4 (S_0_0:SyntheticSpectrum)≫XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4=0
      exact comp_distTriang_mor_zero₁₂ (XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 4) (HasFunctorialCofiber.cofib_distinguished _)
    have ha:=Standard.quotientAlgebra_sphere_action 4 (by decide) 0 (-4) 0 0 l z
    have hp:Standard.quotientAlgebraProduct (Standard.quotientAlgebra 4 (by decide)) (quotientClass 4 l) z=0 := by
      rw [hl]
      unfold Standard.quotientAlgebraProduct
      have hz:z ⊗ₘ (0:BiHom 0 (-4) (XModLambdaN (S_0_0:SyntheticSpectrum) 4))=0 := by
        rw [tensorHom_def]
        have hz':(XModLambdaN (S_0_0:SyntheticSpectrum) 4) ◁ (0:BiHom 0 (-4) (XModLambdaN (S_0_0:SyntheticSpectrum) 4))=0 :=
          (tensorLeft (XModLambdaN (S_0_0:SyntheticSpectrum) 4)).map_zero _ _
        rw [hz',comp_zero]
      simp only [hz,zero_comp,comp_zero]
    have haction:sphereAction l z=lambdaPow 4 (S_0_0:SyntheticSpectrum)≫f := by
      unfold sphereAction z l
      rw [←Category.assoc ((SyntheticCategory.biShift (0,0)).map (lambdaPow 4 (S_0_0:SyntheticSpectrum))),
        SyntheticCategory.biShift_zero.hom.naturality]
      have hc:(SyntheticCategory.biShift_comp (0,-4) (0,0)).hom.app (S_0_0:SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-4)):= by
        have hc := background.quotients.coherence.right_unit (0,-4) (S_0_0:SyntheticSpectrum)
        change (biShiftAddIso (0,-4) (0,0) (0,-4) (by decide)).hom.app (S_0_0:SyntheticSpectrum)=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      change (SyntheticCategory.biShift_comp (0,-4) (0,0)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-4))≫lambdaPow 4 (S_0_0:SyntheticSpectrum))≫f=_
      rw [←hc]
      simp only [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    exact haction.symm.trans (ha.symm.trans hp)
  have unit_restriction_surjective
       :
      Function.Surjective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 4⟶XModLambdaN (S_0_0:SyntheticSpectrum) 4 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4≫g) := by
    intro f
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 4
    obtain ⟨g,hg⟩:=T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished _) f
      (lambda_fourth_kills_unit_hom  f)
    exact ⟨g,hg.symm⟩
  have unit_restriction_injective :
      Function.Injective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 4⟶XModLambdaN (S_0_0:SyntheticSpectrum) 4 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4≫g) := by
    intro f g hfg
    change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4≫f=XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4≫g at hfg
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 4
    have hz:T.mor₂≫(f-g)=0 := by
      change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4≫(f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩:=T.yoneda_exact₃ (HasFunctorialCofiber.cofib_distinguished _) (f-g) hz
    let e:T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 (-4):=(biSuspensionIso 4 (S_0_0:SyntheticSpectrum)).symm
    have he:e.inv≫δ=0 := by
      apply sphere_quotient_high_filtration_zero 4 (by decide) 1 (-4) 0 (by decide)
      exact action_filtration_zero (e.inv≫δ)
    have hd:δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd,comp_zero] using hδ
  have extend_unit_iso
      {S A:SyntheticSpectrum} (i:S⟶A)
      (hi:Function.Bijective (fun g:A⟶A=>i≫g))
      (F T:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful) (tt:T.FullyFaithful)
      (eS:F.obj S≅T.obj S) (eA:F.obj A≅T.obj A) :
      ∃E:F.obj A≅T.obj A,F.map i≫E.hom=eS.hom≫T.map i := by
    have lift (F T:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful)
        (eA:F.obj A≅T.obj A) (f:F.obj S⟶T.obj A) :
        ∃g:F.obj A⟶T.obj A,F.map i≫g=f := by
      let z:=ff.preimage (f≫eA.inv)
      obtain ⟨g,hg⟩:=hi.2 z
      change i≫g=z at hg
      refine ⟨F.map g≫eA.hom,?_⟩
      rw [←Category.assoc,←F.map_comp,hg]
      have hz:F.map z=f≫eA.inv:=ff.map_preimage _
      rw [hz,Category.assoc,Iso.inv_hom_id,Category.comp_id]
    have inj (F:SyntheticSpectrum⥤SyntheticSpectrum) (ff:F.FullyFaithful)
        {a b:F.obj A⟶F.obj A} (h:F.map i≫a=F.map i≫b) :a=b := by
      obtain ⟨a',rfl⟩:=ff.map_surjective a
      obtain ⟨b',rfl⟩:=ff.map_surjective b
      rw [←F.map_comp,←F.map_comp] at h
      exact congrArg F.map (hi.1 (ff.map_injective h))
    obtain ⟨f,hf⟩:=lift F T ff eA (eS.hom≫T.map i)
    obtain ⟨g,hg⟩:=lift T F tt eA.symm (eS.inv≫F.map i)
    have hfg:f≫g=𝟙 _ := by
      apply inj F ff
      rw [←Category.assoc,hf,Category.assoc,hg,←Category.assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id]
    have hgf:g≫f=𝟙 _ := by
      apply inj T tt
      rw [←Category.assoc,hg,Category.assoc,hf,←Category.assoc,Iso.inv_hom_id,Category.id_comp,Category.comp_id]
    exact ⟨⟨f,g,hfg,hgf⟩,hf⟩
  have q4_unit_tensor_iso
       :
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 4,
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (0,1)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 0 1))
      (SyntheticCategory.biShift_fullyFaithful (0,1)) (tensorLeft_sphere_fullyFaithful 0 1)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).symm (biShift_eq_tensor_Smn 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 4))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q4_pi_one_neg_three_zero
      (z : BiHom 1 (-3) (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) : z=0 := by
    apply sphere_quotient_high_filtration_zero 4 (by decide) 1 (-3) 0 (by decide) z
    exact action_filtration_zero z
  have q4_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 4 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 0 1) 4
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 (-3) :=
      (biSuspensionIso 4 (Smn (Syn:=SyntheticSpectrum) 0 1)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (1,-4)).app (S_0_0:SyntheticSpectrum)
    have he := q4_pi_one_neg_three_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q4_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≅
        (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4≫κ.hom=
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4)) :
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 4,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 0 1 (S_0_0:SyntheticSpectrum),
        κ.hom≫e.hom≫(quotientClass 4 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 4))≫
          (Standard.quotientAlgebra 4 (by decide)).mul=XModLambdaN.map ν 4 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.quotientAlgebra 4 (by decide)
    obtain ⟨e,he⟩:=q4_unit_tensor_iso
    refine ⟨e,?_⟩
    intro ν
    apply q4_sphere_inclusion_hom_injective
    simp only [←Category.assoc]
    rw [hκ,he]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 4 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 4 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(quotientClass 4 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 4 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 4
  exact q4_algebra_filler κ hκ

private def q4H0SourceShiftIso :
    (SyntheticCategory.biShift (1,0)).obj (XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 4) ≅
      XModLambdaN (Smn (Syn:=SyntheticSpectrum) 1 1) 4 :=
  (KIP126.Main.Internal.NuThree.quotient_shift_iso (1,0) (Smn (Syn:=SyntheticSpectrum) 0 1) 4).choose ≪≫
    (background.quotients.functoriality.functor 4).mapIso
      ((SyntheticCategory.biShift_comp (0,1) (1,0)).app (S_0_0:SyntheticSpectrum))

private theorem q4_h0_source_shift_inclusion :
    (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4) ≫
      q4H0SourceShiftIso.hom =
    (SyntheticCategory.biShift_comp (0,1) (1,0)).hom.app (S_0_0:SyntheticSpectrum) ≫
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 1 1) 4 := by
  have h := (KIP126.Main.Internal.NuThree.quotient_shift_iso
    (1,0) (Smn (Syn:=SyntheticSpectrum) 0 1) 4).choose_spec
  dsimp only [q4H0SourceShiftIso, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  rw [←Category.assoc, h]
  exact (XModLambdaN.incl_naturality _ 4).symm

private theorem q4_suspended_inclusion_injective :
    Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 1 1) 4 ⟶
      (SyntheticCategory.biShift (1,0)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4) =>
        XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 1 1) 4 ≫ f) := by
  intro f g hfg
  change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 1 1) 4 ≫ f =
    XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 1 1) 4 ≫ g at hfg
  let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 1 1) 4
  have hz : T.mor₂ ≫ (f-g) = 0 := by
    change XModLambdaN.incl _ _ ≫ (f-g) = 0
    rw [Preadditive.comp_sub, hfg, sub_self]
  obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ (XModLambdaN.cofiberTriangle_distinguished _ _) (f-g) hz
  let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 2 (-3) :=
    (biSuspensionIso 4 (Smn (Syn:=SyntheticSpectrum) 1 1)).symm ≪≫
      (SyntheticCategory.biShift_comp (1,1) (1,-4)).app (S_0_0:SyntheticSpectrum)
  let E : BiHom 1 (-3) (XModLambdaN (S_0_0:SyntheticSpectrum) 4) ≃+
      BiHom 2 (-3) ((SyntheticCategory.biShift (1,0)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) :=
    { toEquiv := susp_invariance 1 (-3) 1 0 _
      map_add' := susp_invariance_add 1 (-3) 1 0 _ }
  have he : E.symm (e.inv ≫ δ) = 0 := by
    apply sphere_quotient_high_filtration_zero 4 (by decide) 1 (-3) 0 (by decide)
    exact action_filtration_zero _
  have hd : δ = 0 := by
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using E.symm.map_eq_zero_iff.mp he
  apply sub_eq_zero.mp
  simpa only [hd, comp_zero] using hδ

private theorem q4_suspended_h0_natural :
    XModLambdaN.map mooreShiftedH0 4 ≫ (sphereQuotientShiftIso (1,0) 4).inv =
      q4H0SourceShiftIso.inv ≫
        (SyntheticCategory.biShift (1,0)).map
          (XModLambdaN.map KIP126.Literature.Standard.syntheticH0 4) := by
  apply q4_suspended_inclusion_injective
  have ht : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 1 0) 4 ≫
      (sphereQuotientShiftIso (1,0) 4).inv =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4) := by
    have h := congrArg (fun f => f ≫ (sphereQuotientShiftIso (1,0) 4).inv)
      (sphere_quotient_shift_inclusion (1,0) 4)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Smn] using h.symm
  have hs : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 1 1) 4 ≫ q4H0SourceShiftIso.inv =
      (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app (S_0_0:SyntheticSpectrum) ≫
        (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4) := by
    have h := congrArg (fun f =>
      (SyntheticCategory.biShift_comp (0,1) (1,0)).inv.app (S_0_0:SyntheticSpectrum) ≫
        f ≫ q4H0SourceShiftIso.inv) q4_h0_source_shift_inclusion
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_app_assoc] using h.symm
  simp only [←Category.assoc]
  rw [←XModLambdaN.incl_naturality, Category.assoc, ht, hs]
  simp only [mooreShiftedH0, Category.assoc, ←CategoryTheory.Functor.map_comp]
  rw [XModLambdaN.incl_naturality]
  rfl

private def q4OrdinaryTop
    (a : BiHom 123 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) :
    BiHom 123 132 (XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 4) :=
  (susp_invariance 123 132 1 0 _).symm
    (susp_invariance 123 131 1 1 _ a ≫
      (sphereQuotientShiftIso (1,1) 4).hom ≫ q4H0SourceShiftIso.inv)

private theorem q4_ordinary_top_h0_zero
    (c : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4)) :
    q4OrdinaryTop (mooreTopImage c) ≫
      XModLambdaN.map KIP126.Literature.Standard.syntheticH0 4 = 0 := by
  let E : BiHom 123 132 (XModLambdaN (S_0_0:SyntheticSpectrum) 4) ≃+
      BiHom 124 132 ((SyntheticCategory.biShift (1,0)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) :=
    { toEquiv := susp_invariance 123 132 1 0 _
      map_add' := susp_invariance_add 123 132 1 0 _ }
  apply E.map_eq_zero_iff.mp
  have h := congrArg (fun z => z ≫ (sphereQuotientShiftIso (1,0) 4).inv)
    (moore_top_image_actual_h0_zero c)
  simp only [Category.assoc, zero_comp] at h
  rw [q4_suspended_h0_natural] at h
  have hs : susp_invariance 123 132 1 0 _ (q4OrdinaryTop (mooreTopImage c)) =
      susp_invariance 123 131 1 1 _ (mooreTopImage c) ≫
        (sphereQuotientShiftIso (1,1) 4).hom ≫ q4H0SourceShiftIso.inv :=
    Equiv.apply_symm_apply _ _
  have hc : E (q4OrdinaryTop (mooreTopImage c) ≫
        XModLambdaN.map KIP126.Literature.Standard.syntheticH0 4) =
      susp_invariance 123 132 1 0 _ (q4OrdinaryTop (mooreTopImage c)) ≫
        (SyntheticCategory.biShift (1,0)).map
          (XModLambdaN.map KIP126.Literature.Standard.syntheticH0 4) := by
    change susp_invariance 123 132 1 0 _ (q4OrdinaryTop (mooreTopImage c) ≫
      XModLambdaN.map KIP126.Literature.Standard.syntheticH0 4) = _
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_apply,
      Iso.refl_hom, Category.comp_id, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hc, hs]
  simpa only [Category.assoc] using h

private theorem action_shift_filtration_iff (A : SyntheticObject (coefficients := background.coefficients)) (δ p : ℤ × ℤ)
    (s : ℤ) (a : BiHom p.1 p.2 (A.obj background.nu background.auxiliary)) :
    FiltrationAtLeast background.syntheticTower s (shiftHomotopyClass δ p a) ↔
      FiltrationAtLeast background.syntheticTower s a := by
  let e := (KIP126.AdamsSynthetic.Completed.essShift δ).filtered A p
  have forward {A B : SyntheticSpectrum} {p q : ℤ × ℤ}
      (e : FilteredPieceIso (background.syntheticTower.filtration A)
        (background.syntheticTower.filtration B) p q)
      (a : BiHom p.1 p.2 A) (ha : FiltrationAtLeast background.syntheticTower s a) :
      FiltrationAtLeast background.syntheticTower s (e.ambient.hom a) := by
    obtain ⟨ar,har⟩ := filtration_representative_exists background.syntheticTower A p s a ha
    have hh := ConcreteCategory.congr_hom (e.level_arrow s) ar
    have hm : e.ambient.hom a ∈ ModuleCat.subobjectModule _
        ((background.syntheticTower.filtration B).F s q) := by
      refine ⟨(e.level s).hom ar,?_⟩
      simpa only [ModuleCat.comp_apply,har] using hh
    simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
      FiltrationAtLeast] using hm
  rw [←(KIP126.AdamsSynthetic.Completed.essShift δ).ambient_eq A p a]
  constructor
  · intro ha
    have h := forward e.symm _ ha
    change FiltrationAtLeast background.syntheticTower s (e.ambient.inv (e.ambient.hom a)) at h
    have he : e.ambient.inv (e.ambient.hom a) = a :=
      ConcreteCategory.congr_hom e.ambient.hom_inv_id a
    rwa [he] at h
  · exact forward e a

private theorem action_map_filtration {X Y : SyntheticSpectrum} (f : X ⟶ Y)
    (s m w : ℤ) (a : BiHom m w X) (ha : FiltrationAtLeast background.syntheticTower s a) :
    FiltrationAtLeast background.syntheticTower s (a ≫ f) := by
  obtain ⟨b,hb⟩ := ha
  let φ := background.syntheticTower.map f
  refine ⟨b ≫ φ.stage s.toNat, ?_⟩
  change (b ≫ φ.stage s.toNat) ≫ (background.syntheticTower.tower Y).projection s = a ≫ f
  rw [Category.assoc, φ.projection, ←Category.assoc]
  exact congrArg (fun z => z ≫ f) hb

private theorem action_iso_filtration_iff {X Y : SyntheticSpectrum} (e : X ≅ Y)
    (s m w : ℤ) (a : BiHom m w X) :
    FiltrationAtLeast background.syntheticTower s (a ≫ e.hom) ↔
      FiltrationAtLeast background.syntheticTower s a := by
  constructor
  · intro h
    have ht := action_map_filtration e.inv s m w (a ≫ e.hom) h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ht
  · exact action_map_filtration e.hom s m w a

private theorem action_susp_filtration_iff
    (X : SyntheticObject (coefficients := background.coefficients))
    (s m w k l : ℤ) (a : BiHom m w (X.obj background.nu background.auxiliary)) :
    FiltrationAtLeast background.syntheticTower s (susp_invariance m w k l _ a) ↔
      FiltrationAtLeast background.syntheticTower s a := by
  simpa only [susp_invariance, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
    Iso.homCongr_apply, Iso.refl_hom, Category.comp_id, shiftHomotopyClass, Iso.app_inv]
    using action_shift_filtration_iff X (k,l) (m,w) s a

private theorem q4_ordinary_top_filtration_iff (s : ℤ)
    (a : BiHom 123 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) :
    FiltrationAtLeast background.syntheticTower s (q4OrdinaryTop a) ↔
      FiltrationAtLeast background.syntheticTower s a := by
  have h := action_susp_filtration_iff (.quotient 4 (.shift (0,1) .sphere))
    s 123 132 1 0 (q4OrdinaryTop a)
  have he : susp_invariance 123 132 1 0 _ (q4OrdinaryTop a) =
      susp_invariance 123 131 1 1 _ a ≫
        (sphereQuotientShiftIso (1,1) 4).hom ≫ q4H0SourceShiftIso.inv :=
    Equiv.apply_symm_apply _ _
  erw [he] at h
  have h₁ := action_iso_filtration_iff q4H0SourceShiftIso.symm s 124 132
    (susp_invariance 123 131 1 1 _ a ≫ (sphereQuotientShiftIso (1,1) 4).hom)
  have h₂ := action_iso_filtration_iff (sphereQuotientShiftIso (1,1) 4) s 124 132
    (susp_invariance 123 131 1 1 _ a)
  apply h.symm.trans
  simpa only [Category.assoc, Iso.symm_hom] using h₁.trans (h₂.trans
    (action_susp_filtration_iff (.quotient 4 .sphere) s 123 131 1 1 a))

private theorem action_tensor_faithful (m w : ℤ) :
    (tensorLeft (Smn (Syn:=SyntheticSpectrum) m w)).Faithful := by
  let E : tensorLeft (Smn (Syn:=SyntheticSpectrum) m w) ⋙
      tensorLeft (Smn (-m) (-w)) ≅ 𝟭 SyntheticSpectrum :=
    (tensorLeftTensor _ _).symm ≪≫
      (tensoringLeft SyntheticSpectrum).mapIso (sphereTensorInverseIso m w) ≪≫
        leftUnitorNatIso SyntheticSpectrum
  exact Functor.Faithful.of_comp_iso E

private def actionTensorFullyFaithful (m w : ℤ) :
    (tensorLeft (Smn (Syn:=SyntheticSpectrum) m w)).FullyFaithful := by
  let E : tensorLeft (Smn (Syn:=SyntheticSpectrum) m w) ⋙
      tensorLeft (Smn (-m) (-w)) ≅ 𝟭 SyntheticSpectrum :=
    (tensorLeftTensor _ _).symm ≪≫
      (tensoringLeft SyntheticSpectrum).mapIso (sphereTensorInverseIso m w) ≪≫
        leftUnitorNatIso SyntheticSpectrum
  letI := action_tensor_faithful (-m) (-w)
  exact Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful (𝟭 SyntheticSpectrum)).ofIso E.symm)

/-- The top-cell representative gives a sphere-action-annihilated
representative of the same nonzero filtration-nine class. -/
private theorem moore_fourth_action_representative
    (c : BiHom 124 132 (XModLambdaN
      (background.nu.functor.obj KIP126.AdamsComputation.Moore.spectrum) 4))
    (ha : FiltrationAtLeast background.syntheticTower 9 (mooreTopImage c))
    (hn : ¬FiltrationAtLeast background.syntheticTower 10 (mooreTopImage c)) :
    ∃ a : BiHom 123 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 4),
      FiltrationAtLeast background.syntheticTower 9 a ∧
      ¬FiltrationAtLeast background.syntheticTower 10 a ∧
      sphereAction KIP126.Literature.Standard.syntheticH0 a = 0 := by
  letI := Standard.quotientSyntheticSymmetric
  let Q := Standard.quotientAlgebra 4 (by decide)
  letI := Q
  letI := Standard.quotientAlgebra_commutative 4 (by decide)
  let κ := (sphereQuotientShiftIso (0,1) 4).symm
  have hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 4 ≫ κ.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 4) := by
    have h := congrArg (fun f => f ≫ κ.hom) (sphere_quotient_shift_inclusion (0,1) 4)
    simpa only [κ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id, Smn] using h.symm
  obtain ⟨e, he⟩ := q4_algebra_filler κ hκ
  let d : Smn (Syn:=SyntheticSpectrum) 123 132 ≅
      Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ Smn (Syn:=SyntheticSpectrum) 123 131 :=
    ((SyntheticCategory.biShift_comp (0,1) (123,131)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn 123 131 (Smn (Syn:=SyntheticSpectrum) 0 1) ≪≫
        β_ (Smn (Syn:=SyntheticSpectrum) 123 131) (Smn (Syn:=SyntheticSpectrum) 0 1)
  let b := q4OrdinaryTop (mooreTopImage c)
  let tt := actionTensorFullyFaithful 0 1
  let a : BiHom 123 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 4) :=
    tt.preimage (d.inv ≫ b ≫ κ.hom ≫ e.hom)
  have ht : d.hom ≫ (Smn (Syn:=SyntheticSpectrum) 0 1 ◁ a) = b ≫ κ.hom ≫ e.hom := by
    have h := tt.map_preimage (d.inv ≫ b ≫ κ.hom ≫ e.hom)
    change Smn (Syn:=SyntheticSpectrum) 0 1 ◁ a = _ at h
    rw [h, ←Category.assoc, d.hom_inv_id, Category.id_comp]
  have hf (s : ℤ) : FiltrationAtLeast background.syntheticTower s a ↔
      FiltrationAtLeast background.syntheticTower s (mooreTopImage c) := by
    have h := tensor_left_sphere_filtration_iff background.syntheticTower
      0 1 s 123 131 123 132 a d
    rw [ht] at h
    apply h.symm.trans
    simpa only [Category.assoc] using (action_iso_filtration_iff e s 123 132 (b ≫ κ.hom)).trans
      ((action_iso_filtration_iff κ s 123 132 b).trans
        (q4_ordinary_top_filtration_iff s (mooreTopImage c)))
  refine ⟨a, (hf 9).mpr ha, fun h => hn ((hf 10).mp h), ?_⟩
  have hcomm := IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 4)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 4)
    (XModLambdaN (S_0_0:SyntheticSpectrum) 4)).hom ≫ Q.mul = Q.mul at hcomm
  let h0 := KIP126.Literature.Standard.syntheticH0
  have hb : (a ⊗ₘ quotientClass 4 h0) ≫ Q.mul =
      (β_ (Smn (Syn:=SyntheticSpectrum) 123 131) (Smn (Syn:=SyntheticSpectrum) 0 1)).hom ≫
        (quotientClass 4 h0 ⊗ₘ a) ≫ Q.mul := by
    rw [←hcomm, ←Category.assoc, BraidedCategory.braiding_naturality, Category.assoc]
    simp only [hcomm]
  have hp : quotientClass 4 h0 ⊗ₘ a =
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ a) ≫
        (quotientClass 4 h0 ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 4 (by decide) 0 1 123 131 h0 a]
  change Standard.quotientAlgebraProduct Q (quotientClass 4 h0) a = 0
  calc
    _ = d.hom ≫ (Smn (Syn:=SyntheticSpectrum) 0 1 ◁ a) ≫
        (quotientClass 4 h0 ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) ≫ Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct, d, Iso.trans_hom, Iso.symm_hom]
      rw [hb, hp]
      simp only [Category.assoc, id_tensorHom]
      rfl
    _ = (b ≫ κ.hom ≫ e.hom) ≫
        (quotientClass 4 h0 ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 4)) ≫ Q.mul := by
      rw [←Category.assoc, ht]
    _ = b ≫ XModLambdaN.map h0 4 := by
      simpa only [Category.assoc] using congrArg (fun f => b ≫ f) (he h0)
    _ = 0 := q4_ordinary_top_h0_zero c


end
end KIP126.Main.Internal.Moore
