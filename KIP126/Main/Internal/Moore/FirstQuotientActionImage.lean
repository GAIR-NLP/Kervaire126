module

import all KIP126.Main.Internal.Moore.ConstructionAction

/-! The first-quotient h₀ map has image contained in the sphere-action
image, with representatives chosen by the construction. -/

@[expose] section
namespace KIP126.Main.Internal.Moore
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.Main.Internal KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.AdamsSynthetic.Completed (background SyntheticSpectrum)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

private theorem q1_algebra_filler
    (κ : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
      (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ κ.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
    ∃ e : (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
        Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
      letI := Standard.quotientSyntheticSymmetric
      ∀ h : BiHom 0 1 (S_0_0:SyntheticSpectrum),
        κ.hom ≫ e.hom ≫ (quotientClass 1 h ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) ≫
          (Standard.quotientAlgebra 1 (by decide)).mul = XModLambdaN.map h 1 := by
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
  have lambda_first_kills_unit_hom
      (f:(S_0_0:SyntheticSpectrum)⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1) :
      lambdaPow 1 (S_0_0:SyntheticSpectrum)≫f=0 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.mayData.leftShift
    letI:=Standard.mayData.leftExact
    let l:BiHom 0 (-1) (S_0_0:SyntheticSpectrum):=lambdaPow 1 (S_0_0:SyntheticSpectrum)
    let z:BiHom 0 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=SyntheticCategory.biShift_zero.hom.app (S_0_0:SyntheticSpectrum)≫f
    have hl:quotientClass 1 l=0 := by
      change lambdaPow 1 (S_0_0:SyntheticSpectrum)≫XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1=0
      exact comp_distTriang_mor_zero₁₂ (XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1) (HasFunctorialCofiber.cofib_distinguished _)
    have ha:=Standard.quotientAlgebra_sphere_action 1 (by decide) 0 (-1) 0 0 l z
    have hp:Standard.quotientAlgebraProduct (Standard.quotientAlgebra 1 (by decide)) (quotientClass 1 l) z=0 := by
      rw [hl]
      unfold Standard.quotientAlgebraProduct
      have hz:z ⊗ₘ (0:BiHom 0 (-1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1))=0 := by
        rw [tensorHom_def]
        have hz':(XModLambdaN (S_0_0:SyntheticSpectrum) 1) ◁ (0:BiHom 0 (-1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1))=0 :=
          (tensorLeft (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).map_zero _ _
        rw [hz',comp_zero]
      simp only [hz,zero_comp,comp_zero]
    have haction:sphereAction l z=lambdaPow 1 (S_0_0:SyntheticSpectrum)≫f := by
      unfold sphereAction z l
      rw [←Category.assoc ((SyntheticCategory.biShift (0,0)).map (lambdaPow 1 (S_0_0:SyntheticSpectrum))),
        SyntheticCategory.biShift_zero.hom.naturality]
      have hc:(SyntheticCategory.biShift_comp (0,-1) (0,0)).hom.app (S_0_0:SyntheticSpectrum)=
        SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-1)):= by
        have hc := background.quotients.coherence.right_unit (0,-1) (S_0_0:SyntheticSpectrum)
        change (biShiftAddIso (0,-1) (0,0) (0,-1) (by decide)).hom.app (S_0_0:SyntheticSpectrum)=_ at hc
        simpa only [biShiftAddIso,Iso.trans_hom,NatTrans.comp_app,eqToIso.hom,eqToHom_app,eqToHom_refl,Category.comp_id,Smn] using hc
      change (SyntheticCategory.biShift_comp (0,-1) (0,0)).inv.app (S_0_0:SyntheticSpectrum)≫
        (SyntheticCategory.biShift_zero.hom.app (Smn (Syn:=SyntheticSpectrum) 0 (-1))≫lambdaPow 1 (S_0_0:SyntheticSpectrum))≫f=_
      rw [←hc]
      simp only [←Category.assoc,Iso.inv_hom_id_app,Category.id_comp]
    exact haction.symm.trans (ha.symm.trans hp)
  have unit_restriction_surjective
       :
      Function.Surjective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g) := by
    intro f
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1
    obtain ⟨g,hg⟩:=T.yoneda_exact₂ (HasFunctorialCofiber.cofib_distinguished _) f
      (lambda_first_kills_unit_hom  f)
    exact ⟨g,hg.symm⟩
  have unit_restriction_injective :
      Function.Injective (fun g:XModLambdaN (S_0_0:SyntheticSpectrum) 1⟶XModLambdaN (S_0_0:SyntheticSpectrum) 1 =>
        XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g) := by
    intro f g hfg
    change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫f=XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫g at hfg
    let T:=XModLambdaN.cofiberTriangle (S_0_0:SyntheticSpectrum) 1
    have hz:T.mor₂≫(f-g)=0 := by
      change XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1≫(f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩:=T.yoneda_exact₃ (HasFunctorialCofiber.cofib_distinguished _) (f-g) hz
    let e:T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 (-1):=(biSuspensionIso 1 (S_0_0:SyntheticSpectrum)).symm
    have he:e.inv≫δ=0 := by
      apply sphere_quotient_high_filtration_zero 1 (by decide) 1 (-1) 0 (by decide)
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
  have q1_unit_tensor_iso
       :
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (0,1)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 0 1))
      (SyntheticCategory.biShift_fullyFaithful (0,1)) (tensorLeft_sphere_fullyFaithful 0 1)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).symm (biShift_eq_tensor_Smn 0 1 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q1_pi_one_zero
      (z : BiHom 1 0 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) : z=0 := by
    apply sphere_quotient_high_filtration_zero 1 (by decide) 1 0 0 (by decide) z
    exact action_filtration_zero z
  have q1_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 1 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 0 1) 1
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 0 :=
      (biSuspensionIso 1 (Smn (Syn:=SyntheticSpectrum) 0 1)).symm ≪≫
        (SyntheticCategory.biShift_comp (0,1) (1,-1)).app (S_0_0:SyntheticSpectrum)
    have he := q1_pi_one_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q1_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≅
        (SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1≫κ.hom=
        (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
      ∃e:(SyntheticCategory.biShift (0,1)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 0 1 (S_0_0:SyntheticSpectrum),
        κ.hom≫e.hom≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫
          (Standard.quotientAlgebra 1 (by decide)).mul=XModLambdaN.map ν 1 := by
    letI:=Standard.quotientSyntheticSymmetric
    letI:=Standard.quotientAlgebra 1 (by decide)
    obtain ⟨e,he⟩:=q1_unit_tensor_iso
    refine ⟨e,?_⟩
    intro ν
    apply q1_sphere_inclusion_hom_injective
    simp only [←Category.assoc]
    rw [hκ,he]
    simp only [Category.assoc]
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 1 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 0 1)).inv≫(quotientClass 1 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 1 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 1
  exact q1_algebra_filler κ hκ


private theorem first_quotient_h0_action_image
    (b : BiHom 124 132 (XModLambdaN (Smn (Syn:=SyntheticSpectrum) 0 1) 1)) :
    ∃ z : BiHom 124 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 1),
      sphereAction KIP126.Literature.Standard.syntheticH0 z =
        b ≫ XModLambdaN.map KIP126.Literature.Standard.syntheticH0 1 := by
  letI := Standard.quotientSyntheticSymmetric
  let Q := Standard.quotientAlgebra 1 (by decide)
  letI := Q
  letI := Standard.quotientAlgebra_commutative 1 (by decide)
  let κ := (sphereQuotientShiftIso (0,1) 1).symm
  have hκ : XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 0 1) 1 ≫ κ.hom =
      (SyntheticCategory.biShift (0,1)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    have h := congrArg (fun f => f ≫ κ.hom) (sphere_quotient_shift_inclusion (0,1) 1)
    simpa only [κ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id, Smn] using h.symm
  obtain ⟨e, he⟩ := q1_algebra_filler κ hκ
  let d : Smn (Syn:=SyntheticSpectrum) 124 132 ≅
      Smn (Syn:=SyntheticSpectrum) 0 1 ⊗ Smn (Syn:=SyntheticSpectrum) 124 131 :=
    ((SyntheticCategory.biShift_comp (0,1) (124,131)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn 124 131 (Smn (Syn:=SyntheticSpectrum) 0 1) ≪≫
        β_ (Smn (Syn:=SyntheticSpectrum) 124 131) (Smn (Syn:=SyntheticSpectrum) 0 1)
  let tt := actionTensorFullyFaithful 0 1
  let a : BiHom 124 131 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) :=
    tt.preimage (d.inv ≫ b ≫ κ.hom ≫ e.hom)
  have ht : d.hom ≫ (Smn (Syn:=SyntheticSpectrum) 0 1 ◁ a) = b ≫ κ.hom ≫ e.hom := by
    have h := tt.map_preimage (d.inv ≫ b ≫ κ.hom ≫ e.hom)
    change Smn (Syn:=SyntheticSpectrum) 0 1 ◁ a = _ at h
    rw [h, ←Category.assoc, d.hom_inv_id, Category.id_comp]
  refine ⟨a, ?_⟩
  have hcomm := IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
    (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom ≫ Q.mul = Q.mul at hcomm
  let h0 := KIP126.Literature.Standard.syntheticH0
  have hb : (a ⊗ₘ quotientClass 1 h0) ≫ Q.mul =
      (β_ (Smn (Syn:=SyntheticSpectrum) 124 131) (Smn (Syn:=SyntheticSpectrum) 0 1)).hom ≫
        (quotientClass 1 h0 ⊗ₘ a) ≫ Q.mul := by
    rw [←hcomm, ←Category.assoc, BraidedCategory.braiding_naturality, Category.assoc]
    simp only [hcomm]
  have hp : quotientClass 1 h0 ⊗ₘ a =
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 0 1) ⊗ₘ a) ≫
        (quotientClass 1 h0 ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 1 (by decide) 0 1 124 131 h0 a]
  change Standard.quotientAlgebraProduct Q (quotientClass 1 h0) a = b ≫ XModLambdaN.map h0 1
  calc
    _ = d.hom ≫ (Smn (Syn:=SyntheticSpectrum) 0 1 ◁ a) ≫
        (quotientClass 1 h0 ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) ≫ Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct, d, Iso.trans_hom, Iso.symm_hom]
      rw [hb, hp]
      simp only [Category.assoc, id_tensorHom]
      rfl
    _ = (b ≫ κ.hom ≫ e.hom) ≫
        (quotientClass 1 h0 ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) ≫ Q.mul := by
      rw [←Category.assoc, ht]
    _ = b ≫ XModLambdaN.map h0 1 := by
      simpa only [Category.assoc] using congrArg (fun f => b ≫ f) (he h0)

end
end KIP126.Main.Internal.Moore
