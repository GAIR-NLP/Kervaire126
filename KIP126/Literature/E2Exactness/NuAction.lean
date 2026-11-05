module
public import KIP126.Literature.Standard.QuotientAlgebra
public import KIP126.Literature.Standard.Filtration
import all KIP126.Literature.Standard.FiniteQuotientNoReturn
import all KIP126.Literature.E2Exactness.Coordinates
import all KIP126.Literature.Standard.FiniteQuotientTriangle

/-! Comparison of the actual first-quotient map of ν with sphere action
in a bidegree with a unique nonzero class. All uniqueness premises are
local to this comparison; applications must prove them from sphere data. -/
@[expose] section
namespace KIP126.Literature.Standard.E2Exactness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed (background Spectrum SyntheticSpectrum)
open KIP126.Literature.Standard.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
private noncomputable def quotientBiSuspensionIso (q : ℤ) (Q : SyntheticSpectrum) :
    (SyntheticCategory.biShift (1, -q)).obj Q ≅
      ((SyntheticCategory.biShift (0, -q)).obj Q)⟦(1 : ℤ)⟧ := by
  have h : ((0 : ℤ), -q) + (1, 0) = (1, -q) := by ext <;> simp
  simpa only [h] using
    ((SyntheticCategory.biShift_comp (0, -q) (1, 0)).symm.app Q ≪≫
      (SyntheticCategory.biShift_compat (Syn := SyntheticSpectrum) 1).app
        ((SyntheticCategory.biShift (0, -q)).obj Q))

private theorem sphere_quotient_high_filtration_zero (q : ℕ) (hq : 0 < q)
    (m w s : ℤ) (hs : (q:ℤ) ≤ m+s-w)
    (a : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) q))
    (ha : FiltrationAtLeast background.syntheticTower s a) : a = 0 := by
  let g : XModLambdaN (S_0_0 : SyntheticSpectrum) q ⟶ XModLambdaN (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) q :=
    XModLambdaN.map background.nu.unitIso.inv q
  let f : XModLambdaN (background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) q ⟶ XModLambdaN (S_0_0 : SyntheticSpectrum) q :=
    XModLambdaN.map background.nu.unitIso.hom q
  have hm := map_preserves_filtration
    (background.convergentMap (.quotient q .sphere) (.quotient q (.nu .sphere)) g)
    (m,w) s a ha
  have hz := finite_high_filtration_zero .sphere q hq m w s hs (a ≫ g) hm
  have hgf : g ≫ f = 𝟙 _ := by
    dsimp only [f,g]
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,background.quotients.functoriality.map_id]
    rfl
  have he := congrArg (fun z => z ≫ f) hz
  change (a ≫ g) ≫ f = 0 ≫ f at he
  rw [Category.assoc,hgf,Category.comp_id,zero_comp] at he
  exact he

private theorem filtration_zero {X : SyntheticSpectrum} {m w : ℤ} (a : BiHom m w X) :
    FiltrationAtLeast background.syntheticTower 0 a := by
  let T := background.syntheticTower.tower X
  refine ⟨a ≫ T.zeroIso.inv,?_⟩
  change (a ≫ T.zeroIso.inv) ≫ T.projection 0=a
  dsimp only [AbstractAdamsTower.projection]
  rw [T.map_self]
  change (a ≫ T.zeroIso.inv) ≫ (𝟙 (T.stage 0) ≫ T.zeroIso.hom)=a
  rw [Category.id_comp,Category.assoc,Iso.inv_hom_id,Category.comp_id]

public theorem q1_sphere_action_actual_map_of_unique
    (m w : ℤ)
    (unique:∀u v:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
    (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
      (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom=
      (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1))
    (ν:BiHom 3 4 (S_0_0:SyntheticSpectrum))
    (x:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
    homotopyRegrade (add_comm 3 m) (add_comm 4 w) (sphereAction ν x)=(susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫
      κ.inv≫XModLambdaN.map ν 1 := by
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
    let e:T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 1 (-1):=(quotientBiSuspensionIso 1 (S_0_0:SyntheticSpectrum)).symm
    have he:e.inv≫δ=0 := by
      apply sphere_quotient_high_filtration_zero 1 (by decide) 1 (-1) 0 (by decide)
      exact filtration_zero (e.inv≫δ)
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
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)≫e.hom=
          (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1) := by
    obtain ⟨e,he⟩:=extend_unit_iso (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)
      ⟨unit_restriction_injective,unit_restriction_surjective ⟩
      (SyntheticCategory.biShift (3,4)) (tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4))
      (SyntheticCategory.biShift_fullyFaithful (3,4)) (tensorLeft_sphere_fullyFaithful 3 4)
      (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).symm (biShift_eq_tensor_Smn 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
    refine ⟨e,?_⟩
    simpa only [Iso.symm_hom,tensorLeft,curriedTensor_obj_map,id_tensorHom] using he
  have q1_pi_four_one_zero
      (z : BiHom 4 3 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) : z=0 := by
    apply sphere_quotient_high_filtration_zero 1 (by decide) 4 3 0 (by decide) z
    exact filtration_zero z
  have q1_sphere_inclusion_hom_injective :
      Function.Injective (fun f : XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ⟶
        XModLambdaN (S_0_0:SyntheticSpectrum) 1 => XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ f) := by
    intro f g hfg
    change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ f =
      XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ g at hfg
    let T := XModLambdaN.cofiberTriangle (Smn (Syn:=SyntheticSpectrum) 3 4) 1
    have hT : T ∈ distTriang SyntheticSpectrum := HasFunctorialCofiber.cofib_distinguished _
    have hz : T.mor₂ ≫ (f-g)=0 := by
      change XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≫ (f-g)=0
      rw [Preadditive.comp_sub,hfg,sub_self]
    obtain ⟨δ,hδ⟩ := T.yoneda_exact₃ hT (f-g) hz
    let e : T.obj₁⟦(1:ℤ)⟧ ≅ Smn (Syn:=SyntheticSpectrum) 4 3 :=
      (quotientBiSuspensionIso 1 (Smn (Syn:=SyntheticSpectrum) 3 4)).symm ≪≫
        (SyntheticCategory.biShift_comp (3,4) (1,-1)).app (S_0_0:SyntheticSpectrum)
    have he := q1_pi_four_one_zero (e.inv ≫ δ)
    have hd : δ=0 := by
      apply (cancel_epi e.inv).mp
      simpa only [comp_zero] using he
    apply sub_eq_zero.mp
    simpa only [hd, comp_zero] using hδ
  have q1_tensor_source_square

      (unique:∀u v:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1),u≠0→v≠0→u=v)
      (e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
        Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1)
      (d:Smn (Syn:=SyntheticSpectrum) (m+3) (w+4) ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) m w)
      (x:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) (hx:x≠0) :
      d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)=
        (susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom := by
    let F:=SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (3,4)
    let T:=tensorLeft (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=KIP126.AdamsSynthetic.Completed.graded_shiftAdditive (3,4)
    letI:=Standard.mayData.leftShift (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:=Standard.mayData.leftExact (Smn (Syn:=SyntheticSpectrum) 3 4)
    letI:T.Faithful:=tensorLeft_sphere_faithful 3 4
    let ff:=SyntheticCategory.biShift_fullyFaithful (Syn:=SyntheticSpectrum) (3,4)
    let c: F.obj (Smn (Syn:=SyntheticSpectrum) m w) ≅ Smn (Syn:=SyntheticSpectrum) (m+3) (w+4) :=
      (SyntheticCategory.biShift_comp (m,w) (3,4)).app (S_0_0:SyntheticSpectrum)
    let z:BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1):=
      ff.preimage (c.hom≫d.hom≫T.map x≫e.inv)
    have hz:F.map z=c.hom≫d.hom≫T.map x≫e.inv:=ff.map_preimage _
    have hzn:z≠0 := by
      intro h
      rw [h,Functor.map_zero] at hz
      have ht:T.map x=0 := by
        apply (cancel_epi (c.hom≫d.hom)).mp
        apply (cancel_mono e.inv).mp
        simpa only [Category.assoc,comp_zero,zero_comp] using hz.symm
      apply hx
      apply T.map_injective
      simpa only [Functor.map_zero] using ht
    have hzx:z=x:=unique z x hzn hx
    rw [hzx] at hz
    have heq:c.inv≫F.map x≫e.hom=d.hom≫T.map x := by
      rw [hz]
      simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
    change d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)=_
    dsimp only [susp_invariance]
    simp only [Equiv.trans_apply,Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply,Iso.refl_hom,Category.comp_id]
    simpa only [c,F,T,tensorLeft,curriedTensor_obj_map,id_tensorHom,Category.assoc] using heq.symm
  have q1_algebra_filler

      (κ:XModLambdaN (Smn (Syn:=SyntheticSpectrum) 3 4) 1 ≅
        (SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1))
      (hκ:XModLambdaN.incl (Smn (Syn:=SyntheticSpectrum) 3 4) 1≫κ.hom=
        (SyntheticCategory.biShift (3,4)).map (XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1)) :
      ∃e:(SyntheticCategory.biShift (3,4)).obj (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ XModLambdaN (S_0_0:SyntheticSpectrum) 1,
        letI:=Standard.quotientSyntheticSymmetric
        ∀ν:BiHom 3 4 (S_0_0:SyntheticSpectrum),
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
    rw [←Category.assoc (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ XModLambdaN.incl (S_0_0:SyntheticSpectrum) 1),
      tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
    rw [←Standard.quotientAlgebra_unit 1 (by decide)]
    have hm:=Mathlib.Tactic.MonTauto.rightUnitor_inv_tensor_one_mul (quotientClass 1 ν)
    change (ρ_ (Smn (Syn:=SyntheticSpectrum) 3 4)).inv≫(quotientClass 1 ν ⊗ₘ MonObj.one)≫MonObj.mul=quotientClass 1 ν at hm
    rw [hm]
    exact XModLambdaN.incl_naturality ν 1
  letI:=Standard.quotientSyntheticSymmetric
  let Q:=Standard.quotientAlgebra 1 (by decide)
  letI:=Q
  letI:=Standard.quotientAlgebra_commutative 1 (by decide)
  obtain ⟨e,he⟩:=q1_algebra_filler  κ hκ
  let d:Smn (Syn:=SyntheticSpectrum) (m+3) (w+4) ≅ Smn (Syn:=SyntheticSpectrum) 3 4 ⊗ Smn (Syn:=SyntheticSpectrum) m w :=
    eqToIso (congrArg (fun p : ℤ×ℤ => Smn (Syn:=SyntheticSpectrum) p.1 p.2)
      (show (m+3,w+4)=(3+m,4+w) by ext <;> dsimp <;> omega)) ≪≫
    ((SyntheticCategory.biShift_comp (3,4) (m,w)).app (S_0_0:SyntheticSpectrum)).symm ≪≫
      biShift_eq_tensor_Smn m w (Smn (Syn:=SyntheticSpectrum) 3 4) ≪≫ β_ (Smn (Syn:=SyntheticSpectrum) m w) (Smn (Syn:=SyntheticSpectrum) 3 4)
  have ht:=q1_tensor_source_square  unique e d x hx
  have hc:=IsCommMonObj.mul_comm (XModLambdaN (S_0_0:SyntheticSpectrum) 1)
  change (β_ (XModLambdaN (S_0_0:SyntheticSpectrum) 1) (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).hom≫Q.mul=Q.mul at hc
  have hb:(x ⊗ₘ quotientClass 1 ν)≫Q.mul=
      (β_ (Smn (Syn:=SyntheticSpectrum) m w) (Smn (Syn:=SyntheticSpectrum) 3 4)).hom≫
        (quotientClass 1 ν ⊗ₘ x)≫Q.mul := by
    rw [←hc,←Category.assoc,BraidedCategory.braiding_naturality,Category.assoc]
    simp only [hc]
  have hf:(quotientClass 1 ν ⊗ₘ x)=
      (𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫(quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)) := by
    rw [tensorHom_comp_tensorHom,Category.id_comp,Category.comp_id]
  rw [←Standard.quotientAlgebra_sphere_action 1 (by decide) 3 4 m w ν x]
  change homotopyRegrade (add_comm 3 m) (add_comm 4 w)
    (Standard.quotientAlgebraProduct Q (quotientClass 1 ν) x)=_
  calc
    _=d.hom≫(𝟙 (Smn (Syn:=SyntheticSpectrum) 3 4) ⊗ₘ x)≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      dsimp only [Standard.quotientAlgebraProduct,d,Iso.trans_hom,Iso.symm_hom,eqToIso.hom]
      rw [regrade_precomp,hb,hf]
      simp only [Category.assoc]
      rfl
    _=(susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) x)≫e.hom≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul := by
      simpa only [Category.assoc] using congrArg (fun z=>z≫
        (quotientClass 1 ν ⊗ₘ 𝟙 (XModLambdaN (S_0_0:SyntheticSpectrum) 1))≫Q.mul) ht
    _=_ := by
      rw [←he ν]
      simp only [Iso.inv_hom_id_assoc]

private def positiveNuSphereThreeIso :
    (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj ((AdamsObject.shift 3 .sphere).obj background.auxiliary)) ≅
      Smn (Syn:=SyntheticSpectrum) 3 4 :=
  (SyntheticCategory.biShift (0,1)).mapIso (nuSphereThree background) ≪≫
    (SyntheticCategory.biShift_comp (3,3) (0,1)).app S_0_0

/-- The exponent-one normalized map for the fixed Hopf ν. -/
public def positiveNuNormalizedMap :
    (SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj ((AdamsObject.shift 3 .sphere).obj background.auxiliary)) ⟶
      background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary) := by
  simpa only [KIP126.Literature.Standard.nuCofiber_nu_exponent,Nat.cast_one] using
    (background.normalizedMap (.shift 3 .sphere) .sphere background.auxiliary.nuMap).map

private theorem normalizedNu_positive_coordinates :
    KIP126.Literature.normalizedNu background KIP126.Literature.Standard.nuCofiber_nu_exponent =
      positiveNuSphereThreeIso.inv ≫ positiveNuNormalizedMap ≫ background.nu.unitIso.hom := by
  have H (n : ℕ) (hn : n=1)
      (F : (SyntheticCategory.biShift (0,(n:ℤ))).obj
        (background.nu.functor.obj ((AdamsObject.shift 3 .sphere).obj background.auxiliary)) ⟶
        background.nu.functor.obj (AdamsObject.sphere.obj background.auxiliary)) :
      (let E : (SyntheticCategory.biShift (0,(n:ℤ))).obj
          (background.nu.functor.obj ((AdamsObject.shift 3 .sphere).obj background.auxiliary)) ≅
          Smn (Syn:=SyntheticSpectrum) 3 4 := by
            rw [hn]
            exact positiveNuSphereThreeIso
       E.inv≫F≫background.nu.unitIso.hom) =
        positiveNuSphereThreeIso.inv≫
          (by simpa only [hn,Nat.cast_one,AdamsObject.obj, ClassicalObject.obj] using F)≫background.nu.unitIso.hom := by
    subst n
    rfl
  exact H _ KIP126.Literature.Standard.nuCofiber_nu_exponent _


/-- Vanishing of sphere action implies vanishing of the actual normalized ν
map on the first quotient. The unique-nonzero premise is discharged from
the sphere archive in the application to the top cell. -/
public theorem nu_quotient_operation_zero (m w : ℤ)
    (unique : ∀ u v : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) 1),
      u ≠ 0 → v ≠ 0 → u = v)
    (hact : ∀ z : BiHom m w (XModLambdaN (S_0_0 : SyntheticSpectrum) 1),
      sphereAction (KIP126.Literature.normalizedNu background nuCofiber_nu_exponent) z = 0)
    (a : BiHom (m+3) (w+4) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
      (background.nu.functor.obj ((AdamsObject.shift 3 .sphere).obj background.auxiliary))) 1)) :
    a ≫ XModLambdaN.map positiveNuNormalizedMap 1 = 0 := by
  letI := background.exactness.shiftCommShift (3,4)
  letI := background.exactness.shiftExact (3,4)
  obtain ⟨κ,hκ⟩ := finite_quotient_shift_comparison background.quotients.coherence (3,4) 1 (S_0_0:SyntheticSpectrum)
  let Q := (background.quotients.functoriality.functor 1).mapIso positiveNuSphereThreeIso
  let E : BiHom m w (XModLambdaN (S_0_0:SyntheticSpectrum) 1) ≃
      BiHom (m+3) (w+4) (XModLambdaN ((SyntheticCategory.biShift (0,1)).obj
        (background.nu.functor.obj ((AdamsObject.shift 3 .sphere).obj background.auxiliary))) 1) :=
    (susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1)).trans
      (Iso.homCongr (Iso.refl _) (κ.symm ≪≫ Q.symm))
  let z := E.symm a
  have ha : E z = a := E.apply_symm_apply a
  have haz : a = shiftHomotopyClass (3,4) (m,w) z ≫ κ.inv ≫
      XModLambdaN.map positiveNuSphereThreeIso.inv 1 := by
    rw [←ha]
    simp [E,Q,Iso.homCongr,susp_invariance,shiftHomotopyClass]
    rfl
  by_cases hz : z = 0
  · rw [haz,hz]
    simp only [shiftHomotopyClass,Functor.map_zero,comp_zero,zero_comp]
  · have hs := (q1_sphere_action_actual_map_of_unique m w unique κ hκ
      (KIP126.Literature.normalizedNu background nuCofiber_nu_exponent) z hz).symm
    rw [hact,regrade_zero] at hs
    have hsus : susp_invariance m w 3 4 (XModLambdaN (S_0_0:SyntheticSpectrum) 1) z =
        shiftHomotopyClass (3,4) (m,w) z := by
      simp [susp_invariance,shiftHomotopyClass,Iso.homCongr]
    rw [hsus,normalizedNu_positive_coordinates,background.quotients.functoriality.map_comp,
      background.quotients.functoriality.map_comp] at hs
    haveI : IsIso (XModLambdaN.map background.nu.unitIso.hom 1) := by
      change IsIso ((background.quotients.functoriality.functor 1).map background.nu.unitIso.hom)
      infer_instance
    apply (cancel_mono (XModLambdaN.map background.nu.unitIso.hom 1)).mp
    simpa only [haz,Category.assoc,zero_comp] using hs

end
end KIP126.Literature.Standard.E2Exactness
