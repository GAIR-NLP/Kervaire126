module
import all KIP126.Main.SectionSeven.WeakStripFinite
import all KIP126.Main.SectionSeven.WeakStripTorsion
import all KIP126.Main.SectionSeven.WeakYDetection
import all KIP126.Main.Internal.NuFifth.Frame
/-! Two-layer representative adjustment from the finite table calculations
and common representatives on the fixed quotients. -/
@[expose] section
namespace KIP126.Main.SectionSeven.Internal
open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.AdamsSynthetic
open KIP126.Core.Algebra KIP126.Core.SpectralSequence KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Completed KIP126.Main.Internal KIP126.Main.Internal.Selected
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald KIP126.Main.Internal.Selected.NuError
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

private theorem strip_af7_all_labels (x : background.classical.sphere.Page 2 (7,132)) :
    x=0 ∨ x=KIP126.Computation.Table.basis .sphere 7 132 0 := by
  rcases WeakStripFinite.main_af7_all_labels (Normalized.label (7,132) x) with h|h
  · left
    have h := congrArg (denormalize (7,132)) h
    simpa only [denormalize_label,map_zero] using h
  · right
    have h := congrArg (denormalize (7,132)) h
    rw [denormalize_label] at h
    exact h.trans (denormalize_basis 7 132 0)

private theorem strip_af7_label_boundary : KIP126.Computation.Table.basis .sphere 7 132 0
    ∈boundaries background .sphere 3 (7,132) := by
  have h := WeakStripFinite.main_af7_label_boundary
  change denormalize (7,132) (Normalized.basis .sphere 7 132 0)∈boundaries background .sphere 3 (7,132) at h
  exact (denormalize_basis 7 132 0) ▸ h

private theorem strip_h6b_cosets (x : background.classical.sphere.Page 2 (9,134))
    (hx : x∈cycles background .sphere 7 (9,134)) :
    x∈boundaries background .sphere 3 (9,134) ∨
    x-(show background.classical.sphere.Page 2 (9,134) from KIP126.Computation.Table.basis .sphere 9 134 2)
      ∈boundaries background .sphere 3 (9,134) := by
  have hx' : Normalized.label (9,134) x∈nCycles 7 (9,134) := by
    change denormalize (9,134) (Normalized.label (9,134) x)∈cycles background .sphere 7 (9,134)
    rwa [denormalize_label]
  rcases WeakStripFinite.main_h6b_finite_cosets _ hx' with h|h
  · left
    change denormalize (9,134) (Normalized.label (9,134) x)∈boundaries background .sphere 3 (9,134) at h
    rwa [denormalize_label] at h
  · right
    change denormalize (9,134) (Normalized.label (9,134) x-Normalized.basis .sphere 9 134 2)
      ∈boundaries background .sphere 3 (9,134) at h
    rw [map_sub,denormalize_label] at h
    exact (denormalize_basis 9 134 2) ▸ h

private theorem strip_af8_boundary : cycles background .sphere 8 (8,133) ≤ boundaries background .sphere 2 (8,133) := by
  intro x hx
  have hx' : Normalized.label (8,133) x∈nCycles 8 (8,133) := by
    change denormalize (8,133) (Normalized.label (8,133) x)∈cycles background .sphere 8 (8,133)
    rwa [denormalize_label]
  have h := WeakStripFinite.main_af8_cycles_boundary hx'
  change denormalize (8,133) (Normalized.label (8,133) x)∈boundaries background .sphere 2 (8,133) at h
  rwa [denormalize_label] at h

private theorem strip_low_even_quotient_zero (s : ℤ) (hs : s=8 ∨ s=10) :
    Subsingleton (CycleQuotient background .sphere (16-s) (s-6) (s,125+s)) := by
  have hc : cycles background .sphere (16-s) (s,125+s) ≤ boundaries background .sphere (s-6) (s,125+s) := by
    rcases hs with rfl|rfl
    · exact strip_af8_boundary
    · exact (cycles_antitone background .sphere (10,135) (by decide : (4:ℤ)≤6)).trans
        (KIP126.Main.Internal.NuFifth.nu_af10_cycles_boundary.trans
          (boundaries_monotone background .sphere (10,135) (by decide : (2:ℤ)≤4)))
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨x,rfl⟩ := Quotient.exists_rep x
  exact (subquotientClass_eq_zero_iff _ _ _).mpr (hc x.property)

private theorem strip_low_even_gap (s : ℤ) (hs : s=8 ∨ s=10)
    (a : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)) :
    FiltrationAtLeast background.syntheticTower s a ↔ FiltrationAtLeast background.syntheticTower (s+1) a := by
  apply filtration_iff_of_infinity_zero (background.convergence (.quotient 9 .sphere)) s (s+1) 125 132 (by omega)
  intro j hj hj'
  have : j=s := by omega
  subst j
  apply finite_sphere_zero_of_classical_quotient 9 (by decide) s (125+s) 132
    (by rcases hs with rfl|rfl <;> norm_num)
  convert strip_low_even_quotient_zero s hs using 1 <;> congr 1 <;> omega

private theorem finite_sphere_frame_of_cosets (q k : ℕ) (hq : 0<q) (hk : k<q) (s t : ℤ)
    (y0 : background.classical.sphere.Page 2 (s,t))
    (hframe : ∀x : background.classical.sphere.Page 2 (s,t),
      x∈cycles background .sphere ((q:ℤ)-k) (s,t) →
      x∈boundaries background .sphere (k+1) (s,t) ∨ x-y0∈boundaries background .sphere (k+1) (s,t)) :
    ∀ e : ((background.family.quotient (S_0_0 : SyntheticSpectrum) q).sequence.ssData (s,t,t-k)).eInfty,
      e=0 ∨ HasInfinityRepresentative (background.family.quotient (S_0_0 : SyntheticSpectrum) q)
        2 (s,t,t-k) (quotientLabel q s t k y0) e := by
  intro e
  by_cases hne : e=0
  · exact Or.inl hne
  right
  obtain ⟨x,hx,he⟩ := finite_sphere_infinity_cycle_label_exists q k hq hk s t e
  have hn : x∉boundaries background .sphere (k+1) (s,t) := by
    intro hb
    have hz := finite_sphere_boundary_detects_zero q k hq hk s t x
      (by rwa [add_comm] at hb)
    exact nonzero_detection_ne_zero (.quotient q .sphere) (s,t,t-k)
      (quotientLabel q s t k x) 0 ⟨hz,e,he,hne⟩ rfl
  have hb := (hframe x hx).resolve_left hn
  have hy : y0∈cycles background .sphere ((q:ℤ)-t+(t-k)) (s,t) := by
    have hh := (cycles background .sphere ((q:ℤ)-k) (s,t)).sub_mem hx
      (boundaries_le_cycles background .sphere (s,t) (k+1) _ hb)
    have hy0 : y0∈cycles background .sphere ((q:ℤ)-k) (s,t) := by
      simpa only [sub_sub_cancel] using hh
    rwa [show (q:ℤ)-t+(t-k)=(q:ℤ)-k by omega]
  let y : cycles background .sphere ((q:ℤ)-t+(t-k)) (s,t) := ⟨y0,hy⟩
  apply (finite_sphere_frame q k hq hk s t y ?_ e).resolve_left hne
  intro z
  obtain ⟨c,rfl⟩ := Quotient.exists_rep z
  have hc : c.val∈cycles background .sphere ((q:ℤ)-k) (s,t) := by
    exact (congrArg (fun j : ℤ => c.val∈cycles background .sphere j (s,t))
      (show (q:ℤ)-t+(t-k)=(q:ℤ)-k by omega)).mp c.property
  rcases hframe c.val hc with hc|hc
  · left
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    rwa [show 1+t-(t-k)=(k:ℤ)+1 by omega]
  · right
    apply sub_eq_zero.mp
    change subquotientClass _ _ c - subquotientClass _ _ y=0
    rw [←map_sub]
    apply (subquotientClass_eq_zero_iff _ _ _).mpr
    change (show background.classical.sphere.Page 2 (s,t) from c.val)-y0 ∈ boundaries background .sphere (1+t-(t-k)) (s,t)
    rwa [show 1+t-(t-k)=(k:ℤ)+1 by omega]

private theorem strip_af7_torsion_representative :
    ∃ c : BiHom 125 132 (S_0_0 : SyntheticSpectrum),
      sphereFirstQuotient background 7 132 (quotientClass 1 c)=KIP126.Computation.Table.basis .sphere 7 132 0 ∧
      lambdaMultiply 2 c=0 ∧
      Detects (background.convergence (.quotient 9 .sphere)) (7,132,132)
        (quotientLabel 9 7 132 0 (KIP126.Computation.Table.basis .sphere 7 132 0)) (quotientClass 9 c) := by
  obtain ⟨c,hc,ht⟩ := sphere_boundary_submodule_torsion_lift 7 132 3 (by decide)
    (KIP126.Computation.Table.basis .sphere 7 132 0) strip_af7_label_boundary
  have hzero : lambdaMultiply 0 c=c := by
    have hu := graded_coherence.right_unit (125,132) (S_0_0 : SyntheticSpectrum)
    simp only [biShiftAddIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,Category.comp_id] at hu
    unfold lambdaMultiply lambdaPow
    simp only [eqToHom_refl,Category.id_comp]
    erw [←hu,Iso.inv_hom_id_app_assoc]
  have hd := background.sphereDetectionCompatible.homotopy_lambda 7 132 0 c
  dsimp only [KIP126.Literature.sphereFirstQuotient] at hc
  rw [hzero,hc] at hd
  have hq := detects_map .sphere (.quotient 9 .sphere)
    (XModLambdaN.incl (S_0_0 : SyntheticSpectrum) 9) (7,132,132) _ c hd
  exact ⟨c,hc,ht,hq⟩

private theorem finite_sphere_bottom_filtration (q : ℕ) (hq : 0<q) (s t : ℤ)
    (a : BiHom (t-s) t (XModLambdaN (S_0_0 : SyntheticSpectrum) q)) :
    FiltrationAtLeast background.syntheticTower s a := by
  let g := XModLambdaN.map background.nu.unitIso.inv q
  let f := XModLambdaN.map background.nu.unitIso.hom q
  have hg := finite_bottom_filtration .sphere q hq s t (a≫g)
  have h := map_preserves_filtration
    (background.convergentMap (.quotient q (.nu .sphere)) (.quotient q .sphere) f)
    (t-s,t) s (a≫g) hg
  have hgf : g≫f=𝟙 _ := by
    dsimp only [f,g]
    rw [←background.quotients.functoriality.map_comp,Iso.inv_hom_id,background.quotients.functoriality.map_id]
  change FiltrationAtLeast background.syntheticTower s ((a≫g)≫f) at h
  have he : (a≫g)≫f=a := by
    rw [Category.assoc,hgf]
    exact Category.comp_id a
  exact he ▸ h

theorem main_two_layer_strip
    (c9 : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9))
    (hc9 : Detects (background.convergence (.quotient 9 .sphere)) (9,134,132)
      (quotientLabel 9 9 134 2 (KIP126.Computation.Table.basis .sphere 9 134 2)) c9)
    {A : Type} [AddCommGroup A]
    (Phi : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9) →+ A)
    (hPhi7 : ∀c : BiHom 125 132 (S_0_0 : SyntheticSpectrum), lambdaMultiply 2 c=0 → Phi (quotientClass 9 c)=0)
    (hPhi9 : Phi c9=0)
    (a : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9)) :
    ∃ b : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiltrationAtLeast background.syntheticTower 11 b ∧ Phi b=Phi a := by
  classical
  have ha7 := finite_sphere_bottom_filtration 9 (by decide) 7 132 a
  obtain ⟨c7,hc7,ht7,hd7⟩ := strip_af7_torsion_representative
  have frame7 : ∀x : background.classical.sphere.Page 2 (7,132),
      x∈cycles background .sphere ((9:ℤ)-0) (7,132) →
      x∈boundaries background .sphere (0+1) (7,132) ∨
      x-(show background.classical.sphere.Page 2 (7,132) from KIP126.Computation.Table.basis .sphere 7 132 0)
        ∈boundaries background .sphere (0+1) (7,132) := by
    intro x hx
    rcases strip_af7_all_labels x with h|h
    · left; rw [h]; exact Submodule.zero_mem _
    · right; rw [h,sub_self]; exact Submodule.zero_mem _
  obtain ⟨b7,hb7⟩ := finite_detection_peel 9 (7,132,132)
    (quotientLabel 9 7 132 0 (KIP126.Computation.Table.basis .sphere 7 132 0))
    (finite_sphere_frame_of_cosets 9 0 (by decide) (by decide) 7 132 _ frame7)
    (quotientClass 9 c7) hd7 a ha7
  let a9 := a-(if b7 then quotientClass 9 c7 else 0)
  have ha9 : FiltrationAtLeast background.syntheticTower 9 a9 :=
    (strip_low_even_gap 8 (Or.inl rfl) a9).mp hb7
  obtain ⟨b9,hb9⟩ := finite_detection_peel 9 (9,134,132)
    (quotientLabel 9 9 134 2 (KIP126.Computation.Table.basis .sphere 9 134 2))
    (finite_sphere_frame_of_cosets 9 2 (by decide) (by decide) 9 134 _ strip_h6b_cosets)
    c9 hc9 a9 ha9
  refine ⟨a9-(if b9 then c9 else 0),(strip_low_even_gap 10 (Or.inr rfl) _).mp hb9,?_⟩
  have hz7 := hPhi7 c7 ht7
  dsimp only [a9]
  cases b7 <;> cases b9 <;> simp only [Bool.false_eq_true,↓reduceIte,map_sub,hz7,hPhi9,sub_zero]

end
end KIP126.Main.SectionSeven.Internal
