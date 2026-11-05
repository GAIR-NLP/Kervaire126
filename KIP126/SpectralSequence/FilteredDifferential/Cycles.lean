module

import all KIP126.SpectralSequence.FilteredDifferential.Helpers
import all KIP126.SpectralSequence.FilteredPage.Proofs

import all KIP126.SpectralSequence.FilteredDifferential.Data

@[expose] section

/-! The next cycle subobject gives the kernel of the finite-page differential. -/

namespace KIP126.Core.SpectralSequence.FilteredComplex

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

open DifferentialHelpers
set_option backward.isDefEq.respectTransparency false in
/-- The ≥ direction of Z_succ: image(ofLE(Z_{n+1}, Z_n) ≫ pageπ n) ≤ kernel(pageDifferential).
    Elements of Z_{n+1} (deeper cycle condition: dx ∈ F^{s+n+1}) map to zero under pageDiff
    because their d-image lands in F^{s+n+1}, hence projects to 0 in gr^{s+n}. -/
theorem pageDifferential_Z_succ_ge (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    imageSubobject (
      Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1)) (FC.cycleSubobject s k ↑n)
        (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
      FC.pageπ s k ↑n) ≤
    kernelSubobject (FC.pageDifferential s k n) := by
  apply le_kernelSubobject
  set ofLE_pageπ := Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
    (FC.cycleSubobject s k ↑n)
    (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
    FC.pageπ s k ↑n with h_ofLE_pageπ
  rw [← cancel_epi (factorThruImageSubobject ofLE_pageπ), comp_zero,
    ← Category.assoc, imageSubobject_arrow_comp]
  rw [h_ofLE_pageπ, Category.assoc]
  erw [cokernel.π_desc]
  set f_n := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow)
  set kerZ := kernelSubobject f_n
  set ι_s := Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.mono s k)
  set πV := FC.filtration.toAssociatedGraded s k
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV)
  haveI : Epi p := inferInstance
  set f_n1 := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow)
  set kerZ1 := kernelSubobject f_n1
  set p1 := factorThruImageSubobject (kerZ1.arrow ≫ πV)
  haveI : Epi p1 := inferInstance
  rw [← cancel_epi p1, comp_zero]
  have hkerZ1_le : kerZ1 ≤ kerZ := by
    apply le_kernelSubobject
    have hfil : FC.filtration.F (s + ↑(n + 1)) (k - 1) ≤ FC.filtration.F (s + ↑n) (k - 1) :=
      FC.filtration.le_of_le (by omega) (k - 1)
    have h1 : kerZ1.arrow ≫ f_n1 = 0 := kernelSubobject_arrow_comp f_n1
    have h1' : (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      simp only [Category.assoc] at h1 ⊢; exact h1
    set dk_im := kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)
    set lift1 := Abelian.monoLift (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow dk_im h1'
    calc kerZ1.arrow ≫ f_n
        = dk_im ≫ cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          simp only [f_n, dk_im, Category.assoc]
      _ = (lift1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [Abelian.monoLift_comp]
      _ = lift1 ≫ (Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [show (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow =
            Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow
            from (Subobject.ofLE_arrow hfil).symm]; simp only [Category.assoc]
      _ = 0 := by
          simp only [Category.assoc, cokernel.condition, comp_zero]
  set β := Subobject.ofLE kerZ1 kerZ hkerZ1_le
  have h_factor : p1 ≫ Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
      (FC.cycleSubobject s k ↑n)
      (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) = β ≫ p := by
    apply (inferInstance : Mono (FC.cycleSubobject s k ↑n).arrow).right_cancellation
    simp only [Category.assoc]
    simp only [p1, p, β]
    rw [Subobject.ofLE_arrow]
    erw [imageSubobject_arrow_comp, imageSubobject_arrow_comp]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  rw [show p1 ≫ _ = (p1 ≫ _) ≫ _ from (Category.assoc _ _ _).symm]
  rw [h_factor]
  rw [Category.assoc]
  rw [Abelian.comp_epiDesc]
  set ι_t := Subobject.ofLE (FC.filtration.F (s + ↑n + 1) (k - 1)) (FC.filtration.F (s + ↑n) (k - 1))
    (FC.filtration.mono (s + ↑n) (k - 1))
  set πV' := FC.filtration.toAssociatedGraded (s + ↑n) (k - 1)
  suffices h : β ≫ _ = (0 : _ ⟶ Subobject.underlying.obj
    (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)) by
    rw [show β ≫ (_ ≫ _) = (β ≫ _) ≫ _ from (Category.assoc β _ _).symm]
    rw [h, zero_comp]
  apply (inferInstance : Mono (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow).right_cancellation
  rw [zero_comp]
  simp only [Category.assoc]
  unfold FilteredComplex.cycleSubobject
  push_cast
  simp only [imageSubobject_arrow_comp]
  simp only [factorThruKernelSubobject]
  set f' := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf'_def
  set ml := Abelian.monoLift (FC.filtration.F (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1))
    (by simp only [Category.assoc]; exact kernelSubobject_arrow_comp f_n) with hml_def
  suffices h_main : β ≫ ml ≫ πV' = 0 by
    convert h_main using 2; try rfl
    rw [show (_ : Subobject.underlying.obj _ ⟶ _) ≫ _ ≫ πV' = (_ ≫ _) ≫ πV'
      from (Category.assoc _ _ _).symm, Subobject.factorThru_arrow]
  have h_kerZ1_factor : (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
      cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc]
    exact kernelSubobject_arrow_comp f_n1
  set lift_n1 := Abelian.monoLift (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow
    (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) h_kerZ1_factor
  have h_lift_n1_spec : lift_n1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow =
      kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) :=
    Abelian.monoLift_comp _ _ _
  have hfil_le_nat : FC.filtration.F (s + ↑(n + 1)) (k - 1) ≤ FC.filtration.F (s + ↑n) (k - 1) :=
    FC.filtration.le_of_le (by omega) (k - 1)
  have h_β_ml_eq : β ≫ ml = lift_n1 ≫ Subobject.ofLE _ _ hfil_le_nat := by
    apply (inferInstance : Mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).right_cancellation
    have h_ml_arrow : ml ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
        kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
      simp only [hml_def]; exact Abelian.monoLift_comp _ _ _
    calc (β ≫ ml) ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow
        = β ≫ (ml ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) := Category.assoc _ _ _
      _ = β ≫ (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) := by rw [h_ml_arrow]
      _ = (β ≫ kerZ.arrow) ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
          simp only [Category.assoc]
      _ = kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := by
          rw [Subobject.ofLE_arrow hkerZ1_le]
      _ = lift_n1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow := h_lift_n1_spec.symm
      _ = lift_n1 ≫ (Subobject.ofLE _ _ hfil_le_nat ≫
            (FC.filtration.F (s + ↑n) (k - 1)).arrow) := by rw [Subobject.ofLE_arrow]
      _ = (lift_n1 ≫ Subobject.ofLE _ _ hfil_le_nat) ≫
            (FC.filtration.F (s + ↑n) (k - 1)).arrow := (Category.assoc _ _ _).symm
  rw [show β ≫ ml ≫ πV' = (β ≫ ml) ≫ πV' from (Category.assoc _ _ _).symm,
    h_β_ml_eq, Category.assoc]
  suffices h_zero : Subobject.ofLE _ _ hfil_le_nat ≫ πV' = 0 by
    rw [h_zero, comp_zero]
  have h_idx_eq : (s : ℤ) + ↑(n + 1) = s + ↑n + 1 := by omega
  have h_fil_eq : FC.filtration.F (s + ↑(n + 1)) (k - 1) =
      FC.filtration.F (s + ↑n + 1) (k - 1) := by
    rw [h_idx_eq]
  have h_factor : Subobject.ofLE _ _ hfil_le_nat =
      (Subobject.isoOfEq (FC.filtration.F (s + ↑(n + 1)) (k - 1))
        (FC.filtration.F (s + ↑n + 1) (k - 1)) h_fil_eq).hom ≫ ι_t := by
    apply (cancel_mono (FC.filtration.F (s + ↑n) (k - 1)).arrow).mp
    simp only [Category.assoc, Subobject.isoOfEq_hom, ι_t,
      Subobject.ofLE_arrow]
  rw [h_factor, Category.assoc]
  dsimp [πV']
  unfold KIP126.Core.SpectralSequence.Filtration.toAssociatedGraded
    KIP126.Core.SpectralSequence.Filtration.associatedGraded
  rw [cokernel.condition, comp_zero]



set_option maxHeartbeats 900000 in
/-- Every class in the kernel of the finite-page differential has a representative
in the next cycle subobject.  -/
theorem pageDifferential_Z_succ_le (FC : FilteredComplex C)
    (s k : ℤ) (n : ℕ) :
    kernelSubobject (FC.pageDifferential s k n) ≤
    imageSubobject (
      Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1)) (FC.cycleSubobject s k ↑n)
        (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
      FC.pageπ s k ↑n) := by
  set ι_s := Subobject.ofLE (FC.filtration.F (s + 1) k) (FC.filtration.F s k) (FC.filtration.mono s k) with hι_s_def
  set πV := FC.filtration.toAssociatedGraded s k with hπV_def
  set f_n := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) with hf_n_def
  set kerZ := kernelSubobject f_n with hkerZ_def
  set ι_t := Subobject.ofLE (FC.filtration.F (s + ↑n + 1) (k - 1)) (FC.filtration.F (s + ↑n) (k - 1))
    (FC.filtration.mono (s + ↑n) (k - 1)) with hι_t_def
  set πV' := FC.filtration.toAssociatedGraded (s + ↑n) (k - 1) with hπV'_def
  set f_n' := (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫ FC.complex.d (k - 1) (k - 1 - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf_n'_def
  set kerZ' := kernelSubobject f_n' with hkerZ'_def
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV) with hp_def
  haveI hp_epi : Epi p := inferInstance
  have h_ker_fn : kerZ.arrow ≫ f_n = 0 := kernelSubobject_arrow_comp f_n
  have h_factor_zero : (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
      cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc] at h_ker_fn ⊢; exact h_ker_fn
  set lift_n := Abelian.monoLift (FC.filtration.F (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) h_factor_zero with hlift_n_def
  have h_lift_spec : lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
      kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) := Abelian.monoLift_comp _ _ _
  have h_lift_in_kerZ' : lift_n ≫ f_n' = 0 := by
    calc lift_n ≫ f_n'
        = ((lift_n ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫ FC.complex.d (k - 1) (k - 1 - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [hf_n'_def, Category.assoc]
      _ = ((kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫ FC.complex.d (k - 1) (k - 1 - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by rw [h_lift_spec]
      _ = 0 := by
          rw [show (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫ FC.complex.d (k - 1) (k - 1 - 1) =
            kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ (FC.complex.d k (k - 1) ≫ FC.complex.d (k - 1) (k - 1 - 1)) from by
            simp only [Category.assoc], FC.complex.d_comp_d k]; simp only [comp_zero, zero_comp]
  set lift_to_kerZ' := factorThruKernelSubobject f_n' lift_n h_lift_in_kerZ'
    with hlift_to_kerZ'_def
  have h_ltk_spec : lift_to_kerZ' ≫ kerZ'.arrow = lift_n :=
    factorThruKernelSubobject_comp_arrow f_n' lift_n h_lift_in_kerZ'
  set to_Z_n_t := lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')
    with hto_Z_n_t_def
  set pageπ_t := FC.pageπ (s + ↑n) (k - 1) ↑n with hpageπ_t_def
  set ψ := to_Z_n_t ≫ pageπ_t with hψ_def
  have h_ker_le : kernelSubobject (FC.pageDifferential s k n) ≤
      imageSubobject ((kernelSubobject ψ).arrow ≫ p ≫ FC.pageπ s k ↑n) := by
    erw [kernelSubobject_cokernel_desc']
    erw [kernelSubobject_epiDesc']
    erw [← imageSubobject_epi_comp'_local
      (factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p))
      ((imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow ≫
        FC.pageπ s k ↑n)]
    erw [show factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p) ≫
      (imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow ≫
      FC.pageπ s k ↑n =
      (factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p) ≫
      (imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow) ≫
      FC.pageπ s k ↑n from (Category.assoc _ _ _).symm,
      imageSubobject_arrow_comp ((kernelSubobject ψ).arrow ≫ p),
      Category.assoc]
  apply le_trans h_ker_le
  set f_n1 := (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
    cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) with hf_n1_def
  set kerZ1 := kernelSubobject f_n1 with hkerZ1_def
  have hkerZ1_le : kerZ1 ≤ kerZ := by
    apply le_kernelSubobject
    have hfil : FC.filtration.F (s + ↑(n + 1)) (k - 1) ≤ FC.filtration.F (s + ↑n) (k - 1) :=
      FC.filtration.le_of_le (by omega) (k - 1)
    have h1' : (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      simp only [Category.assoc]; exact kernelSubobject_arrow_comp f_n1
    set lift1 := Abelian.monoLift (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow
      (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) h1'
    calc kerZ1.arrow ≫ f_n
        = (kerZ1.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          simp only [f_n, Category.assoc]
      _ = (lift1 ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [Abelian.monoLift_comp]
      _ = lift1 ≫ (Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
            cokernel.π ((FC.filtration.F (s + ↑n) (k - 1)).arrow) := by
          rw [show (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow =
            Subobject.ofLE _ _ hfil ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow
            from (Subobject.ofLE_arrow hfil).symm]; simp only [Category.assoc]
      _ = 0 := by simp only [Category.assoc, cokernel.condition, comp_zero]
  set β := Subobject.ofLE kerZ1 kerZ hkerZ1_le with hβ_def
  set p1 := factorThruImageSubobject (kerZ1.arrow ≫ πV) with hp1_def
  haveI hp1_epi : Epi p1 := inferInstance
  have h_Zn_eq : FC.cycleSubobject s k ↑n = imageSubobject (kerZ.arrow ≫ πV) := by
    subst kerZ
    subst f_n
    subst πV
    rfl
  have h_Zn1_eq : FC.cycleSubobject s k ↑(n + 1) =
      imageSubobject (kerZ1.arrow ≫ πV) := by
    subst kerZ1
    subst f_n1
    subst πV
    rfl
  have h_factor : p1 ≫ Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
      (FC.cycleSubobject s k ↑n)
      (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) = β ≫ p := by
    change p1 ≫ Subobject.ofLE
      (imageSubobject (kerZ1.arrow ≫ πV))
      (imageSubobject (kerZ.arrow ≫ πV)) _ = β ≫ p
    apply (inferInstance : Mono (imageSubobject (kerZ.arrow ≫ πV)).arrow).right_cancellation
    simp only [Category.assoc, p1, p, β]
    rw [Subobject.ofLE_arrow]
    erw [imageSubobject_arrow_comp, imageSubobject_arrow_comp]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  have h_p_Z : p ≫ (FC.cycleSubobject s k ↑n).arrow = kerZ.arrow ≫ πV := by
    change p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow = kerZ.arrow ≫ πV
    exact imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
  have h_to_Z_kills : ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ pageπ_t = 0 := by
    simp only [Category.assoc]; rw [← hψ_def]; exact kernelSubobject_arrow_comp ψ
  set B_n_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑n with hB_n_t_def
  have hB_le_Z := FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n
  have h_to_Z_comp : to_Z_n_t ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow = lift_n ≫ πV' := by
    change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
      (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
    simp only [Category.assoc, imageSubobject_arrow_comp]
    rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
      (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm, h_ltk_spec]
  have h_lift_πV'_eq : (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
      ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow := by
    rw [Category.assoc, h_to_Z_comp]
  have h_bnd_factors : B_n_t.Factors ((kernelSubobject ψ).arrow ≫ lift_n ≫ πV') := by
    rw [h_lift_πV'_eq]
    set γ₁ := factorThruKernelSubobject pageπ_t
      ((kernelSubobject ψ).arrow ≫ to_Z_n_t) h_to_Z_kills
    have hγ₁_spec : γ₁ ≫ (kernelSubobject pageπ_t).arrow =
        (kernelSubobject ψ).arrow ≫ to_Z_n_t :=
      factorThruKernelSubobject_comp_arrow _ _ _
    have h_exact : (ShortComplex.mk (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) pageπ_t
        (by simp only [hpageπ_t_def]; exact cokernel.condition _)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _
        (by simp only [hpageπ_t_def]; exact cokernelIsCokernel _)
    rw [ShortComplex.exact_iff_image_eq_kernel] at h_exact
    change imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) = kernelSubobject pageπ_t at h_exact
    haveI : Mono (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) := inferInstance
    haveI h_fti_epi : Epi (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) :=
      inferInstance
    haveI h_fti_mono : Mono (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) :=
      mono_of_mono_fac (imageSubobject_arrow_comp _)
    haveI : IsIso (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) :=
      isIso_of_mono_of_epi _
    have h_ker_Z_fac : B_n_t.Factors ((kernelSubobject pageπ_t).arrow ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow) := by
      rw [show (kernelSubobject pageπ_t).arrow =
        eqToHom (congr_arg Subobject.underlying.obj h_exact.symm) ≫
        (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow from
        (Subobject.arrow_congr _ _ h_exact.symm).symm, Category.assoc]
      apply Subobject.factors_of_factors_right
      have h_arrow_eq : (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow ≫
          (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow =
        inv (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)) ≫
          B_n_t.arrow := by
        rw [← cancel_epi (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z))]
        rw [show factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) ≫
          (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow =
          (factorThruImageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z) ≫
          (imageSubobject (Subobject.ofLE B_n_t (FC.cycleSubobject (s + ↑n) (k - 1) ↑n) hB_le_Z)).arrow) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow
          from (Category.assoc _ _ _).symm,
          imageSubobject_arrow_comp, Subobject.ofLE_arrow,
          IsIso.hom_inv_id_assoc]
      rw [h_arrow_eq]
      exact Subobject.factors_comp_arrow _
    rw [show ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow =
      (γ₁ ≫ (kernelSubobject pageπ_t).arrow) ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow from by
        exact congrArg (fun t => t ≫ (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow)
          hγ₁_spec.symm,
      Category.assoc]
    exact Subobject.factors_of_factors_right _ h_ker_Z_fac
  set α := B_n_t.factorThru _ h_bnd_factors with hα_def
  have hα_spec : α ≫ B_n_t.arrow = (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' :=
    Subobject.factorThru_arrow _ _ _
  set imgD_bnd := imageSubobject ((FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
    FC.dToK (k - 1)) with himgD_bnd_def
  set I_bnd := imgD_bnd ⊓ FC.filtration.F (s + ↑n) (k - 1) with hI_bnd_def
  set oI_bnd := Subobject.ofLE I_bnd (FC.filtration.F (s + ↑n) (k - 1)) inf_le_right
    with hoI_bnd_def
  set factorB := factorThruImageSubobject (oI_bnd ≫ πV') with hfactorB_def
  haveI hfactorB_epi : Epi factorB := inferInstance
  have hfactorB_spec : factorB ≫ B_n_t.arrow = oI_bnd ≫ πV' := by
    change factorThruImageSubobject (oI_bnd ≫ πV') ≫
      (imageSubobject (oI_bnd ≫ πV')).arrow = oI_bnd ≫ πV'
    exact imageSubobject_arrow_comp (oI_bnd ≫ πV')
  set pb1_fst := Limits.pullback.fst factorB α
  set pb1_snd := Limits.pullback.snd factorB α
  have hpb1_cond : pb1_fst ≫ factorB = pb1_snd ≫ α := Limits.pullback.condition
  haveI : Epi pb1_snd := Abelian.epi_pullback_of_epi_f factorB α
  have h_pb1_eq_πV' : pb1_snd ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
      pb1_fst ≫ oI_bnd ≫ πV' := by
    calc pb1_snd ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV'
        = pb1_snd ≫ (α ≫ B_n_t.arrow) := by rw [hα_spec]
      _ = (pb1_snd ≫ α) ≫ B_n_t.arrow := (Category.assoc _ _ _).symm
      _ = (pb1_fst ≫ factorB) ≫ B_n_t.arrow := by
        exact congrArg (fun t => t ≫ B_n_t.arrow) hpb1_cond.symm
      _ = pb1_fst ≫ (factorB ≫ B_n_t.arrow) := Category.assoc _ _ _
      _ = pb1_fst ≫ oI_bnd ≫ πV' := by simp only [hfactorB_spec]
  set imgD_src := (FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)
    with himgD_src_def
  set factorD := factorThruImageSubobject imgD_src with hfactorD_def
  haveI hfactorD_epi : Epi factorD := inferInstance
  have hfactorD_spec : factorD ≫ imgD_bnd.arrow = imgD_src :=
    imageSubobject_arrow_comp imgD_src
  set oI_to_imgD := Subobject.ofLE I_bnd imgD_bnd inf_le_left with hoI_to_imgD_def
  set pb2_fst := Limits.pullback.fst factorD (pb1_fst ≫ oI_to_imgD)
  set pb2_snd := Limits.pullback.snd factorD (pb1_fst ≫ oI_to_imgD)
  have hpb2_cond : pb2_fst ≫ factorD = pb2_snd ≫ (pb1_fst ≫ oI_to_imgD) :=
    Limits.pullback.condition
  haveI : Epi pb2_snd := Abelian.epi_pullback_of_epi_f factorD _
  set e := pb2_snd ≫ pb1_snd with he_def
  haveI : Epi e := epi_comp _ _
  set eqH := eqToHom (show Subobject.underlying.obj (FC.filtration.F (s + ↑n - ↑n + 1) ((k - 1) + 1)) =
    Subobject.underlying.obj (FC.filtration.F (s + 1) k) from by
    rw [show (s : ℤ) + ↑n - ↑n + 1 = s + 1 from by omega,
        show (k : ℤ) - 1 + 1 = k from by omega]) with heqH_def
  set σ := pb2_fst ≫ eqH ≫ ι_s with hσ_def
  have hσ_πV : σ ≫ πV = 0 := by
    simp only [hσ_def, Category.assoc, show ι_s ≫ πV = 0 from cokernel.condition ι_s,
      comp_zero]
  set w := e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow - σ with hw_def
  have hw_kills : w ≫ f_n1 = 0 := by
    rw [hw_def, Preadditive.sub_comp, sub_eq_zero]
    have h_sn1_eq : (s : ℤ) + ↑n + 1 = s + ↑(n + 1) := by push_cast; omega
    have h_e_lift_πV' : e ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
        pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ πV' := by
      simp only [he_def, Category.assoc, h_pb1_eq_πV']
    have h_diff_kills : (e ≫ (kernelSubobject ψ).arrow ≫ lift_n -
        pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ πV' = 0 := by
      rw [Preadditive.sub_comp]; simp only [Category.assoc]
      rw [h_e_lift_πV', sub_self]
    set γ_diff := Abelian.monoLift ι_t
        (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd)
        (show _ ≫ cokernel.π ι_t = 0 from h_diff_kills) with hγ_diff_def
    have hγ_spec : γ_diff ≫ ι_t =
        e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd :=
      Abelian.monoLift_comp ι_t
        (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd)
        (show _ ≫ cokernel.π ι_t = 0 from h_diff_kills)
    have h_decomp : e ≫ (kernelSubobject ψ).arrow ≫ lift_n =
        pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t := by
      have key : e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd =
          γ_diff ≫ ι_t := hγ_spec.symm
      calc e ≫ (kernelSubobject ψ).arrow ≫ lift_n
          = (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd) +
            pb2_snd ≫ pb1_fst ≫ oI_bnd := (sub_add_cancel _ _).symm
        _ = γ_diff ≫ ι_t + pb2_snd ≫ pb1_fst ≫ oI_bnd := by rw [key]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t := add_comm _ _
    have h_ι_t_kills : ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      have h1 : ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow =
          (FC.filtration.F (s + ↑n + 1) (k - 1)).arrow :=
        Subobject.ofLE_arrow (FC.filtration.mono (s + ↑n) (k - 1))
      have h2 : (FC.filtration.F (s + ↑n + 1) (k - 1)).arrow =
          eqToHom (congr_arg (fun i => Subobject.underlying.obj (FC.filtration.F i (k - 1)))
            h_sn1_eq) ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow := by
        simp [h_sn1_eq]
      calc ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow)
          = (ι_t ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
            rw [Category.assoc]
        _ = (eqToHom _ ≫ (FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
            rw [h1, h2]
        _ = eqToHom _ ≫ ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow)) := by
            rw [Category.assoc]
        _ = eqToHom _ ≫ 0 := by
            rw [cokernel.condition]
        _ = 0 := by rw [comp_zero]
    have h_oI_arrow : oI_bnd ≫ (FC.filtration.F (s + ↑n) (k - 1)).arrow = I_bnd.arrow :=
      Subobject.ofLE_arrow inf_le_right
    have h_σ_arrow : σ ≫ (FC.filtration.F s k).arrow =
        pb2_fst ≫ eqH ≫ (FC.filtration.F (s + 1) k).arrow := by
      simp only [hσ_def, Category.assoc]
      congr 2; exact Subobject.ofLE_arrow (FC.filtration.mono s k)
    have h_eqH_d : eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) = imgD_src := by
      conv_lhs => rw [← eqToHom_arrow_dToK_local FC (s + 1) k]
      rw [heqH_def]; simp only [← Category.assoc]; rw [eqToHom_trans]
      rw [himgD_src_def]
      congr 1
      exact Subobject.arrow_congr _ _ (by congr 1; omega)
    have h_pb2_imgD : pb2_fst ≫ imgD_src = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow := by
      calc pb2_fst ≫ imgD_src
          = pb2_fst ≫ (factorD ≫ imgD_bnd.arrow) := by
            rw [imageSubobject_arrow_comp imgD_src]
        _ = (pb2_fst ≫ factorD) ≫ imgD_bnd.arrow := by rw [Category.assoc]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_to_imgD) ≫ imgD_bnd.arrow := by rw [hpb2_cond]
        _ = pb2_snd ≫ pb1_fst ≫ (oI_to_imgD ≫ imgD_bnd.arrow) := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow := by
            congr 1; congr 1; exact Subobject.ofLE_arrow inf_le_left
    have h_lhs : (e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow) ≫ f_n1 =
        pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
      rw [hf_n1_def]; simp only [Category.assoc]
      conv_lhs =>
        rw [show (kernelSubobject ψ).arrow ≫ kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            (kernelSubobject ψ).arrow ≫ (kerZ.arrow ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [← h_lift_spec]
      simp only [Category.assoc]
      set F_sn := (FC.filtration.F (s + ↑n) (k - 1)).arrow with hF_sn_def
      set cok := cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) with hcok_def
      calc e ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ F_sn ≫ cok
          = (e ≫ (kernelSubobject ψ).arrow ≫ lift_n) ≫ F_sn ≫ cok := by
            simp only [Category.assoc]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t) ≫ F_sn ≫ cok := by
            rw [h_decomp]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ F_sn ≫ cok +
            (γ_diff ≫ ι_t) ≫ F_sn ≫ cok := by
            rw [Preadditive.add_comp]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok +
            γ_diff ≫ ι_t ≫ F_sn ≫ cok := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok + γ_diff ≫ 0 := by
            rw [h_ι_t_kills]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok + 0 := by
            rw [comp_zero]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok := by
            rw [add_zero]
        _ = pb2_snd ≫ pb1_fst ≫ (oI_bnd ≫ F_sn) ≫ cok := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫ cok := by
            rw [h_oI_arrow]
    have h_rhs : σ ≫ f_n1 =
        pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫
        cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) := by
      rw [hf_n1_def]
      conv_lhs =>
        rw [show σ ≫ (FC.filtration.F s k).arrow ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            (σ ≫ (FC.filtration.F s k).arrow) ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [h_σ_arrow]
      simp only [Category.assoc]
      conv_lhs =>
        rw [show pb2_fst ≫ eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            (pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1))) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [show pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1)) =
            (pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1))) from rfl]
      conv_lhs =>
        rw [show (pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1))) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) =
            pb2_fst ≫ (eqH ≫ (FC.filtration.F (s + 1) k).arrow ≫ FC.complex.d k (k - 1)) ≫
              cokernel.π ((FC.filtration.F (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
      rw [h_eqH_d]
      simp only [← Category.assoc]; rw [h_pb2_imgD]; simp only [Category.assoc]
    rw [h_lhs, h_rhs]
  set w_fac := factorThruKernelSubobject f_n1 w hw_kills with hw_fac_def
  have hw_fac_spec : w_fac ≫ kerZ1.arrow = w :=
    factorThruKernelSubobject_comp_arrow _ _ _
  have h_key_eq : w_fac ≫ β ≫ p = e ≫ (kernelSubobject ψ).arrow ≫ p := by
    apply (inferInstance : Mono (FC.cycleSubobject s k ↑n).arrow).right_cancellation
    calc
      (w_fac ≫ β ≫ p) ≫ (FC.cycleSubobject s k ↑n).arrow =
          w_fac ≫ β ≫ (p ≫ (FC.cycleSubobject s k ↑n).arrow) := by
            simp only [Category.assoc]
      _ = w_fac ≫ β ≫ (kerZ.arrow ≫ πV) := by rw [h_p_Z]
      _ = (w_fac ≫ (β ≫ kerZ.arrow)) ≫ πV := by
            simp only [Category.assoc]
      _ = (w_fac ≫ kerZ1.arrow) ≫ πV := by
            rw [Subobject.ofLE_arrow hkerZ1_le]
      _ = w ≫ πV := by rw [hw_fac_spec]
      _ = (e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow - σ) ≫ πV := by
            rw [hw_def]
      _ = (e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow) ≫ πV := by
            rw [Preadditive.sub_comp, hσ_πV, sub_zero]
      _ = e ≫ (kernelSubobject ψ).arrow ≫ (kerZ.arrow ≫ πV) := by
            simp only [Category.assoc]
      _ = e ≫ (kernelSubobject ψ).arrow ≫ (p ≫
          (FC.cycleSubobject s k ↑n).arrow) := by rw [h_p_Z]
      _ = (e ≫ (kernelSubobject ψ).arrow ≫ p) ≫
          (FC.cycleSubobject s k ↑n).arrow := by
            simp only [Category.assoc]
  rw [(imageSubobject_epi_comp'_local e
    ((kernelSubobject ψ).arrow ≫ p ≫ FC.pageπ s k ↑n)).symm]
  have h_rewrite : e ≫ (kernelSubobject ψ).arrow ≫ p ≫ FC.pageπ s k ↑n =
      (w_fac ≫ p1) ≫ (Subobject.ofLE (FC.cycleSubobject s k ↑(n + 1))
        (FC.cycleSubobject s k ↑n)
        (FC.cycleSubobject_antitone s k (by exact_mod_cast Nat.le_succ n)) ≫
        FC.pageπ s k ↑n) := by
    simp only [FilteredComplex.cycleSubobject]
    have h_img_le : imageSubobject (kerZ1.arrow ≫ πV) ≤
        imageSubobject (kerZ.arrow ≫ πV) := by
      rw [show kerZ1.arrow ≫ πV = (β ≫ kerZ.arrow) ≫ πV by
        rw [Subobject.ofLE_arrow hkerZ1_le]]
      simpa only [Category.assoc] using imageSubobject_comp_le β (kerZ.arrow ≫ πV)
    change e ≫ (kernelSubobject ψ).arrow ≫ (p ≫ FC.pageπ s k ↑n) =
      (w_fac ≫ p1) ≫
        (Subobject.ofLE (imageSubobject (kerZ1.arrow ≫ πV))
          (imageSubobject (kerZ.arrow ≫ πV)) h_img_le ≫ FC.pageπ s k ↑n)
    have h_factor_image : p1 ≫ Subobject.ofLE
        (imageSubobject (kerZ1.arrow ≫ πV))
        (imageSubobject (kerZ.arrow ≫ πV)) h_img_le = β ≫ p := by
      change p1 ≫ Subobject.ofLE
        (imageSubobject (kerZ1.arrow ≫ πV))
        (imageSubobject (kerZ.arrow ≫ πV)) h_img_le = β ≫ p at h_factor
      exact h_factor
    have h_prefix : e ≫ (kernelSubobject ψ).arrow ≫ p =
        w_fac ≫ p1 ≫ Subobject.ofLE
          (imageSubobject (kerZ1.arrow ≫ πV))
          (imageSubobject (kerZ.arrow ≫ πV)) h_img_le := by
      rw [← h_key_eq]
      congr 1
      exact h_factor_image.symm
    rw [← Category.assoc e (kernelSubobject ψ).arrow
      (p ≫ FC.pageπ s k ↑n)]
    rw [← Category.assoc (e ≫ (kernelSubobject ψ).arrow) p
      (FC.pageπ s k ↑n)]
    have h_prefix_left :
        ((e ≫ (kernelSubobject ψ).arrow) ≫ p) =
          w_fac ≫ p1 ≫ Subobject.ofLE
            (imageSubobject (kerZ1.arrow ≫ πV))
            (imageSubobject (kerZ.arrow ≫ πV)) h_img_le := by
      rw [show ((e ≫ (kernelSubobject ψ).arrow) ≫ p) =
        e ≫ (kernelSubobject ψ).arrow ≫ p from by simp only [Category.assoc],
        h_prefix]
    rw [h_prefix_left]
    simp only [Category.assoc]
  rw [h_rewrite]
  exact imageSubobject_comp_le _ _

end KIP126.Core.SpectralSequence.FilteredComplex
