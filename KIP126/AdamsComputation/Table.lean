module

public import KIP126.AdamsComputation.Standard
public import KIP126.AdamsComputation.Table.Data
public import KIP126.AdamsComputation.Table.Dimensions
public import KIP126.AdamsComputation.Internal.NuCofiberArchive.Realization
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Realization
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Coordinates
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Basis
import all KIP126.AdamsComputation.Internal.NuCofiberArchive.Range

/-! Finite equations on the specified actual objects. The bounded rows and
coordinate data use the fixed sphere algebra and its actual-page comparison. -/
@[expose] section
namespace KIP126.Computation.NuCofiberArchive
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

private theorem inScope_of_mem (d : Table.Raw.Degree) (hd : d ∈ Table.Raw.degrees)
    (hs : d.spectrum = .nuCofiber) : InScope d.s d.t := by
  have hbound : ∀ d ∈ Table.Raw.degrees, d.spectrum = .nuCofiber → d.t ≤ 200 := by
    decide
  exact hbound d hd hs

private theorem selected_count (d : Table.Raw.Degree) (hd : d ∈ Table.Raw.degrees)
    (hs : d.spectrum = .nuCofiber) : basisCount d.s d.t = d.monomials.length := by
  have all : ∀ d ∈ Table.Raw.degrees, d.spectrum = .nuCofiber →
      basisCount d.s d.t = d.monomials.length := by decide
  exact all d hd hs

end KIP126.Computation.NuCofiberArchive

namespace KIP126.Computation.Table
open CategoryTheory KIP126.StableHomotopy KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Completed
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

public def object : Raw.Spectrum → Spectrum
  | .sphere => SphereSpectrum
  | .nuCofiber => HasFunctorialCofiber.cofib background.auxiliary.nuMap

public abbrev sequence (o : Raw.Spectrum) := background.classical.obj (object o)
public abbrev Page (o : Raw.Spectrum) (s t : ℕ) := (sequence o).Page 2 (s,t)

public def sphereBasis (s t i : ℕ) : background.classical.sphere.Page 2 (s,t) :=
  if ht : t ≤ 261 then
    if hi : i < Standard.archive.basisCount s t then
      (Standard.coordinates s t ht).symm (Finsupp.single ⟨i,hi⟩ 1)
    else 0
  else 0

private theorem sphereCoordinate_agrees (s t i : ℕ) :
    KIP126.Computation.NuCofiberArchive.sphereCoordinate s t i = sphereBasis s t i := rfl

set_option backward.privateInPublic true in
/-- Transport a prescribed coordinate along its two degree equalities.
Keep the equality proofs internal to the coordinate construction. -/
private def cofiberCoordinate {s t i s' t' i' : ℕ}
    (h : s = s' ∧ t = t' ∧ i = i') (x : Page .nuCofiber s' t') :
    Page .nuCofiber s t := by
  rcases h with ⟨rfl, rfl, rfl⟩
  exact x

private theorem cofiberCoordinate_self (s t i : ℕ)
    (h : s = s ∧ t = t ∧ i = i) (x : Page .nuCofiber s t) :
    cofiberCoordinate h x = x := by
  rcases h with ⟨hs,ht,hi⟩
  cases hs
  cases ht
  cases hi
  rfl

set_option backward.privateInPublic true in
/-- Cν basis calibrated by the top-cell monomial `323,1,1`
(x₁₂₁,₇ times h₁[4]) and the four `Raw.bottomMaps` bindings.
The other valid labels through t = 200 are inverse images of data coordinate
vectors; outside that range, labels use the actual-element family. -/
public def cofiberBasis (s t i : ℕ) : Page .nuCofiber s t := by
  if htop : s = 8 ∧ t = 134 ∧ i = 0 then
    exact cofiberCoordinate htop (Standard.topCell)
  else if hb3 : s = 8 ∧ t = 134 ∧ i = 4 then
    exact cofiberCoordinate hb3 (Standard.bottom 8 134 (sphereBasis 8 134 3))
  else if hb2 : s = 8 ∧ t = 134 ∧ i = 3 then
    exact cofiberCoordinate hb2 (Standard.bottom 8 134 (sphereBasis 8 134 2))
  else if hbY : s = 11 ∧ t = 136 ∧ i = 3 then
    exact cofiberCoordinate hbY (Standard.bottom 11 136 (sphereBasis 11 136 3))
  else if hbT : s = 14 ∧ t = 139 ∧ i = 2 then
    exact cofiberCoordinate hbT (Standard.bottom 14 139 (sphereBasis 14 139 1))
  else
    if hs : KIP126.Computation.NuCofiberArchive.InScope s t then
      if hi : i < KIP126.Computation.NuCofiberArchive.basisCount s t then
        exact (KIP126.Computation.NuCofiberArchive.comparison s t hs).symm
          (KIP126.Computation.NuCofiberArchive.basisVector s t ⟨i,hi⟩)
      else exact KIP126.Computation.NuCofiberArchive.outsideBasis s t i
    else exact KIP126.Computation.NuCofiberArchive.outsideBasis s t i

set_option backward.isDefEq.respectTransparency false in
private theorem cofiberBasis_eq_coordinate (s t : ℕ)
    (hs : KIP126.Computation.NuCofiberArchive.InScope s t)
    (i : Fin (KIP126.Computation.NuCofiberArchive.basisCount s t)) :
    cofiberBasis s t i.val =
      (KIP126.Computation.NuCofiberArchive.comparison s t hs).symm
        (KIP126.Computation.NuCofiberArchive.basisVector s t i) := by
  delta cofiberBasis
  simp only [dif_pos hs, dif_pos i.isLt]
  split_ifs with htop hb3 hb2 hbY hbT
  · rcases htop with ⟨rfl,rfl,hi⟩
    have he : i = ⟨0, by decide⟩ := Fin.ext hi
    subst i
    simpa only [cofiberCoordinate_self, sphereCoordinate_agrees] using
      KIP126.Computation.NuCofiberArchive.comparison_calibrated.1.symm
  · rcases hb3 with ⟨rfl,rfl,hi⟩
    have he : i = ⟨4, by decide⟩ := Fin.ext hi
    subst i
    simpa only [cofiberCoordinate_self, sphereCoordinate_agrees] using
      KIP126.Computation.NuCofiberArchive.comparison_calibrated.2.1.symm
  · rcases hb2 with ⟨rfl,rfl,hi⟩
    have he : i = ⟨3, by decide⟩ := Fin.ext hi
    subst i
    simpa only [cofiberCoordinate_self, sphereCoordinate_agrees] using
      KIP126.Computation.NuCofiberArchive.comparison_calibrated.2.2.1.symm
  · rcases hbY with ⟨rfl,rfl,hi⟩
    have he : i = ⟨3, by decide⟩ := Fin.ext hi
    subst i
    simpa only [cofiberCoordinate_self, sphereCoordinate_agrees] using
      KIP126.Computation.NuCofiberArchive.comparison_calibrated.2.2.2.1.symm
  · rcases hbT with ⟨rfl,rfl,hi⟩
    have he : i = ⟨2, by decide⟩ := Fin.ext hi
    subst i
    simpa only [cofiberCoordinate_self, sphereCoordinate_agrees] using
      KIP126.Computation.NuCofiberArchive.comparison_calibrated.2.2.2.2.symm
  · rfl

public def basis : (o : Raw.Spectrum) → (s t i : ℕ) → Page o s t
  | .sphere, s, t, i => sphereBasis s t i
  | .nuCofiber, s, t, i => cofiberBasis s t i

public def decode (o : Raw.Spectrum) (s t : ℕ) (indices : List ℕ) :
    Option (Page o s t) :=
  if Raw.coordinatesValid Raw.degrees o s t indices then
    some ((indices.map (basis o s t)).sum)
  else none

public def BasisCorrect (d : Raw.Degree) : Prop :=
  ∃ e : Page d.spectrum d.s d.t ≃ₗ[ℤ] (Fin d.monomials.length →₀ ZMod 2),
    ∀ i, e.symm (Finsupp.single i 1) = basis d.spectrum d.s d.t i.val

/-- Catalogue lengths for the sphere archive. -/
public theorem basis_count (d : Raw.Degree) (hd : d ∈ Raw.degrees)
    (hs : d.spectrum = .sphere) :
    Standard.archive.basisCount d.s d.t = d.monomials.length := by
  have hbound : ∀ d ∈ Raw.degrees, d.t ≤ 261 := by decide
  rw [archive_dimension d.s d.t (hbound d hd)]
  have hlength : ∀ d ∈ Raw.degrees, d.spectrum = .sphere →
      basisDimension d.s d.t = d.monomials.length := by decide
  exact hlength d hd hs

public theorem cofiber_basis_correct (d : Raw.Degree) (hd : d ∈ Raw.degrees)
    (hs : d.spectrum = .nuCofiber) : BasisCorrect d := by
  have hc := KIP126.Computation.NuCofiberArchive.selected_count d hd hs
  have hscope := KIP126.Computation.NuCofiberArchive.inScope_of_mem d hd hs
  rcases d with ⟨o,s,t,ms⟩
  dsimp only [Raw.Degree.spectrum] at hs
  subst o
  dsimp only at hc hscope
  change ∃ e : Page .nuCofiber s t ≃ₗ[ℤ] (Fin ms.length →₀ ZMod 2),
    ∀ i, e.symm (Finsupp.single i 1) = cofiberBasis s t i.val
  rw [← hc]
  refine ⟨KIP126.Computation.NuCofiberArchive.comparison s t hscope, ?_⟩
  intro i
  exact (cofiberBasis_eq_coordinate s t hscope i).symm

set_option maxRecDepth 10000 in
private theorem table_degree_bound (d : Raw.Degree) (hd : d ∈ Raw.degrees) : d.t ≤ 261 := by
  have all : ∀ d ∈ Raw.degrees, d.t ≤ 261 := by decide
  exact all d hd

public theorem basis_correct (d : Raw.Degree) (hd : d ∈ Raw.degrees) : BasisCorrect d := by
  rcases d with ⟨o,s,t,ms⟩
  cases o with
  | sphere =>
    have hc := basis_count ⟨.sphere,s,t,ms⟩ hd rfl
    have ht := table_degree_bound ⟨.sphere,s,t,ms⟩ hd
    dsimp only at hc ht
    change ∃ e : background.classical.sphere.Page 2 (s,t) ≃ₗ[ℤ] (Fin ms.length →₀ ZMod 2),
      ∀ i, e.symm (Finsupp.single i 1) = sphereBasis s t i.val
    rw [← hc]
    refine ⟨Standard.coordinates s t ht, ?_⟩
    intro i
    simp only [sphereBasis, dif_pos ht, dif_pos i.isLt]
  | nuCofiber => exact cofiber_basis_correct ⟨.nuCofiber,s,t,ms⟩ hd rfl

end
end KIP126.Computation.Table
