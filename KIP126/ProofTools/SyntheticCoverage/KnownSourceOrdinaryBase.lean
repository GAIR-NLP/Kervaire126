module

public import KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch

public import KIP126.ProofTools.MahowaldLeibniz.PositiveBranches

public import KIP126.ProofTools.E2Boundary

import all KIP126.ProofTools.SyntheticCoverage.KnownSourceOrdinary

/-! Ordinary known-source criterion at upper length one.
The finite source is the ordinary image of the adjacent lift
with first label `y=F₂x`. -/

@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Completed
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2500000

/-- The K₁=1 ordinary known-source branch, with the original restricted lower conditions. -/
public theorem known_source_differential_ordinary_second_top_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 1)
    (hh : normalizedExponent background.classicalTower T.h = 0)
    (b L : ℕ) (hb : 0 < b) (hL : 0 < L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (y : Ambient background T.Y (B+1,W))
    (hyF : y=(background.classical.map T.f).pageMap 2 (B+1,W) x)
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L)+1,(W+L)+1))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      ((background.classical.map T.h).pageMap 2 (((B+1)+L)+1,(W+L)+1) z₂) (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L)+1,(W+L)+1) ((((B+1)+L)+b+1)+1,((W+L)+b)+1) z₂
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j-1+1,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L:ℕ)+j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j-1+1,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j-1+1,(W+L)+j+1),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1+1,(W+L)+j+1) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j-1+1) ((W+L)+j+1)
            ((background.classical.map T.h).pageMap 2 ((((B+1)+L)+1)+j-1+1,(W+L)+j+1) z₂) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((((B+1)+L)+1)+j-1+1,(W+L)+j))
    (hy : y ∈ cycles background T.Y (L+b:ℕ) (B+1,W))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (((B+1)+L)+b+1) ((W+L)+b) z = 0 →
      z ∈ boundaries background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b:ℕ) (B+1,W) y ∧
      IsCycle background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b:ℕ)+1) (B+1,W) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L hL
    (B+1) W x u).mp hdx
  let η₀ := ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) L
  have hfirst : η₀ ≫ (background.quotients.tower _).rho 1 L hL =
      nativeFirstLabel T.Y (B+1) W y := by
    dsimp only [η₀]
    rw [Category.assoc,←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality,
      ←Category.assoc,hζ,native_first_label_natural,←hyF]
  let U := boundaryRepresentative T.X L (B+1) W ζ
  have hboundary : U ≫ background.nu.functor.map T.f =
      homotopyRegrade (show (W-(B+1))-1=(W+L)-(((B+1)+L)+1) by omega)
        (show W+L=W+L by rfl)
        (biSuspensionHomEquiv (W-(B+1)) W L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L)) := by
    simpa only [U,η₀,boundaryRepresentative] using
      (boundary_representative_natural T.X T.Y (background.nu.functor.map T.f) L (B+1) W ζ).symm
  have hbot := known_source_ordinary_bottom_differential_second T he hT hf hg hh
    b L hb hL ((B+1)+L) (W+L) (B+1) W ((L+b:ℕ)+1)
    (by omega) (by omega) (by omega) y η₀ hfirst
    (by simpa only [add_sub_cancel_right] using hy)
    u z₂ v huz hdz₂ Pm hPm hbottom U hU hboundary P hP hv
    (by simpa only [Nat.cast_add] using hker)
  simpa only [Nat.cast_add] using hbot


/-- The K₁=1 ordinary known-source branch, with the original restricted lower conditions. -/
public theorem known_source_differential_ordinary_third_top_one
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ) +
      normalizedExponent background.classicalTower T.g + normalizedExponent background.classicalTower T.h = 1)
    (hf : normalizedExponent background.classicalTower T.f = 0)
    (hg : normalizedExponent background.classicalTower T.g = 0)
    (hh : normalizedExponent background.classicalTower T.h = 1)
    (b L : ℕ) (hb : 0 < b) (hL : 0 < L) (B W : ℤ)
    (x : Ambient background T.X (B+1,W))
    (y : Ambient background T.Y (B+1,W))
    (hyF : y=(background.classical.map T.f).pageMap 2 (B+1,W) x)
    (u : Ambient background T.X ((B+1)+L+1,W+L))
    (hdx : HasDifferential (background.classical.obj (T.X.obj background.auxiliary))
      (L+1) (B+1,W) ((B+1)+L+1,W+L) x u)
    (z₂ : Ambient background T.Z (((B+1)+L),(W+L)))
    (v : Ambient background T.Y (((B+1)+L)+b+1,(W+L)+b))
    (huz : (background.classicalSuspension T.X).DesuspendsClass (((B+1)+L)+1) ((W+L)+1)
      (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh) ((B+1)+L) (W+L) z₂)
      (by simpa using u))
    (hdz₂ : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (b+1) (((B+1)+L),(W+L)) (((B+1)+L)+b+1,(W+L)+b) z₂
      ((background.classical.map T.g).pageMap 2 (((B+1)+L)+b+1,(W+L)+b) v))
    (Pm : (j : ℕ) → Submodule ℤ (Ambient background T.Y ((((B+1)+L)+1)+j-1+1,(W+L)+j)))
    (hPm : ∀ j : ℕ, 1≤j → j<(b+1)-1 → boundaries background T.Y ((L:ℕ)+j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) ≤ Pm j)
    (hbottom : ∀ j : ℕ, 1≤j → j<(b+1)-1 →
      ∀ x : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
        x ∈ cycles background T.X (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1+1,(W+L)+j) →
        (background.classical.map T.f).pageMap 2 ((((B+1)+L)+1)+j-1+1,(W+L)+j) x ∈ Pm j →
        ∃ z₂ : Ambient background T.Z ((((B+1)+L)+1)+j-1,(W+L)+j),
          z₂ ∈ cycles background T.Z (((b+1):ℤ)-j) ((((B+1)+L)+1)+j-1,(W+L)+j) ∧
        ∃ u : Ambient background T.X ((((B+1)+L)+1)+j-1+1,(W+L)+j),
          (background.classicalSuspension T.X).DesuspendsClass ((((B+1)+L)+1)+j-1+1) ((W+L)+j+1)
            (positiveFirstQuotientOperation T.Z (.shift 1 T.X) (positiveHMap T hh)
              ((((B+1)+L)+1)+j-1) ((W+L)+j) z₂) (by simpa only [add_sub_cancel_right] using u) ∧
          x-u ∈ boundaries background T.X ((0:ℤ)+j+1) ((((B+1)+L)+1)+j-1+1,(W+L)+j))
    (hy : y ∈ cycles background T.Y (L+b:ℕ) (B+1,W))
    (P : Submodule ℤ (Ambient background T.Y ((((B+1)+L)+b+1),((W+L)+b))))
    (hP : permanentCycles background T.Y ((((B+1)+L)+b+1),((W+L)+b)) ≤ P)
    (hv : v ∈ P)
    (hker : ∀ z ∈ P, (background.classical.map T.g).pageMap 2 ((((B+1)+L)+b+1),((W+L)+b)) z = 0 →
      z ∈ boundaries background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b))) :
    IsCycle background T.Y (L+b:ℕ) (B+1,W) y ∧
      IsCycle background T.Y (L+b:ℕ) ((((B+1)+L)+b+1),((W+L)+b)) v ∧
      DifferentialAt background T.Y ((L+b:ℕ)+1) (B+1,W) ((((B+1)+L)+b+1),((W+L)+b)) y v := by
  have hT : NormalizedTriangleCompatible background T he :=
    KIP126.Literature.Standard.normalized_triangle_distinguished T _
  obtain ⟨ζ,hζ,hU⟩ := (differential_iff_specified_adjacent_lift T.X L hL
    (B+1) W x u).mp hdx
  let η₀ := ζ ≫ XModLambdaN.map (background.nu.functor.map T.f) L
  have hfirst : η₀ ≫ (background.quotients.tower _).rho 1 L hL =
      nativeFirstLabel T.Y (B+1) W y := by
    dsimp only [η₀]
    rw [Category.assoc,←(background.quotients.natural (background.nu.functor.map T.f)).rho_naturality,
      ←Category.assoc,hζ,native_first_label_natural,←hyF]
  let U := boundaryRepresentative T.X L (B+1) W ζ
  have hboundary : U ≫ background.nu.functor.map T.f =
      homotopyRegrade (show (W-(B+1))-1=(W+L)-(((B+1)+L)+1) by omega)
        (show W+L=W+L by rfl)
        (biSuspensionHomEquiv (W-(B+1)) W L (background.nu.functor.obj (T.Y.obj background.auxiliary))
          (η₀ ≫ XModLambdaN.proj _ L)) := by
    simpa only [U,η₀,boundaryRepresentative] using
      (boundary_representative_natural T.X T.Y (background.nu.functor.map T.f) L (B+1) W ζ).symm
  have hbot := known_source_ordinary_bottom_differential_third T he hT hf hg hh
    b L hb hL ((B+1)+L) (W+L) (B+1) W ((L+b:ℕ)+1)
    (by omega) (by omega) (by omega) y η₀ hfirst
    (by simpa only [add_sub_cancel_right] using hy)
    u z₂ v huz hdz₂ Pm hPm hbottom U hU hboundary P hP hv
    (by simpa only [Nat.cast_add] using hker)
  simpa only [Nat.cast_add] using hbot


end
end KIP126.ProofTools.Internal.SyntheticCoverage
