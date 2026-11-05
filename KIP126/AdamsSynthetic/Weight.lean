module

public import KIP126.AdamsSynthetic.ExtensionLabels

@[expose] section

/-! Weight lowering at E∞ in the specified ν-family.
The maps, composition, and naturality are structural data;
surjectivity is supplied by the corresponding literature result. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The comparison at weight `w`, with nonnegative λ exponent determined by `w ≤ t`. -/
public noncomputable def nuWeightLabel (D : AdamsSyntheticBackground C Syn) (X : AdamsObject (coefficients := D.coefficients))
    (s t w : ℤ) (hw : w ≤ t)
    (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t)) :
    (D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).E₂ (s,t,w) :=
  regradeE2 (by
    ext <;> simp [Int.toNat_of_nonneg (sub_nonneg.mpr hw)])
    (targetNuLabel D X s t (t-w).toNat x)

/-- A coherent weight comparison on the ν(X) infinity pages, compatible with the
specified E₂ labels. -/
public structure NuInfinityWeightMaps (D : AdamsSyntheticBackground C Syn) where
  map : ∀ (X : AdamsObject (coefficients := D.coefficients)) (s t w₁ w₂ : ℤ) (_hw : w₁ ≤ w₂) (_ht : w₂ ≤ t),
    ((D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).sequence.ssData (s,t,w₂)).eInfty ⟶
      ((D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).sequence.ssData (s,t,w₁)).eInfty
  map_self : ∀ (X : AdamsObject (coefficients := D.coefficients)) (s t w : ℤ) (hw : w ≤ t),
    map X s t w w le_rfl hw = 𝟙 _
  map_comp : ∀ (X : AdamsObject (coefficients := D.coefficients)) (s t w₁ w₂ w₃ : ℤ)
      (h₁₂ : w₁ ≤ w₂) (h₂₃ : w₂ ≤ w₃) (h₃ : w₃ ≤ t),
    map X s t w₂ w₃ h₂₃ h₃ ≫ map X s t w₁ w₂ h₁₂ (h₂₃.trans h₃) =
      map X s t w₁ w₃ (h₁₂.trans h₂₃) h₃
  naturality : ∀ (X Y : AdamsObject (coefficients := D.coefficients)) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
      (s t w₁ w₂ : ℤ) (hw : w₁ ≤ w₂) (ht : w₂ ≤ t),
    (D.family.map (D.nu.functor.map f)).eInftyMap (s,t,w₂) ≫ map Y s t w₁ w₂ hw ht =
      map X s t w₁ w₂ hw ht ≫ (D.family.map (D.nu.functor.map f)).eInftyMap (s,t,w₁)
  representative : ∀ (X : AdamsObject (coefficients := D.coefficients)) (s t w₁ w₂ : ℤ)
      (hw : w₁ ≤ w₂) (ht : w₂ ≤ t)
      (x : (D.classical.obj (X.obj D.auxiliary)).Page 2 (s,t))
      (z : ((D.family.obj (D.nu.functor.obj (X.obj D.auxiliary))).sequence.ssData (s,t,w₂)).eInfty),
    HasInfinityRepresentative _ 2 (s,t,w₂) (nuWeightLabel D X s t w₂ ht x) z →
      HasInfinityRepresentative _ 2 (s,t,w₁) (nuWeightLabel D X s t w₁ (hw.trans ht) x)
        (map X s t w₁ w₂ hw ht z)

end KIP126.AdamsSynthetic
