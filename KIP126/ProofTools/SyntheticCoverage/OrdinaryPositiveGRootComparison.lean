module

import all KIP126.ProofTools.SyntheticCoverage.OrdinaryPositiveGRoot
import all KIP126.ProofTools.SyntheticCoverage.OrdinaryEarlyRootComparison

/-! Positive-G completion of the actual ordinary early root comparison.
The original root hypotheses are retained. -/
@[expose] section
namespace KIP126.ProofTools.Internal.SyntheticCoverage
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Completed KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- Positive G: original root and middle hypotheses construct a compatible
root on the fixed negative-weight third vertex, then the same long source.
The actual early representative and its exact top are retained throughout. -/
private theorem ordinary_long_source_positive_g_of_root
    (T : TriangleData background.auxiliary)
    (he : (normalizedExponent background.classicalTower T.f : ℤ)+
      normalizedExponent background.classicalTower T.g+normalizedExponent background.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible background T he)
    (hf : normalizedExponent background.classicalTower T.f=0)
    (hg : normalizedExponent background.classicalTower T.g=1)
    (hh : normalizedExponent background.classicalTower T.h=0)
    (i q : ℕ) (hi : 0 < i) (hiq : i < q) (s t : ℤ)
    (z : Ambient background T.Z (s+1,t+1)) (u : Ambient background T.X (s+i+1,t+i))
    (v : Ambient background T.Y (s+q+1,t+q))
    (hd : HasDifferential (background.classical.obj (T.Z.obj background.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) (s+q+1) (t+q) v))
    (hR : ∀ p : ℤ, s+1≤p → p<s+(i+1)-1 →
      ∀ z : Ambient background T.Z (p+1,(t-s+p)+1),
        z ∈ cycles background T.Z ((i+1)-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) →
      ∃ y : Ambient background T.Y (p,t-s+p),
        y ∈ cycles background T.Y ((i+1)-(p-s).toNat:ℕ) (p,t-s+p) ∧
      ∃ k : Ambient background T.Z (p+1,(t-s+p)+1),
        k ∈ cycles background T.Z (q+1-(p-s).toNat:ℕ) (p+1,(t-s+p)+1) ∧
        z-positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) p (t-s+p) y-k ∈
          boundaries background T.Z ((p-s).toNat+1) (p+1,(t-s+p)+1))
    (hH : ∀ z : Ambient background T.Z (s+(i+1),(t+(i+1)-1)+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T (s+(i+1)) (t+(i+1)-1) z ∈
        boundaries background T.X (i+1) (s+(i+1),t+(i+1)-1))
    (ei : XModLambdaN ((background.nu.functor.obj (T.X.obj background.auxiliary))⟦(1:ℤ)⟧) (i+1) ≅
      (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (i+1))⟦(1:ℤ)⟧)
    (hei : XModLambdaN.incl _ (i+1)≫ei.hom=(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (i+1)))
    (R : BiHom (t-s) t (XModLambdaN (normalizedTriangle background T he).obj₃ (i+1)))
    (hRfirst : R≫(background.quotients.tower _).rho 1 (i+1) (by omega)=
      homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (shiftHomotopyClass (0,-1) ((t+1)-(s+1),t+1)
          (nativeFirstLabel T.Z (s+1) (t+1) z))≫
        (levelQuotientShiftIso T.Z (-1) 1).inv≫
          XModLambdaN.map (normalizedThirdNegativeIso T he hg).inv 1)
    (hRtop : R≫XModLambdaN.map (ordinaryNativeTriangle T he hf).mor₃ (i+1)≫ei.hom=
      ordinarySuspendedRepresentative _ (t-s) t (ordinaryEarlyTop T.X i hi s t u)) :
    ∃ a : BiHom ((t-s)-1) t (XModLambdaN (background.nu.functor.obj (T.X.obj background.auxiliary)) (q+1)),
      a≫(background.quotients.tower _).rho (i+1) (q+1) (by omega)=ordinaryEarlyTop T.X i hi s t u ∧
      a≫XModLambdaN.map (background.nu.functor.map T.f) (q+1)=
        homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega)
          (show (t+q)-q=t by omega) (finiteTopLabel T.Y q (by omega) (s+q+1) (t+q) v) := by
  obtain ⟨root,hfirst,hdelta⟩ := ordinary_positive_g_root_square T he hT hg q (by omega) s t z v hd
  obtain ⟨root',_,hsame,hcomp⟩ := positive_g_normalized_root_compatible T he hf hg hh hT
    (i+1) q (by omega) (by omega) s t hR hH R root (hRfirst.trans hfirst.symm)
  have hdelta' := higher_adjacent_delta_equality (normalizedTriangle background T he).obj₃ q
    (by omega) (t-s) t root' root hsame
  exact ordinary_long_source_of_compatible_root T he hT hf i q hi hiq s t u v
    ei hei R root' hcomp hRtop (hdelta'.trans hdelta)

end
end KIP126.ProofTools.Internal.SyntheticCoverage
