module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Fiber.Cubical.Data

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
universe u

/-- Exactness at the source is already true for the actual cubical homotopy
sets at every level, including dimension zero. -/
theorem fiberProjection_levelLoop_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    GenLoop.Homotopic (f.levelLoop n r p) GenLoop.const ↔
      ∃ q, GenLoop.Homotopic ((fiberProjection f).levelLoop n r q) p := by
  constructor
  · rintro ⟨H⟩
    exact ⟨fiberLiftNullhomotopy f n r p H,GenLoop.Homotopic.refl _⟩
  · rintro ⟨q,hq⟩
    exact (hq.comp_continuousMap (f.level n)).symm.trans
      ⟨fiberProjectionNullhomotopy f n r q⟩

end KIP126.AdamsSynthetic.Source.Prespectrum
