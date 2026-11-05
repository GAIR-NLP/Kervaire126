module
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Prespectrum
import all KIP126.AdamsSynthetic.Internal.ClassicalModel.Sphere
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Fiber.Kernel.Lift.Data
import all KIP126.AdamsSynthetic.Internal.HInjective.PrespectrumConstruction.Prespectrum.Fiber.Proofs

@[expose] section

namespace KIP126.AdamsSynthetic.Source.Prespectrum
open CategoryTheory Topology
universe u

/-- A based source nullhomotopy transports a fiber loop into the image of
actual based loops of the target. -/
theorem fiberConnecting_levelLoop_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n r : ℕ) (p : GenLoop (Fin r) ((fiber f).level n) ((fiber f).level n).point) :
    GenLoop.Homotopic ((fiberProjection f).levelLoop n r p) GenLoop.const ↔
      ∃ q, GenLoop.Homotopic ((fiberConnecting f).levelLoop n r q) p := by
  constructor
  · rintro ⟨H⟩
    refine ⟨fiberKernelLoop f n r p H,?_⟩
    exact ⟨(fiberMoveHomotopy f n r p H).symm.trans (fiberPaddingHomotopy f n r p H)⟩
  · rintro ⟨q,hq⟩
    have hh := hq.comp_continuousMap ((fiberProjection f).level n)
    exact hh.symm

end KIP126.AdamsSynthetic.Source.Prespectrum
