import Lake
open Lake DSL

package Kervaire126Main where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "905b95818eb32af7874a58b427f50c1711a5e96c"

@[default_target]
lean_lib KIP126 where
  globs := #[.one `KIP126, .andSubmodules `KIP126.SpectralSequence,
    .andSubmodules `KIP126.AdamsSynthetic,
    .andSubmodules `KIP126.Literature,
    .andSubmodules `KIP126.AdamsComputation,
    .andSubmodules `KIP126.ProofTools,
    .andSubmodules `KIP126.SSComputation,
    .andSubmodules `KIP126.Main,
    .andSubmodules `KIP126.Geometry]
