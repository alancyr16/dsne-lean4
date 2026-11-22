import Lake
open Lake DSL

-- DSNE Formal Proofs — Lean 4 / Mathlib4
-- Theorems: Tesla Prime Desert, TM Barrier, TRL-1, Closure Laws, Riemann Equilibrium
-- CYR Technologies · Alan Cyr · Phil Woodward
-- Established: 2026-11-21

package «dsne» where
  name := "dsne"
  version := Version.parse "0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib «DSNE» where
  -- Proof source: DSNE_Lean4_Proofs.lean (renamed to DSNE.lean per setup script)
  roots := #[`DSNE]
