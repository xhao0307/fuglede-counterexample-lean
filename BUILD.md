# Reproduce the frozen two-dimensional Fuglede formalization

This project pins Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The eight transitive Git revisions are recorded in `lake-manifest.json`. All sixteen mathematical source modules and `Audit.lean` belong to this standalone project.

From the directory containing `lakefile.toml`, with the pinned Lean toolchain available through `lake`, run:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get \
  Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.Group.Fin.Basic Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Algebra.Order.Floor.Ring Mathlib.Analysis.Fourier.AddCircleMulti Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality \
  Mathlib.Analysis.InnerProductSpace.Projection.Submodule Mathlib.Analysis.SpecialFunctions.Complex.Circle Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar \
  Mathlib.Data.Fin.Basic Mathlib.Data.Fin.VecNotation Mathlib.Data.Finset.Basic \
  Mathlib.Data.Finset.Card Mathlib.Data.Finset.Prod Mathlib.Data.Fintype.Card \
  Mathlib.Data.Fintype.Prod Mathlib.Data.Int.Interval Mathlib.Data.ZMod.Basic \
  Mathlib.LinearAlgebra.FiniteDimensional.Basic Mathlib.MeasureTheory.Function.L2Space Mathlib.MeasureTheory.Group.Measure \
  Mathlib.MeasureTheory.Integral.Bochner.Basic Mathlib.MeasureTheory.Integral.Bochner.Set Mathlib.MeasureTheory.Measure.Lebesgue.Basic \
  Mathlib.RingTheory.Polynomial.Cyclotomic.Expand Mathlib.Tactic.Abel Mathlib.Tactic.Continuity \
  Mathlib.Tactic.FieldSimp Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith \
  Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Topology.Bornology.Constructions
lake build FugledeCounterexample Audit
```

`lakefile.toml` sets `warningAsError=true` and `debug.skipKernelTC=false` for every project module. The library registers all sixteen source roots, so the build compiles the entire supplied proof chain and the audit. `Audit.lean` prints the canonical spectral-pair/conjecture definitions, six final endpoint types, and their transitive axiom dependencies.

The cache command obtains official upstream Mathlib dependency artifacts matched to the pinned source and dependency hashes. This is not a claim that every third-party dependency has been recompiled from source. Our independent verification starts with an empty project build tree and compiles all sixteen supplied mathematical modules and the audit from source. No `.olean` from the original formalization directory is copied.

For the recorded local verification only, the existing official `work/mathlib-cache` `.ltar` archives are reused. Dependency source checkouts are independently checked out at their pins; Git object storage is shared with existing local repositories, while source working trees and build artifacts are separate. A portable source package does not require those local Git alternates: `lake update` fetches the fixed official repositories.

The mathematical construction is attributed to Tao Zhang, arXiv:2607.15632v1. The proof gives a two-dimensional counterexample; it does not settle the independent dimension-one question or assert priority/award eligibility.

The exact publication source version was freshly rebuilt again after adding third-party source notices, with no mathematical code changes. All 16 proof modules and `Audit.lean` were built from an empty project build tree; the strict build exited 0. See `release-verification.json`, `release-build.log`, and `source-notice-changes.json`. Earlier 48.184-second build records describe the version before those comment-only notice additions.
