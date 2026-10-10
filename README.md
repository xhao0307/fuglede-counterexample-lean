# Planar Fuglede counterexample in Lean

This repository contains a Lean formalization of the **spectral-but-nontiling planar construction** in Tao Zhang, [Both directions of Fuglede’s conjecture fail in dimension two](https://arxiv.org/abs/2607.15632v1), Corollary 4.5. The original mathematical construction is credited to Tao Zhang. The proof scripts and local reviews were produced with OpenAI Codex assistance, under the submitting user's direction; see [ATTRIBUTION.md](ATTRIBUTION.md).

## What is proved

[FugledeCounterexample.lean](FugledeCounterexample.lean) proves, with no additional mathematical premises, that there is a bounded measurable set of positive finite Lebesgue measure in the plane that is spectral and does not tile by translations.

- Spectrality uses actual complex exponentials in `Lp ℂ 2 (volume.restrict Ω)`, pairwise orthogonality, and the full closed complex linear span.
- Nontiling excludes arbitrary countable real translation sets with almost-everywhere coverage and disjointness, without assuming integer translations or periodicity.
- Both properties refer to the same concrete region: 564,540 half-open unit squares obtained from the 60-point finite example and a 97 × 97 block construction.

The main declarations are `FugledeCounterexample.exists_bounded_measurable_spectral_nontile` and `FugledeCounterexample.not_FugledeConjectureFor_two`. This refutes the two-dimensional equivalence. **The independent one-dimensional problem is not resolved here.** Only one of the paper's two counterexample directions is formalized, which suffices to refute the two-dimensional equivalence.

## Reproduction and verification

The toolchain is `leanprover/lean4:v4.34.1`; Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`, with all transitive pins in [lake-manifest.json](lake-manifest.json). Follow [BUILD.md](BUILD.md), then run:

```sh
lake build FugledeCounterexample Audit
```

All 16 proof modules and [Audit.lean](Audit.lean) are registered. Warnings are errors and kernel type checking is enabled. The final declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; the proof chain has no `sorry`, custom mathematical axiom, or `native_decide`. [release-verification.json](release-verification.json) binds the verified release to exact source hashes. Clean project builds reuse pinned upstream dependency caches, while rebuilding this project's own proof modules from source.

The submission recheck on 10 October 2026 rebuilt all 16 proof modules and Audit from another empty own build tree with the same pinned runtime, using the standard Lake build command (exit 0; 58.23 seconds). All 17 source hashes and generated project module hashes matched the earlier exact release. See [submission-recheck-result.json](submission-recheck-result.json) and [submission-recheck-lake.log](submission-recheck-lake.log). Earlier file-reading stalls were resolved by unpacking the identical official runtime into a temporary local directory; they were environment attempts, not proof failures. The separate [source semantic review](submission-semantic-review.md) is an AI-agent review; its new-import limitation was resolved by this later successful build.

[proof-outline.md](proof-outline.md) explains the finite construction, real-translation nontiling transfer, orthogonality, and analytic completeness. The auxiliary `FiniteTiling.lean` is included for context and is not a dependency of the final counterexample.

## Submission scope

This proof is offered for technical and scope review for [JSP-000032](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/problems/catalog-0001-0100.md#JSP-000032). That combined catalogue entry names both dimensions one and two. The independent dimension-one assertion remains unresolved by this project. No award eligibility, first-formalization priority, or official acceptance is asserted. The related scope inquiry is [awards issue #4951](https://github.com/TheJustinSunPrize/awards/issues/4951).

Public repository history starts with publication; earlier local snapshot timestamps are not asserted as public priority evidence. Local independent reviews were conducted by separate AI agents, not external human referees.

## Third-party notices

[NOTICE.md](NOTICE.md) identifies adapted Formal Conjectures and Mathlib source portions. Their full Apache 2.0 license is included in [Apache-2.0.txt](Apache-2.0.txt). These notices do not assign a license to separately written project material. No manuscript text or figures are redistributed.
