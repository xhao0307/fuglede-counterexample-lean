# Attribution and source provenance

## Mathematical source

**Tao Zhang**, *Both directions of Fuglede’s conjecture fail in dimension two*, [arXiv:2607.15632v1](https://arxiv.org/abs/2607.15632v1), submitted 17 July 2026. The arXiv record names one author, Tao Zhang, and displays a [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) license.

The 60-point spectral-but-nontile construction, its three finite seeds, and the finite-to-planar strategy are credited to this paper. The present work formalizes one counterexample direction and its full analytic and tiling implications in Lean. This is an AI-assisted formalization of an existing mathematical construction. The one-dimensional conjecture remains unresolved by this project. No manuscript text or figures are included in this source package.

## Adapted source

**Formal Conjectures.** [CanonicalDefinitions.lean](CanonicalDefinitions.lean) adapts definitions and supporting character lemmas from:

- [SpectralSets.lean](https://github.com/google-deepmind/formal-conjectures/blob/a924684979d41f543898ec43b940b74e124315d9/FormalConjecturesForMathlib/Analysis/Fourier/SpectralSets.lean): translations, actual exponential characters, continuity/norm/L² membership lemmas, spectral pairs, spectral sets, and a.e. translational tilings;
- [Wikipedia/Fuglede.lean](https://github.com/google-deepmind/formal-conjectures/blob/a924684979d41f543898ec43b940b74e124315d9/FormalConjectures/Wikipedia/Fuglede.lean): the bounded measurable positive-volume universal conjecture.

Both are pinned to commit `a924684979d41f543898ec43b940b74e124315d9`. The preserved upstream attribution is **Copyright 2026 The Formal Conjectures Authors**, under [Apache License 2.0](https://github.com/google-deepmind/formal-conjectures/blob/a924684979d41f543898ec43b940b74e124315d9/LICENSE). Changes include local namespace wrapping, formatting, and minor proof-variable names; the mathematical quantifiers are preserved. The additional final-target wrapper and counterexample proofs are project additions.

**Mathlib source fragment.** The three local `UnitAddCircle` measure instances in [FourierCube.lean](FourierCube.lean) and [CubeOrthogonality.lean](CubeOrthogonality.lean) reuse the normalized Haar-measure setup in [AddCircleMulti.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Fourier/AddCircleMulti.lean), pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`. This small setup fragment is credited conservatively as adapted source: **Copyright (c) 2023 David Loeffler. All rights reserved. Authors: David Loeffler.** Its upstream license is [Apache 2.0](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/LICENSE). This notice concerns the identified fragment, not a new license assignment for the entire project files.

## Imported dependency

Mathlib is declared as the pinned Lake dependency in [lakefile.toml](lakefile.toml). Its existing Fourier Hilbert basis, measure transport, Lp, finite character, and algebraic APIs are imported dependencies. Their library proof implementations are not reproduced as project theorem bodies. The small setup fragment above is recorded separately from this API use.

## License and notice handling

For redistributed Apache-covered material, section 4 requires a license copy, prominent modification notices for changed files, retention of relevant upstream notices, and preservation of applicable upstream `NOTICE` material. No tracked `NOTICE` file was found in either checked pinned repository. Their per-file copyright attributions still matter. [Apache 2.0 source terms](https://github.com/google-deepmind/formal-conjectures/blob/a924684979d41f543898ec43b940b74e124315d9/LICENSE).

The release includes the full license in [Apache-2.0.txt](Apache-2.0.txt) and the consolidated third-party notices in [NOTICE.md](NOTICE.md). The three adapted files carry source and modification notices in their headers; the Mathlib notices identify only the three local measure instances. This document assigns no new license to the separately written project material; that release decision remains with the publisher.

## Release-version evidence

Earlier semantic audits and reproduction records concern the sources before the notice updates. Only comments changed in the three files identified above; [source-notice-changes.json](source-notice-changes.json) records the old and release hashes and the unchanged proof code. The final theorem source remains `27e08226448eb23f150ec7e95e48c6f98e1ce7bcce8b8b26d9add0b65c55aa44`.

The exact release sources then passed a fresh build of all 16 proof modules and `Audit`, with warnings treated as errors and kernel checking enabled. The final declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. [release-verification.json](release-verification.json) binds this check to the release source hashes, and [release-build.log](release-build.log) contains the build and declaration output. Existing official Mathlib dependency caches were used; the project's own proof modules were rebuilt without copying their earlier compiled artifacts.

## AI assistance and evidenced human role

Proof scripting, auxiliary computations, verification orchestration, semantic audits, and review documents in this workspace were produced with **OpenAI Codex assistance**, including coordinated AI agents. Lean compilation and axiom checks validate the resulting proof artifacts; they are distinct from a human authorship claim.

The submitting account is xhao0307. The human requester initiated and directed the project and authorized verification, publication, and submission. Codex generated/adapted the proof scripts and performed the local checks. This does not claim that the human manually authored each proof step, and repository ownership or the latest commit alone does not establish formalization authorship. The connection between the human applicant and the AI-assisted work remains subject to the organizers' attribution review. Mathematical authorship of the cited construction remains attributed to Tao Zhang.

This provenance note makes no claim of first-formalization priority, award eligibility, official endorsement, or ownership of original project code.
