# Reviewer proof outline: a planar Fuglede counterexample

The entry point is [FugledeCounterexample.lean](FugledeCounterexample.lean). The 16-module proof establishes a bounded measurable set of positive finite Lebesgue measure in **ℝ²** that is spectral in the genuine complex **L²** sense and does not tile by arbitrary countable real translations, even allowing null exceptional sets.

The mathematical construction follows **Tao Zhang**, [*Both directions of Fuglede’s conjecture fail in dimension two*, arXiv:2607.15632v1](https://arxiv.org/abs/2607.15632v1). This contribution is a Lean formalization of its spectral-but-nontile construction; it does not claim a new mathematical counterexample, first-formalization priority, or award entitlement. One counterexample disproves the dimension-two equivalence. The independent dimension-one problem remains open.

## Definitions and finite core

[CanonicalDefinitions.lean](CanonicalDefinitions.lean) preserves the [original spectral, L², and a.e. tiling definitions](https://github.com/google-deepmind/formal-conjectures/blob/a924684979d41f543898ec43b940b74e124315d9/FormalConjecturesForMathlib/Analysis/Fourier/SpectralSets.lean) and the quantifiers of the [original Fuglede statement](https://github.com/google-deepmind/formal-conjectures/blob/a924684979d41f543898ec43b940b74e124315d9/FormalConjectures/Wikipedia/Fuglede.lean), within a local namespace.

Write H = ℤ₁₂ × ℤ₁₂ and

- V₀ = {(0,k) : k ∈ ℤ₁₂};
- V₁ = {(k,k) : k ∈ ℤ₁₂};
- V₂ = {(4k+δ, 2k+2δ) : k ∈ ℤ₆, δ ∈ ℤ₂}.

All three have the same 12-point spectrum E = {(f(y),y)}, where
`f = [0,5,0,7,9,2,10,4,7,8,10,10]`.
[FiniteSpectralSeeds.lean](FiniteSpectralSeeds.lean) proves actual complex-exponential orthogonality by geometric sums. For V₂, either the six-term sum vanishes or the two remaining terms have opposite signs. Finite-dimensional synthesis then proves completeness.

There is no common tiling complement for V₀,V₁,V₂. [FiniteNontile.lean](FiniteNontile.lean) proves this universally: quotienting a hypothetical complement into ℤ₄ × ℤ₆ forces equal even-column counts in four rows, while a permutation condition forces their total to be six, contradicting divisibility by four.

Place V₀ in layers 0,1,2, V₂ in layer 3, and V₁ in layer 4 of H × ℤ₅. Apply the CRT map
`((x,y),t) ↦ ((25x+36t) mod 60,y)`.
The resulting A⁺ ⊂ ℤ₆₀ × ℤ₁₂ has 60 points and spectrum
Γ = {((5f(y)+12r) mod 60,y) : y ∈ ℤ₁₂, r ∈ ℤ₅}.
Explicit cross-layer difference witnesses force any tiling complement into one layer, whose projection would complement all three seeds. The finite spectral and nontiling modules prove that they use exactly the same A⁺.

## The same concrete planar region

Copy integer representatives of A⁺ over a 97 × 97 grid, with origins `(60j₁,12j₂)`. The resulting integer set F has
**60 · 97² = 564540** points. Define Ω = F + [0,1)², an exact disjoint union of unit squares. [ConcreteNontile.lean](ConcreteNontile.lean) proves measurability, boundedness, and volume 564540.

[BlockSpectrum.lean](BlockSpectrum.lean) proves the copied finite Gram matrix and function expansion. Its real base frequencies are
`((ξ₁+s₁/97)/60, (ξ₂+s₂/97)/12)`, with ξ ∈ Γ and s₁,s₂ ∈ ℤ₉₇.
[ConcreteSpectrum.lean](ConcreteSpectrum.lean) identifies the copied point set with precisely F and discharges both the finite Gram and expansion inputs. The continuous spectrum Λ contains **every integer shift** of every base frequency.

## Arbitrary a.e. nontiling and genuine L² spectrality

**Nontiling.** A hypothetical countable a.e. real tiling of Ω has a single sampling point u for which all points u+z, z ∈ ℤ², have unique tile membership. Exact half-open-cube membership gives integer translations `c(t)ᵢ = −floor(uᵢ−tᵢ)`, yielding an exact integer-lattice tiling by F. No periodicity of the translation set is assumed. [TilingTransfer.lean](TilingTransfer.lean) uses boundary counting to descend this tiling to a finite-group complement of A⁺. The numerical condition is `8·720 < 60·97`, so the finite nontiling contradiction applies.

**Orthogonality.** [CubeOrthogonality.lean](CubeOrthogonality.lean) factors the union integral into the true finite Gram factor and a unit-cube integral. Different base indices vanish by the finite Gram; equal base indices with different integer shifts vanish by genuine integer Fourier orthogonality on [0,1)². These integral identities are proved for the canonical L² exponential representatives.

**Completeness.** If a union-L² function is orthogonal to every frequency in Λ, its finite weighted slice sums have all integer Fourier coefficients zero. [FourierCube.lean](FourierCube.lean) proves their vanishing through Mathlib’s torus Fourier Hilbert basis, an actual measure-preserving transport, and the a.e. Ico/Ioc boundary change. Finite expansion then forces every slice to vanish. [SpectralCubeBridge.lean](SpectralCubeBridge.lean) applies the orthogonal-complement criterion to obtain the full closed complex span, not just finite orthogonality.

## Final declarations and validation

The final module has no additional mathematical premises:

- `FugledeCounterexample.omega_spectralPair`;
- `FugledeCounterexample.exists_bounded_measurable_spectral_nontile`;
- `FugledeCounterexample.not_FugledeConjectureFor_two`;
- `FugledeCounterexample.completeTwoDimensionalTarget`;
- `FugledeCounterexample.not_joint_dimension_one_and_two`.

Lean **4.34.1**, with Mathlib pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`, completed strict compilation with warnings treated as errors and kernel type checking enabled. An independent frozen-module import checked the exact final types and their transitive axioms: only `propext`, `Classical.choice`, and `Quot.sound`. A separate clean-project run rebuilt all 16 project modules and its audit from an empty project build tree, excluding the original project `.olean` files (exit 0; 48.184 seconds). It used 3443 official Mathlib dependency cache archives; third-party sources were not all rebuilt.

Frozen final-source SHA-256:
`27e08226448eb23f150ec7e95e48c6f98e1ce7bcce8b8b26d9add0b65c55aa44`.
See [final-scope-audit.json](final-scope-audit.json) and [verification-counterexample.txt](verification-counterexample.txt) for the recorded checks. The clean-project evidence is documented in [BUILD.md](BUILD.md), [reproduction-audit.json](reproduction-audit.json), and [fresh-build.log](fresh-build.log).

The exact publication source version was freshly rebuilt again after adding third-party source notices, with no mathematical code changes. All 16 proof modules and `Audit.lean` were built from an empty project build tree; the strict build exited 0. See `release-verification.json`, `release-build.log`, and `source-notice-changes.json`. Earlier 48.184-second build records describe the version before those comment-only notice additions.
