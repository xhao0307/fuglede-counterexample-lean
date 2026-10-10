import FiniteSpectralSeeds
import FiniteNontile

/-!
The actual sixty-point finite spectral pair in Tao Zhang,
arXiv:2607.15632v1, Section 4.  The seed proof supplies actual complex
exponential orthogonality and finite completeness.  This module checks
that its point set is exactly the point set used in the nontiling proof.
It contains no continuous spectrality assertion.
-/
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace FugledeSpectral
open scoped BigOperators ComplexConjugate

abbrev G := FugledeSeeds.G
abbrev PointIndex := FugledeSeeds.PointIndex
abbrev FrequencyIndex := FugledeSeeds.FrequencyIndex
abbrev aPoint := FugledeSeeds.aPoint
abbrev spectrumPoint := FugledeSeeds.spectrumPoint
abbrev Aplus := FugledeSeeds.Aplus
abbrev Lplus := FugledeSeeds.Lplus
noncomputable abbrev character := FugledeSeeds.character

/-- Sixty actual seed points satisfy the independent nontiling definition. -/
lemma aPoint_mem_nontile : ∀ a : PointIndex, aPoint a ∈ FugledeNontile.Aplus := by
  decide +kernel

/-- The spectrality and nontiling proofs use the same finite point set. -/
theorem Aplus_eq_nontile : Aplus = FugledeNontile.Aplus := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact aPoint_mem_nontile i
  · rw [FugledeSeeds.card_Aplus, FugledeNontile.card_Aplus]

lemma card_Aplus : Aplus.card = 60 := FugledeSeeds.card_Aplus
lemma card_Lplus : Lplus.card = 60 := FugledeSeeds.card_Lplus

/-- The characters here are exp(2*pi*I*(x*xi/60+y*eta/12)). -/
theorem finiteSpectralGram (i j : FrequencyIndex) :
    (∑ a : PointIndex, conj (character (spectrumPoint i) (aPoint a)) *
      character (spectrumPoint j) (aPoint a)) = if i = j then 60 else 0 :=
  FugledeSeeds.actual_character_gram i j

theorem Aplus_Lplus_finite_spectral_pair :
    Aplus.card = Lplus.card ∧
      ∀ ξ ∈ Lplus, ∀ η ∈ Lplus, ξ ≠ η →
        (∑ a ∈ Aplus, conj (character ξ a) * character η a) = 0 :=
  FugledeSeeds.Aplus_Lplus_finite_spectral_pair

/-- Completeness on the finite point set, stated without any Gram assumption. -/
theorem every_function_expansion (v : G → ℂ) :
    ∃ c : FrequencyIndex → ℂ, ∀ a ∈ Aplus,
      v a = ∑ i : FrequencyIndex, c i * character (spectrumPoint i) a := by
  obtain ⟨c, hc⟩ := FugledeSeeds.every_function_expansion (fun a => v (aPoint a))
  refine ⟨c, ?_⟩
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact hc i

/-- This actual finite spectral set has no finite tiling complement. -/
theorem Aplus_no_complement :
    ¬ ∃ C : Finset G, FugledeNontile.Tiles Aplus C := by
  rw [Aplus_eq_nontile]
  exact FugledeNontile.Aplus_no_complement

#print axioms Aplus_eq_nontile
#print axioms finiteSpectralGram
#print axioms Aplus_Lplus_finite_spectral_pair
#print axioms every_function_expansion
#print axioms Aplus_no_complement
end FugledeSpectral
