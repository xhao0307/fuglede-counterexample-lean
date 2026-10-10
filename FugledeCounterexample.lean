import ConcreteNontile
import ConcreteSpectrum
import CubeOrthogonality
import SpectralCubeBridge

/-!
A complete two-dimensional counterexample to the bounded measurable Fuglede
conjecture. The concrete mathematical construction is from Tao Zhang,
arXiv:2607.15632v1. The spectrum and arbitrary a.e. translational nontiling
are both proved for the same actual finite union of 564540 unit squares.
The independent one-dimensional question is not resolved here.
-/
set_option Elab.async false
set_option debug.skipKernelTC false
namespace FugledeCounterexample
open Set MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section

def spectrum : Set (Fin 2 → ℝ) :=
  FugledeSpectralBridge.spectrum FugledeConcreteSpectrum.frequency

theorem finite_gram_as_card (i j : FugledeConcreteSpectrum.Index) :
    (∑ f ∈ FugledeConcrete.vectorBlock,
      conj (FugledeTarget.exponentialCharacter (FugledeConcreteSpectrum.frequency i)
        (FugledeCube.intVec f)) *
      FugledeTarget.exponentialCharacter (FugledeConcreteSpectrum.frequency j)
        (FugledeCube.intVec f)) =
      if i = j then (FugledeConcrete.vectorBlock.card : ℂ) else 0 := by
  simpa [FugledeConcrete.vectorBlock_card] using FugledeConcreteSpectrum.finite_gram i j

/-- The actual region has a complete orthogonal family of true Euclidean exponentials. -/
theorem omega_spectralPair : FugledeTarget.spectralPair FugledeConcrete.omega spectrum := by
  refine ⟨FugledeConcrete.omega_measurable.nullMeasurableSet,
    FugledeConcrete.omega_positive_volume, FugledeConcrete.omega_finite_volume, ?_, ?_⟩
  · intro ξ hξ η hη hne
    obtain ⟨⟨i, z⟩, rfl⟩ := hξ
    obtain ⟨⟨j, w⟩, rfl⟩ := hη
    exact FugledeOrthogonality.e_shifted_inner_eq_zero FugledeConcrete.vectorBlock
      FugledeConcreteSpectrum.frequency (by
        intro p q
        by_cases hpq : p = q
        · simpa only [ite_eq_left hpq] using finite_gram_as_card p q
        · simpa only [ite_eq_right hpq] using finite_gram_as_card p q) i j z w hne
  · exact FugledeSpectralBridge.spectrum_closedSpan_top FugledeConcrete.vectorBlock
      FugledeConcreteSpectrum.frequency FugledeConcreteSpectrum.finite_expansion

theorem omega_isSpectral : FugledeTarget.isSpectral FugledeConcrete.omega :=
  ⟨spectrum, omega_spectralPair⟩

/-- All regularity, true L2 completeness, and arbitrary a.e. nontiling are discharged. -/
theorem exists_bounded_measurable_spectral_nontile :
    ∃ Ω : Set (Fin 2 → ℝ), Bornology.IsBounded Ω ∧ MeasurableSet Ω ∧
      0 < volume Ω ∧ volume Ω ≠ ⊤ ∧ FugledeTarget.isSpectral Ω ∧
      ¬ FugledeTarget.tilesByTranslation Ω :=
  ⟨FugledeConcrete.omega, FugledeConcrete.omega_bounded, FugledeConcrete.omega_measurable,
    FugledeConcrete.omega_positive_volume, FugledeConcrete.omega_finite_volume,
    omega_isSpectral, FugledeConcrete.omega_nontile⟩

/-- The full two-dimensional equivalence fails for the canonical original definitions. -/
theorem not_FugledeConjectureFor_two : ¬ FugledeTarget.FugledeConjectureFor 2 := by
  intro h
  exact FugledeConcrete.omega_nontile
    ((h FugledeConcrete.omega FugledeConcrete.omega_bounded FugledeConcrete.omega_measurable
      FugledeConcrete.omega_positive_volume).mp omega_isSpectral)

theorem completeTwoDimensionalTarget : FugledeTarget.CompleteTwoDimensionalTarget :=
  not_FugledeConjectureFor_two

/-- This refutes the joint universal claim; it leaves the independent dimension-one variant open. -/
theorem not_joint_dimension_one_and_two :
    ¬ (FugledeTarget.FugledeConjectureFor 1 ∧ FugledeTarget.FugledeConjectureFor 2) := by
  rintro ⟨_, htwo⟩
  exact not_FugledeConjectureFor_two htwo

end
end FugledeCounterexample

#print axioms FugledeCounterexample.omega_spectralPair
#print axioms FugledeCounterexample.exists_bounded_measurable_spectral_nontile
#print axioms FugledeCounterexample.not_FugledeConjectureFor_two
#print axioms FugledeCounterexample.completeTwoDimensionalTarget
#print axioms FugledeCounterexample.not_joint_dimension_one_and_two
