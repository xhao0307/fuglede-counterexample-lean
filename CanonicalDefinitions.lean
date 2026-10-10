/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
http://www.apache.org/licenses/LICENSE-2.0

Definitions adapted without changing mathematical scope from
FormalConjecturesForMathlib/Analysis/Fourier/SpectralSets.lean at
Google Formal Conjectures commit a924684979d41f543898ec43b940b74e124315d9.
The FugledeConjectureFor definition is adapted from
FormalConjectures/Wikipedia/Fuglede.lean at the same commit.
A copy of the Apache 2.0 license is in licenses/Apache-2.0.txt.
The original namespace-free names are enclosed here to avoid collisions.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Continuity

namespace FugledeTarget
open Real Set Complex MeasureTheory
open scoped InnerProductSpace

def translateSet {d : ℕ} (Ω : Set (Fin d → ℝ)) (t : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | x - t ∈ Ω}

noncomputable def exponentialCharacter {d : ℕ} (ξ x : Fin d → ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * (∑ i, ξ i * x i))

theorem continuous_exponentialCharacter {d : ℕ} (ξ : Fin d → ℝ) :
    Continuous (exponentialCharacter ξ) := by
  unfold exponentialCharacter
  continuity

theorem norm_exponentialCharacter {d : ℕ} (ξ x : Fin d → ℝ) :
    ‖exponentialCharacter ξ x‖ = 1 := by
  unfold exponentialCharacter
  have h : 2 * π * Complex.I * (∑ i, ξ i * x i) =
      Complex.I * ((2 * π * ∑ i, ξ i * x i) : ℝ) := by
    simp
    ring
  rw [h, Complex.norm_exp_I_mul_ofReal]

theorem exponentialCharacter_memLp {d : ℕ} {Ω : Set (Fin d → ℝ)}
    (hΩ_finite : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) :
    MemLp (exponentialCharacter ξ) 2 (volume.restrict Ω) := by
  rw [MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_exponentialCharacter ξ).aestronglyMeasurable]
  simp_rw [norm_exponentialCharacter]
  change IntegrableOn (fun _ ↦ (1 : ℝ) ^ 2) Ω volume
  simpa using (MeasureTheory.integrableOn_const
    (μ := volume) (s := Ω) (C := (1 : ℝ)) hΩ_finite)

def spectralPair {d : ℕ} (Ω Λ : Set (Fin d → ℝ)) : Prop :=
  NullMeasurableSet Ω volume ∧ 0 < volume Ω ∧
  ∃ hΩ_finite : volume Ω ≠ ⊤,
    let e : (Fin d → ℝ) → MeasureTheory.Lp ℂ 2 (volume.restrict Ω) := fun ξ ↦
      MeasureTheory.MemLp.toLp (exponentialCharacter ξ)
        (exponentialCharacter_memLp hΩ_finite ξ)
    (∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → ⟪e ξ₁, e ξ₂⟫_ℂ = 0) ∧
    Submodule.topologicalClosure
      (Submodule.span ℂ (Set.range fun (ξ : Λ) ↦ e ξ.1)) = ⊤

def isSpectral {d : ℕ} (Ω : Set (Fin d → ℝ)) : Prop := ∃ Λ, spectralPair Ω Λ

def tilesByTranslation {d : ℕ} (Ω : Set (Fin d → ℝ)) : Prop :=
  ∃ T : Set (Fin d → ℝ), T.Countable ∧
    volume (Set.univ \ (⋃ t ∈ T, translateSet Ω t)) = 0 ∧
    (∀ {t₁ t₂ : Fin d → ℝ}, t₁ ∈ T → t₂ ∈ T → t₁ ≠ t₂ →
      volume (translateSet Ω t₁ ∩ translateSet Ω t₂) = 0)

def FugledeConjectureFor (d : ℕ) : Prop :=
  ∀ Ω : Set (Fin d → ℝ), Bornology.IsBounded Ω → MeasurableSet Ω →
    0 < volume Ω → (isSpectral Ω ↔ tilesByTranslation Ω)

/-- A completed candidate must prove this statement without extra premises.
The one-dimensional conjecture is an independent target. -/
def CompleteTwoDimensionalTarget : Prop := ¬ FugledeConjectureFor 2

end FugledeTarget
