/-
The three local UnitAddCircle measure instances below are adapted from
Mathlib/Analysis/Fourier/AddCircleMulti.lean at Mathlib commit
d13f23b723b8a846827a245b89c10fc7d3f11612, in this file's local namespace.
Original portion notice:
Copyright (c) 2023 David Loeffler. All rights reserved.
Authors: David Loeffler
This adapted portion is licensed under Apache 2.0; see licenses/Apache-2.0.txt.
The remaining original proof development is not assigned a license by this notice.
-/
import FourierCube
import SpectralSlices
import Mathlib.MeasureTheory.Function.L2Space
import CubeCharacters

/-! Genuine integer Fourier orthogonality on the half-open cube. -/
set_option Elab.async false
set_option debug.skipKernelTC false
namespace FugledeOrthogonality
open MeasureTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace ENNReal Classical
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d : ℕ}

theorem torus_integer_gram (z w : Fin d → ℤ) :
    (∫ t : UnitAddTorus (Fin d), conj (UnitAddTorus.mFourier z t) *
      UnitAddTorus.mFourier w t) = if z = w then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin d))) z w
  have hh : (∫ t : UnitAddTorus (Fin d), conj (UnitAddTorus.mFourierLp 2 z t) *
      UnitAddTorus.mFourierLp 2 w t) = if z = w then 1 else 0 := by
    simpa only [L2.inner_def, RCLike.inner_apply, mul_comm] using h
  calc
    _ = ∫ t : UnitAddTorus (Fin d), conj (UnitAddTorus.mFourierLp 2 z t) *
        UnitAddTorus.mFourierLp 2 w t := by
      apply integral_congr_ae
      filter_upwards [UnitAddTorus.coeFn_mFourierLp 2 z, UnitAddTorus.coeFn_mFourierLp 2 w]
        with t hz hw
      rw [hz, hw]
    _ = _ := hh

/-- Complete actual integral matrix; no unit-cube orthogonality premise. -/
theorem unitCube_integer_gram (z w : Fin d → ℤ) :
    (∫ u in FugledeCube.unitCube, conj (FugledeFourier.integerCharacter z u) *
      FugledeFourier.integerCharacter w u) = if z = w then 1 else 0 := by
  calc
    _ = ∫ t : UnitAddTorus (Fin d),
        conj (FugledeFourier.integerCharacter z (FugledeFourier.torusMap t)) *
          FugledeFourier.integerCharacter w (FugledeFourier.torusMap t) :=
      (FugledeFourier.torusMap_measurePreserving.integral_comp
        FugledeFourier.torusMap_measurableEmbedding
        (fun u => conj (FugledeFourier.integerCharacter z u) *
          FugledeFourier.integerCharacter w u)).symm
    _ = _ := by
      simp_rw [← FugledeFourier.mFourier_torusMap]
      exact torus_integer_gram z w

open FugledeCharacters

abbrev RPoint (d : ℕ) := Fin d → ℝ
abbrev IPoint (d : ℕ) := Fin d → ℤ

/-- The exact Lp representative used by the canonical spectralPair definition. -/
def e (F : Finset (IPoint d)) (ξ : RPoint d) :
    Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F)) :=
  (FugledeTarget.exponentialCharacter_memLp (FugledeCube.volume_cubeUnion_ne_top F) ξ).toLp
    (FugledeTarget.exponentialCharacter ξ)
lemma coe_e (F : Finset (IPoint d)) (ξ : RPoint d) :
    e F ξ =ᵐ[volume.restrict (FugledeCube.cubeUnion F)] character ξ :=
  MemLp.coeFn_toLp _
lemma e_inner_integral (F : Finset (IPoint d)) (ξ η : RPoint d) :
    ⟪e F ξ, e F η⟫_ℂ =
      ∫ x in FugledeCube.cubeUnion F, conj (character ξ x) * character η x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coe_e F ξ, coe_e F η] with x hξ hη
  rw [hξ, hη, RCLike.inner_apply]
  ring

lemma gram_integrable (F : Finset (IPoint d)) (ξ η : RPoint d) :
    IntegrableOn (fun x => conj (character ξ x) * character η x)
      (FugledeCube.cubeUnion F) volume := by
  have hb : IntegrableOn (fun _ : RPoint d => (1 : ℝ)) (FugledeCube.cubeUnion F) volume :=
    integrableOn_const (FugledeCube.volume_cubeUnion_ne_top F)
  apply hb.mono'
  · exact (Complex.continuous_conj.comp (FugledeTarget.continuous_exponentialCharacter ξ)).mul
      (FugledeTarget.continuous_exponentialCharacter η) |>.aestronglyMeasurable
  · exact ae_of_all _ (fun x => by simp [character, FugledeTarget.norm_exponentialCharacter])

/-- Integer cube translations factor the actual union Gram integral. -/
lemma integral_union_gram_factor (F : Finset (IPoint d)) (ξ η : RPoint d) :
    (∫ x in FugledeCube.cubeUnion F, conj (character ξ x) * character η x) =
      (∑ f ∈ F, conj (character ξ (FugledeCube.intVec f)) *
        character η (FugledeCube.intVec f)) *
      (∫ u in FugledeCube.unitCube, conj (character ξ u) * character η u) := by
  classical
  rw [FugledeSlices.integral_union_eq_sum_slices F _ (gram_integrable F ξ η)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f _
  calc
    _ = ∫ u in FugledeCube.unitCube,
        (conj (character ξ (FugledeCube.intVec f)) * character η (FugledeCube.intVec f)) *
          (conj (character ξ u) * character η u) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => by
        dsimp only
        rw [character_add_point, character_add_point, map_mul]
        ring)
    _ = _ := integral_const_mul _ _

lemma lattice_phase_frequency_shift (ξ : RPoint d) (z f : IPoint d) :
    character (ξ + FugledeCube.intVec z) (FugledeCube.intVec f) =
      character ξ (FugledeCube.intVec f) := by
  rw [character_add_frequency, character_integer_integer, mul_one]

/-- With the same real base frequency, the unit-cube Gram is genuinely integer Fourier Gram. -/
lemma unitCube_shifted_gram (ξ : RPoint d) (z w : IPoint d) :
    (∫ u in FugledeCube.unitCube,
      conj (character (ξ + FugledeCube.intVec z) u) *
        character (ξ + FugledeCube.intVec w) u) = if z = w then 1 else 0 := by
  calc
    _ = ∫ u in FugledeCube.unitCube, conj (FugledeFourier.integerCharacter z u) *
        FugledeFourier.integerCharacter w u := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => by
        dsimp only
        rw [character_add_frequency, character_add_frequency, map_mul,
          character_intVec, character_intVec]
        calc
          _ = (conj (character ξ u) * character ξ u) *
              (conj (FugledeFourier.integerCharacter z u) * FugledeFourier.integerCharacter w u) := by
            ring
          _ = _ := by rw [character_conj_mul, one_mul])
    _ = _ := unitCube_integer_gram z w

/-- A true finite exponential Gram matrix lifts to the full union-L2 matrix.
Neither unit-cube orthogonality nor a real-union Gram identity is assumed. -/
theorem e_shifted_gram {σ : Type*} (F : Finset (IPoint d)) (freq : σ → RPoint d)
    (hGram : ∀ i j : σ,
      (∑ f ∈ F, conj (character (freq i) (FugledeCube.intVec f)) *
        character (freq j) (FugledeCube.intVec f)) = if i = j then (F.card : ℂ) else 0)
    (i j : σ) (z w : IPoint d) :
    ⟪e F (freq i + FugledeCube.intVec z), e F (freq j + FugledeCube.intVec w)⟫_ℂ =
      if i = j ∧ z = w then (F.card : ℂ) else 0 := by
  classical
  rw [e_inner_integral, integral_union_gram_factor]
  simp_rw [lattice_phase_frequency_shift]
  rw [hGram]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, unitCube_shifted_gram]
    by_cases hzw : z = w <;> simp [hzw]
  · simp [hij]

theorem e_shifted_inner_eq_zero {σ : Type*} (F : Finset (IPoint d)) (freq : σ → RPoint d)
    (hGram : ∀ i j : σ,
      (∑ f ∈ F, conj (character (freq i) (FugledeCube.intVec f)) *
        character (freq j) (FugledeCube.intVec f)) = if i = j then (F.card : ℂ) else 0)
    (i j : σ) (z w : IPoint d)
    (hne : freq i + FugledeCube.intVec z ≠ freq j + FugledeCube.intVec w) :
    ⟪e F (freq i + FugledeCube.intVec z), e F (freq j + FugledeCube.intVec w)⟫_ℂ = 0 := by
  rw [e_shifted_gram F freq hGram]
  apply ite_eq_right
  rintro ⟨hij, hzw⟩
  exact hne (by rw [hij, hzw])

/-- Nonempty finite Gram data also proves different indices give different real frequencies. -/
theorem frequency_shift_injective {σ : Type*} (F : Finset (IPoint d)) (hF : F.Nonempty)
    (freq : σ → RPoint d)
    (hGram : ∀ i j : σ,
      (∑ f ∈ F, conj (character (freq i) (FugledeCube.intVec f)) *
        character (freq j) (FugledeCube.intVec f)) = if i = j then (F.card : ℂ) else 0) :
    Function.Injective (fun p : σ × IPoint d => freq p.1 + FugledeCube.intVec p.2) := by
  intro a b hab
  by_contra hne
  have hp : ¬ (a.1 = b.1 ∧ a.2 = b.2) := by
    rintro ⟨h1, h2⟩
    exact hne (Prod.ext h1 h2)
  have hoff := e_shifted_gram F freq hGram a.1 b.1 a.2 b.2
  rw [ite_eq_right hp] at hoff
  have hdiag := e_shifted_gram F freq hGram a.1 a.1 a.2 a.2
  simp only [and_self] at hdiag
  change freq a.1 + FugledeCube.intVec a.2 = freq b.1 + FugledeCube.intVec b.2 at hab
  rw [← hab] at hoff
  have hc : (F.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hF).ne'
  exact hc (hdiag.symm.trans hoff)

end
end FugledeOrthogonality
#print axioms FugledeOrthogonality.unitCube_integer_gram
#print axioms FugledeOrthogonality.e_inner_integral
#print axioms FugledeOrthogonality.integral_union_gram_factor
#print axioms FugledeOrthogonality.e_shifted_gram
#print axioms FugledeOrthogonality.e_shifted_inner_eq_zero
#print axioms FugledeOrthogonality.frequency_shift_injective
