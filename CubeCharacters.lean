import SpectralSlices
import FourierCube

/-! Algebra of the actual canonical Euclidean exponential characters.
Integer-frequency periodicity and the coefficient/slice identity are proved,
not assumed, for the same half-open cube-union L2 spaces. -/
set_option Elab.async false
set_option debug.skipKernelTC false
namespace FugledeCharacters
open Set MeasureTheory
open scoped BigOperators ComplexConjugate
variable {d : ℕ}
abbrev RPoint (d : ℕ) := Fin d → ℝ
abbrev IPoint (d : ℕ) := Fin d → ℤ
noncomputable abbrev character := @FugledeTarget.exponentialCharacter d

lemma intVec_add (z w : IPoint d) :
    FugledeCube.intVec (z + w) = FugledeCube.intVec z + FugledeCube.intVec w := by
  ext i
  simp [FugledeCube.intVec]

lemma intVec_sub (z w : IPoint d) :
    FugledeCube.intVec (z - w) = FugledeCube.intVec z - FugledeCube.intVec w := by
  ext i
  simp [FugledeCube.intVec]

theorem character_add_frequency (ξ η x : RPoint d) :
    character (ξ + η) x = character ξ x * character η x := by
  unfold character FugledeTarget.exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.ofReal_add]
  ring

theorem character_add_point (ξ x y : RPoint d) :
    character ξ (x + y) = character ξ x * character ξ y := by
  unfold character FugledeTarget.exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add]

lemma character_zero_frequency (x : RPoint d) : character 0 x = 1 := by
  simp [character, FugledeTarget.exponentialCharacter]

lemma character_zero_point (ξ : RPoint d) : character ξ 0 = 1 := by
  simp [character, FugledeTarget.exponentialCharacter]

theorem character_ne_zero (ξ x : RPoint d) : character ξ x ≠ 0 :=
  Complex.exp_ne_zero _

theorem character_mul_conj (ξ x : RPoint d) :
    character ξ x * conj (character ξ x) = 1 := by
  rw [Complex.mul_conj']
  simp [character, FugledeTarget.norm_exponentialCharacter]

theorem character_conj_mul (ξ x : RPoint d) :
    conj (character ξ x) * character ξ x = 1 := by
  rw [mul_comm, character_mul_conj]

theorem character_neg_frequency (ξ x : RPoint d) :
    character (-ξ) x = conj (character ξ x) := by
  apply mul_right_cancel₀ (character_ne_zero ξ x)
  rw [← character_add_frequency, neg_add_cancel, character_zero_frequency,
    character_conj_mul]

theorem character_conj_product (ξ η x : RPoint d) :
    conj (character ξ x) * character η x = character (η - ξ) x := by
  rw [← character_neg_frequency, ← character_add_frequency]
  simp only [sub_eq_add_neg, add_comm]

/-- Every integer scalar dot product gives a full turn of the actual exponential. -/
theorem character_integer_integer (z f : IPoint d) :
    character (FugledeCube.intVec z) (FugledeCube.intVec f) = 1 := by
  have hs : (∑ i, (z i : ℝ) * (f i : ℝ)) = ((∑ i, z i * f i : ℤ) : ℝ) := by
    push_cast
    rfl
  unfold character FugledeTarget.exponentialCharacter
  simp only [FugledeCube.intVec]
  rw [hs]
  have he : 2 * Real.pi * Complex.I * (((∑ i, z i * f i : ℤ) : ℝ) : ℂ) =
      (∑ i, z i * f i : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I _

theorem character_intVec (z : IPoint d) (u : RPoint d) :
    character (FugledeCube.intVec z) u = FugledeFourier.integerCharacter z u := rfl

theorem character_integer_periodic (z f : IPoint d) (u : RPoint d) :
    character (FugledeCube.intVec z) (FugledeCube.intVec f + u) =
      FugledeFourier.integerCharacter z u := by
  rw [character_add_point, character_integer_integer, one_mul, character_intVec]

/-- Simultaneous integer frequency shift and integer cube-origin translation. -/
theorem character_frequency_shift (ξ : RPoint d) (z f : IPoint d) (u : RPoint d) :
    character (ξ + FugledeCube.intVec z) (FugledeCube.intVec f + u) =
      character ξ (FugledeCube.intVec f + u) * FugledeFourier.integerCharacter z u := by
  rw [character_add_frequency, character_integer_periodic]

/-- The actual finite slice sum has the expected integer Fourier multiplier. -/
theorem weightedSlices_frequency_shift (F : Finset (IPoint d)) (ξ : RPoint d)
    (z : IPoint d) (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F)))
    (u : RPoint d) :
    FugledeSlices.weightedSlices F (ξ + FugledeCube.intVec z) g u =
      conj (FugledeFourier.integerCharacter z u) * FugledeSlices.weightedSlices F ξ g u := by
  classical
  unfold FugledeSlices.weightedSlices
  simp_rw [FugledeSlices.weightedSlice, FugledeSlices.phase, FugledeSlices.slice,
    character_frequency_shift, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

/-- The true shifted character coefficient equals the unit-cube Fourier coefficient.
All integrability is discharged by SpectralSlices from the genuine L2 input. -/
theorem coefficient_eq_weightedSlices_fourier (F : Finset (IPoint d)) (ξ : RPoint d)
    (z : IPoint d) (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    (∫ x in FugledeCube.cubeUnion F,
      conj (character (ξ + FugledeCube.intVec z) x) * g x) =
      ∫ u in FugledeCube.unitCube,
        conj (FugledeFourier.integerCharacter z u) * FugledeSlices.weightedSlices F ξ g u := by
  rw [FugledeSlices.integral_character_weight_eq_integral_weightedSlices]
  apply integral_congr_ae
  exact ae_of_all _ (weightedSlices_frequency_shift F ξ z g)

#print axioms character_add_frequency
#print axioms character_add_point
#print axioms character_integer_integer
#print axioms character_frequency_shift
#print axioms character_conj_product
#print axioms weightedSlices_frequency_shift
#print axioms coefficient_eq_weightedSlices_fourier
end FugledeCharacters
