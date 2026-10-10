import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Alternative finite spectral proof via the three twelve-point seeds.
The character normalization follows the local FiniteSpectral source, whose
large certificate compile is independent of this file. -/
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace FugledeSeeds
open scoped BigOperators ComplexConjugate
open Complex
abbrev H := Fin 12 × Fin 12
abbrev G := Fin 60 × Fin 12

def f : Fin 12 → Fin 12 := ![0, 5, 0, 7, 9, 2, 10, 4, 7, 8, 10, 10]
def ePoint (y : Fin 12) : H := (f y, y)
def dot (e a : H) : Fin 12 := e.1 * a.1 + e.2 * a.2
noncomputable def zeta12 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)
lemma zeta12_primitive : IsPrimitiveRoot zeta12 12 :=
  Complex.isPrimitiveRoot_exp 12 (by decide)

noncomputable def powChar {n : ℕ} (ζ : ℂ) (a : Fin n) : ℂ := ζ ^ a.val
lemma pow_mod {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (a : ℕ) :
    ζ ^ (a % n) = ζ ^ a := by
  rw [h.eq_orderOf]
  exact pow_mod_orderOf ζ a
lemma powChar_add {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (a b : Fin n) :
    powChar ζ (a + b) = powChar ζ a * powChar ζ b := by
  unfold powChar
  rw [Fin.val_add, pow_mod h, pow_add]
lemma powChar_mul {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (a b : Fin n) :
    powChar ζ (a * b) = (ζ ^ a.val) ^ b.val := by
  unfold powChar
  rw [Fin.val_mul, pow_mod h, pow_mul]
lemma sum_powers_zero {ζ : ℂ} {n : ℕ} (hn : ζ ^ n = 1) (hne : ζ ≠ 1) :
    (∑ k : Fin n, ζ ^ k.val) = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hh := geom_sum_mul ζ n
  rw [hn, sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hne)
lemma sum_powChar_mul_zero {n : ℕ} [NeZero n] {ζ : ℂ} (h : IsPrimitiveRoot ζ n)
    (a : Fin n) (ha : a ≠ 0) :
    (∑ k : Fin n, powChar ζ (a * k)) = 0 := by
  simp_rw [powChar_mul h]
  apply sum_powers_zero
  · rw [← pow_mul, Nat.mul_comm, pow_mul, h.pow_eq_one, one_pow]
  · apply h.pow_ne_one_of_pos_of_lt
    · intro hval
      apply ha
      exact Fin.ext (by simpa using hval)
    · exact a.is_lt

def v0 (k : Fin 12) : H := (0, k)
def v1 (k : Fin 12) : H := (k, k)
def lift6 (k : Fin 6) : Fin 12 := ⟨k.val, by omega⟩
def lift2 (δ : Fin 2) : Fin 12 := ⟨δ.val, by omega⟩
def v2 (p : Fin 6 × Fin 2) : H :=
  (4 * lift6 p.1 + lift2 p.2, 2 * lift6 p.1 + 2 * lift2 p.2)
def diagonalFrequency (y : Fin 12) : Fin 12 := f y + y
lemma diagonalFrequency_injective : Function.Injective diagonalFrequency := by decide +kernel
lemma v0_dot (i j k : Fin 12) :
    dot (ePoint j - ePoint i) (v0 k) = (j - i) * k := by
  simp [dot, ePoint, v0]
lemma v1_dot : ∀ i j k : Fin 12,
    dot (ePoint j - ePoint i) (v1 k) =
      (diagonalFrequency j - diagonalFrequency i) * k := by decide +kernel
lemma v0_sum_zero (i j : Fin 12) (hij : i ≠ j) :
    (∑ k : Fin 12, powChar zeta12 (dot (ePoint j - ePoint i) (v0 k))) = 0 := by
  simp_rw [v0_dot]
  apply sum_powChar_mul_zero zeta12_primitive
  exact sub_ne_zero.mpr (Ne.symm hij)
lemma v1_sum_zero (i j : Fin 12) (hij : i ≠ j) :
    (∑ k : Fin 12, powChar zeta12 (dot (ePoint j - ePoint i) (v1 k))) = 0 := by
  simp_rw [v1_dot]
  apply sum_powChar_mul_zero zeta12_primitive
  exact sub_ne_zero.mpr (fun h => hij (diagonalFrequency_injective h).symm)

def r (y : Fin 12) : Fin 6 :=
  ⟨(2 * (f y).val + y.val) % 6, Nat.mod_lt _ (by decide)⟩
def s (y : Fin 12) : Fin 12 := f y + 2 * y
lemma v2_dot : ∀ i j : Fin 12, ∀ p : Fin 6 × Fin 2,
    dot (ePoint j - ePoint i) (v2 p) =
      (2 * lift6 (r j - r i)) * lift6 p.1 + (s j - s i) * lift2 p.2 := by
  decide +kernel
lemma r_collision : ∀ i j : Fin 12, i ≠ j → r i = r j → s j - s i = 6 := by
  decide +kernel
lemma zeta6_primitive : IsPrimitiveRoot (zeta12 ^ 2) 6 := by
  simpa using zeta12_primitive.pow_of_dvd (p := 2) (by decide) (by decide)
lemma powChar_v2 (i j : Fin 12) (p : Fin 6 × Fin 2) :
    powChar zeta12 (dot (ePoint j - ePoint i) (v2 p)) =
      ((zeta12 ^ 2) ^ (r j - r i).val) ^ p.1.val *
        (zeta12 ^ (s j - s i).val) ^ p.2.val := by
  rw [v2_dot, powChar_add zeta12_primitive, powChar_mul zeta12_primitive,
    powChar_mul zeta12_primitive]
  simp only [lift6, lift2, Fin.val_mk]
  rw [Fin.val_mul, pow_mod zeta12_primitive]
  change (zeta12 ^ (2 * (r j - r i).val)) ^ p.1.val *
      (zeta12 ^ (s j - s i).val) ^ p.2.val = _
  rw [pow_mul]
lemma v2_sum_zero (i j : Fin 12) (hij : i ≠ j) :
    (∑ p : Fin 6 × Fin 2, powChar zeta12 (dot (ePoint j - ePoint i) (v2 p))) = 0 := by
  simp_rw [powChar_v2]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  by_cases hr : r i = r j
  · have hs := r_collision i j hij hr
    rw [hs]
    have hneg : zeta12 ^ 6 = -1 := by
      have hprim : IsPrimitiveRoot (zeta12 ^ 6) 2 := by
        simpa using zeta12_primitive.pow_of_dvd (p := 6) (by decide) (by decide)
      exact hprim.eq_neg_one_of_two_right
    norm_num [hneg, Fin.sum_univ_succ]
  · have hn : r j - r i ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
    have hz := sum_powChar_mul_zero zeta6_primitive (r j - r i) hn
    simp_rw [powChar_mul zeta6_primitive] at hz
    rw [hz, zero_mul]

def v2Index (p : Fin 6 × Fin 2) : Fin 12 := ⟨6 * p.2.val + p.1.val, by omega⟩
lemma v2Index_bijective : Function.Bijective v2Index := by decide +kernel
def v2ByIndex (k : Fin 12) : H :=
  v2 (⟨k.val % 6, Nat.mod_lt _ (by decide)⟩, ⟨k.val / 6, by omega⟩)
lemma v2ByIndex_reindex : ∀ p : Fin 6 × Fin 2, v2ByIndex (v2Index p) = v2 p := by
  decide +kernel
lemma v2ByIndex_sum_zero (i j : Fin 12) (hij : i ≠ j) :
    (∑ k : Fin 12, powChar zeta12 (dot (ePoint j - ePoint i) (v2ByIndex k))) = 0 := by
  rw [← v2Index_bijective.sum_comp]
  simp_rw [v2ByIndex_reindex]
  exact v2_sum_zero i j hij

def seedPoint (j : Fin 3) (k : Fin 12) : H :=
  if j = 0 then v0 k else if j = 1 then v1 k else v2ByIndex k
lemma seed_sum_zero (j : Fin 3) (i i' : Fin 12) (hii : i ≠ i') :
    (∑ k : Fin 12, powChar zeta12 (dot (ePoint i' - ePoint i) (seedPoint j k))) = 0 := by
  fin_cases j
  · simpa [seedPoint] using v0_sum_zero i i' hii
  · simpa [seedPoint] using v1_sum_zero i i' hii
  · simpa [seedPoint] using v2ByIndex_sum_zero i i' hii

def layerSeed (l : Fin 5) : Fin 3 := if l = 3 then 2 else if l = 4 then 1 else 0
noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
lemma zeta5_primitive : IsPrimitiveRoot zeta5 5 :=
  Complex.isPrimitiveRoot_exp 5 (by decide)
abbrev FrequencyIndex := Fin 12 × Fin 5
abbrev PointIndex := Fin 5 × Fin 12
noncomputable def productCharacter (ξ : FrequencyIndex) (a : PointIndex) : ℂ :=
  powChar zeta12 (dot (ePoint ξ.1) (seedPoint (layerSeed a.1) a.2)) *
    powChar zeta5 (ξ.2 * a.1)
lemma powChar_ne_zero {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0)
    (a : Fin n) : powChar ζ a ≠ 0 := pow_ne_zero _ (h.ne_zero hn)
lemma powChar_mul_conj {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0)
    (a : Fin n) : powChar ζ a * conj (powChar ζ a) = 1 := by
  rw [Complex.mul_conj']
  simp only [powChar, norm_pow, h.norm'_eq_one hn, one_pow, Complex.ofReal_one]
lemma powChar_sub {n : ℕ} [NeZero n] {ζ : ℂ} (h : IsPrimitiveRoot ζ n)
    (a b : Fin n) : powChar ζ (a - b) = conj (powChar ζ b) * powChar ζ a := by
  apply mul_right_cancel₀ (powChar_ne_zero h (NeZero.ne n) b)
  rw [← powChar_add h, sub_add_cancel]
  symm
  calc
    _ = powChar ζ a * (powChar ζ b * conj (powChar ζ b)) := by ring
    _ = _ := by rw [powChar_mul_conj h (NeZero.ne n), mul_one]
lemma product_dot_difference : ∀ i j : Fin 12, ∀ a : PointIndex,
    dot (ePoint j - ePoint i) (seedPoint (layerSeed a.1) a.2) =
      dot (ePoint j) (seedPoint (layerSeed a.1) a.2) -
        dot (ePoint i) (seedPoint (layerSeed a.1) a.2) := by decide +kernel
lemma layer_dot_difference : ∀ i j a : Fin 5, (j - i) * a = j * a - i * a := by
  decide +kernel
lemma productCharacter_difference (i j : FrequencyIndex) (a : PointIndex) :
    conj (productCharacter i a) * productCharacter j a =
      powChar zeta12 (dot (ePoint j.1 - ePoint i.1) (seedPoint (layerSeed a.1) a.2)) *
        powChar zeta5 ((j.2 - i.2) * a.1) := by
  rw [product_dot_difference, layer_dot_difference,
    powChar_sub zeta12_primitive, powChar_sub zeta5_primitive]
  unfold productCharacter
  rw [map_mul]
  ring
lemma productCharacter_self (i : FrequencyIndex) (a : PointIndex) :
    conj (productCharacter i a) * productCharacter i a = 1 := by
  rw [productCharacter_difference]
  simp [dot, ePoint, powChar]

theorem product_character_gram (i j : FrequencyIndex) :
    (∑ a : PointIndex, conj (productCharacter i a) * productCharacter j a) =
      if i = j then 60 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    simp_rw [productCharacter_self]
    norm_num
  · rw [ite_eq_right hij]
    simp_rw [productCharacter_difference]
    rw [Fintype.sum_prod_type]
    by_cases hy : i.1 = j.1
    · rw [hy]
      simp [dot, powChar]
      have hr : i.2 ≠ j.2 := by
        intro hr
        exact hij (Prod.ext hy hr)
      have hz := sum_powChar_mul_zero zeta5_primitive (j.2 - i.2)
        (sub_ne_zero.mpr (Ne.symm hr))
      simp only [powChar] at hz
      rw [← Finset.mul_sum, hz, mul_zero]
    · simp_rw [← Finset.sum_mul]
      simp_rw [seed_sum_zero _ _ _ hy, zero_mul]
      simp

def lift12 (k : Fin 12) : Fin 60 := ⟨k.val, by omega⟩
def lift5 (k : Fin 5) : Fin 60 := ⟨k.val, by omega⟩
def crt (h : H) (l : Fin 5) : G := (25 * lift12 h.1 + 36 * lift5 l, h.2)
def aPoint (a : PointIndex) : G := crt (seedPoint (layerSeed a.1) a.2) a.1
def spectrumPoint (ξ : FrequencyIndex) : G := (5 * lift12 (f ξ.1) + 12 * lift5 ξ.2, ξ.1)
def Aplus : Finset G := Finset.univ.image aPoint
def Lplus : Finset G := Finset.univ.image spectrumPoint
lemma aPoint_injective : Function.Injective aPoint := by decide +kernel
lemma spectrumPoint_injective : Function.Injective spectrumPoint := by decide +kernel
lemma card_Aplus : Aplus.card = 60 := by
  rw [Aplus, Finset.card_image_of_injective _ aPoint_injective]
  simp
lemma card_Lplus : Lplus.card = 60 := by
  rw [Lplus, Finset.card_image_of_injective _ spectrumPoint_injective]
  simp
noncomputable def zeta60 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 60)
lemma zeta60_primitive : IsPrimitiveRoot zeta60 60 :=
  Complex.isPrimitiveRoot_exp 60 (by decide)
lemma zeta60_pow (n : ℕ) :
    zeta60 ^ n = Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) / 60)) := by
  unfold zeta60
  rw [← Complex.exp_nat_mul]
  congr 1
  ring
lemma zeta60_pow5 : zeta60 ^ 5 = zeta12 := by
  rw [zeta60_pow]
  unfold zeta12
  congr 1
  ring
lemma zeta60_pow12 : zeta60 ^ 12 = zeta5 := by
  rw [zeta60_pow]
  unfold zeta5
  congr 1
  ring

def rawDot (ξ a : G) : ℕ := ξ.1.val * a.1.val + 5 * ξ.2.val * a.2.val
noncomputable def character (ξ a : G) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I *
    (((ξ.1.val : ℝ) * (a.1.val : ℝ) / 60 +
      (ξ.2.val : ℝ) * (a.2.val : ℝ) / 12) : ℝ))
lemma character_eq_power (ξ a : G) : character ξ a = zeta60 ^ rawDot ξ a := by
  rw [zeta60_pow]
  unfold character rawDot
  congr 1
  push_cast
  ring
lemma crt_dual_identity : ∀ ξ : FrequencyIndex, ∀ a : PointIndex,
    rawDot (spectrumPoint ξ) (aPoint a) % 60 =
      (5 * (dot (ePoint ξ.1) (seedPoint (layerSeed a.1) a.2)).val +
        12 * (ξ.2 * a.1).val) % 60 := by decide +kernel
lemma character_eq_productCharacter (ξ : FrequencyIndex) (a : PointIndex) :
    character (spectrumPoint ξ) (aPoint a) = productCharacter ξ a := by
  rw [character_eq_power, ← pow_mod zeta60_primitive (rawDot _ _), crt_dual_identity,
    pow_mod zeta60_primitive, pow_add, pow_mul, pow_mul, zeta60_pow5, zeta60_pow12]
  rfl

theorem actual_character_gram (i j : FrequencyIndex) :
    (∑ a : PointIndex, conj (character (spectrumPoint i) (aPoint a)) *
      character (spectrumPoint j) (aPoint a)) = if i = j then 60 else 0 := by
  simp_rw [character_eq_productCharacter]
  exact product_character_gram i j

theorem finiteSpectralOrthogonal {ξ η : G} (hξ : ξ ∈ Lplus) (hη : η ∈ Lplus)
    (hne : ξ ≠ η) :
    (∑ a ∈ Aplus, conj (character ξ a) * character η a) = 0 := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hξ
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hη
  have hij : i ≠ j := fun h => hne (congrArg spectrumPoint h)
  have hg := actual_character_gram i j
  rw [ite_eq_right hij] at hg
  rw [Aplus, Finset.sum_image]
  · exact hg
  · intro i _ j _ h
    exact aPoint_injective h

theorem Aplus_Lplus_finite_spectral_pair :
    Aplus.card = Lplus.card ∧
      ∀ ξ ∈ Lplus, ∀ η ∈ Lplus, ξ ≠ η →
        (∑ a ∈ Aplus, conj (character ξ a) * character η a) = 0 := by
  constructor
  · rw [card_Aplus, card_Lplus]
  · intro ξ hξ η hη hne
    exact finiteSpectralOrthogonal hξ hη hne

/-- Use coordinate swap only to put the synthesis map on one vector space. -/
noncomputable def synthesis : (FrequencyIndex → ℂ) →ₗ[ℂ] (FrequencyIndex → ℂ) where
  toFun c a := ∑ i : FrequencyIndex, c i * character (spectrumPoint i) (aPoint a.swap)
  map_add' c d := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem analysis_synthesis (c : FrequencyIndex → ℂ) (i : FrequencyIndex) :
    (∑ a : PointIndex, conj (character (spectrumPoint i) (aPoint a)) * synthesis c a.swap) =
      (60 : ℂ) * c i := by
  change (∑ a : PointIndex, conj (character (spectrumPoint i) (aPoint a)) *
      ∑ j : FrequencyIndex, c j * character (spectrumPoint j) (aPoint a)) = _
  calc
    _ = ∑ j : FrequencyIndex, c j *
        ∑ a : PointIndex, conj (character (spectrumPoint i) (aPoint a)) *
          character (spectrumPoint j) (aPoint a) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by simp_rw [actual_character_gram]; simp [mul_ite, mul_comm]

theorem synthesis_injective : Function.Injective synthesis := by
  intro c d h
  funext i
  have hi := congrArg (fun v : FrequencyIndex → ℂ =>
    ∑ a : PointIndex, conj (character (spectrumPoint i) (aPoint a)) * v a.swap) h
  rw [analysis_synthesis, analysis_synthesis] at hi
  exact mul_left_cancel₀ (by norm_num : (60 : ℂ) ≠ 0) hi

theorem synthesis_surjective : Function.Surjective synthesis :=
  LinearMap.surjective_of_injective synthesis_injective

theorem every_function_expansion (v : PointIndex → ℂ) :
    ∃ c : FrequencyIndex → ℂ, ∀ a : PointIndex,
      v a = ∑ i : FrequencyIndex, c i * character (spectrumPoint i) (aPoint a) := by
  obtain ⟨c, hc⟩ := synthesis_surjective (fun a => v a.swap)
  refine ⟨c, fun a => ?_⟩
  exact (congrFun hc a.swap).symm

#print axioms product_character_gram
#print axioms actual_character_gram
#print axioms Aplus_Lplus_finite_spectral_pair
#print axioms every_function_expansion
end FugledeSeeds
