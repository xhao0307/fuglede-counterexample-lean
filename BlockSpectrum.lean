import FiniteSpectralSeeds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option debug.skipKernelTC false

/-!
Finite Gram matrices for explicit rectangular block copies and their
expanded frequencies. The input is the original finite Gram matrix;
the expanded Gram matrix is proved, not assumed.
-/

namespace FugledeBlockSpectrum

open scoped BigOperators ComplexConjugate

variable (k : ℕ) [NeZero k]

noncomputable def gridCharacter (s j : ZMod k) : ℂ := ZMod.stdAddChar (s * j)

theorem grid_character_product (s t j : ZMod k) :
    conj (gridCharacter k s j) * gridCharacter k t j =
      ZMod.stdAddChar ((t - s) * j) := by
  unfold gridCharacter
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

theorem grid_character_sum (u : ZMod k) :
    (∑ j : ZMod k, ZMod.stdAddChar (u * j)) = if u = 0 then (k : ℂ) else 0 := by
  classical
  let ψ : AddChar (ZMod k) ℂ := ZMod.stdAddChar.mulShift u
  have hψ : ψ = 0 ↔ u = 0 := by
    constructor
    · intro h
      have heval := congrArg (fun χ : AddChar (ZMod k) ℂ => χ 1) h
      have hvalue : ZMod.stdAddChar u = ZMod.stdAddChar (0 : ZMod k) := by
        simpa [ψ] using heval
      exact ZMod.injective_stdAddChar hvalue
    · intro h
      subst u
      ext j
      simp [ψ]
  have h := AddChar.sum_eq_ite ψ
  have h' : (∑ j : ZMod k, ψ j) = if u = 0 then (k : ℂ) else 0 := by
    simpa only [hψ, ZMod.card] using h
  simpa only [ψ, AddChar.mulShift_apply] using h'

theorem grid_character_gram (s t : ZMod k) :
    (∑ j : ZMod k, conj (gridCharacter k s j) * gridCharacter k t j) =
      if s = t then (k : ℂ) else 0 := by
  simp_rw [grid_character_product]
  simpa only [sub_eq_zero, eq_comm] using grid_character_sum k (t - s)

section Replication

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

noncomputable def replicatedMatrix
    (B : σ → ι → ℂ) (U : ι → (ZMod k × ZMod k) → ℂ)
    (v : σ × (ZMod k × ZMod k)) (p : ι × (ZMod k × ZMod k)) : ℂ :=
  B v.1 p.1 * U p.1 v.2 * gridCharacter k v.2.1 p.2.1 *
    gridCharacter k v.2.2 p.2.2

omit [DecidableEq σ] in
theorem replicated_gram_factor
    (B : σ → ι → ℂ) (U : ι → (ZMod k × ZMod k) → ℂ)
    (v w : σ × (ZMod k × ZMod k)) :
    (∑ p : ι × (ZMod k × ZMod k),
      conj (replicatedMatrix k B U v p) * replicatedMatrix k B U w p) =
    (∑ a : ι, (conj (B v.1 a) * B w.1 a) * (conj (U a v.2) * U a w.2) *
      ((∑ j : ZMod k, conj (gridCharacter k v.2.1 j) * gridCharacter k w.2.1 j) *
       (∑ j : ZMod k, conj (gridCharacter k v.2.2 j) * gridCharacter k w.2.2 j))) := by
  simp only [Fintype.sum_prod_type, replicatedMatrix, map_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem replicated_spectral_gram
    (B : σ → ι → ℂ) (U : ι → (ZMod k × ZMod k) → ℂ)
    (baseGram : ∀ i j : σ,
      (∑ a : ι, conj (B i a) * B j a) =
        if i = j then (Fintype.card ι : ℂ) else 0)
    (unitPhase : ∀ a s, conj (U a s) * U a s = 1)
    (v w : σ × (ZMod k × ZMod k)) :
    (∑ p : ι × (ZMod k × ZMod k),
      conj (replicatedMatrix k B U v p) * replicatedMatrix k B U w p) =
      if v = w then (Fintype.card ι : ℂ) * (k : ℂ) ^ 2 else 0 := by
  classical
  rcases v with ⟨i, s⟩
  rcases w with ⟨j, t⟩
  rw [replicated_gram_factor]
  by_cases hst : s = t
  · subst t
    simp only [grid_character_gram, ite_true]
    simp_rw [unitPhase, mul_one]
    rw [← Finset.sum_mul, baseGram]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      ring
    · simp [hij]
  · have hpq : (i, s) ≠ (j, t) := fun h => hst (congrArg Prod.snd h)
    simp only [hpq, ↓reduceIte]
    by_cases h₁ : s.1 = t.1
    · have h₂ : s.2 ≠ t.2 := fun h => hst (Prod.ext h₁ h)
      simp [grid_character_gram, h₁, h₂]
    · simp [grid_character_gram, h₁]

end Replication

noncomputable def cis (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem cis_add (x y : ℝ) : cis (x + y) = cis x * cis y := by
  unfold cis
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem cis_int (m : ℤ) : cis (m : ℝ) = 1 := by
  unfold cis
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨m, ?_⟩
  push_cast
  ring

theorem conj_cis_mul (x : ℝ) : conj (cis x) * cis x = 1 := by
  unfold cis
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have h : conj (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) +
      2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = 0 := by
    norm_num [map_mul, map_ofNat]
  rw [h, Complex.exp_zero]

theorem gridCharacter_eq_cis (s j : ZMod k) :
    gridCharacter k s j = cis ((s.val : ℝ) * (j.val : ℝ) / k) := by
  have hcast : (((s.val * j.val : ℕ) : ℤ) : ZMod k) = s * j := by
    simp only [Int.cast_natCast, Int.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val]
  unfold gridCharacter
  rw [← hcast, ZMod.stdAddChar_coe]
  unfold cis
  push_cast
  congr 1
  ring

abbrev Point := ℤ × ℤ
abbrev Frequency := ℝ × ℝ

noncomputable def pairCharacter (ξ : Frequency) (a : Point) : ℂ :=
  cis (ξ.1 * (a.1 : ℝ) + ξ.2 * (a.2 : ℝ))

noncomputable def baseCharacter (n₁ n₂ : ℕ) (code a : Point) : ℂ :=
  cis ((code.1 : ℝ) * (a.1 : ℝ) / n₁ + (code.2 : ℝ) * (a.2 : ℝ) / n₂)

noncomputable def blockPhase (n₁ n₂ : ℕ) (a : Point)
    (s : ZMod k × ZMod k) : ℂ :=
  cis ((s.1.val : ℝ) / k * (a.1 : ℝ) / n₁ +
    (s.2.val : ℝ) / k * (a.2 : ℝ) / n₂)

def expandedPoint {ι : Type*} (n₁ n₂ : ℕ) (a : ι → Point)
    (p : ι × (ZMod k × ZMod k)) : Point :=
  a p.1 + ((p.2.1.val : ℤ) * n₁, (p.2.2.val : ℤ) * n₂)

noncomputable def expandedFrequency {σ : Type*} (n₁ n₂ : ℕ) (code : σ → Point)
    (v : σ × (ZMod k × ZMod k)) : Frequency :=
  (((code v.1).1 + (v.2.1.val : ℝ) / k) / n₁,
    ((code v.1).2 + (v.2.2.val : ℝ) / k) / n₂)

/-- The matrix factor is an identity for the actual complex exponentials
at the actual copied integer points and expanded real frequencies. -/
theorem expanded_character_factor
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (code a : Point) (s j : ZMod k × ZMod k) :
    pairCharacter
      (((code.1 : ℝ) + (s.1.val : ℝ) / k) / n₁,
       ((code.2 : ℝ) + (s.2.val : ℝ) / k) / n₂)
      (a + ((j.1.val : ℤ) * n₁, (j.2.val : ℤ) * n₂)) =
    baseCharacter n₁ n₂ code a * blockPhase k n₁ n₂ a s *
      gridCharacter k s.1 j.1 * gridCharacter k s.2 j.2 := by
  let b := (code.1 : ℝ) * (a.1 : ℝ) / n₁ + (code.2 : ℝ) * (a.2 : ℝ) / n₂
  let u := (s.1.val : ℝ) / k * (a.1 : ℝ) / n₁ +
    (s.2.val : ℝ) / k * (a.2 : ℝ) / n₂
  let m : ℤ := code.1 * j.1.val + code.2 * j.2.val
  have hn₁ : (n₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n₁)
  have hn₂ : (n₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n₂)
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hangle :
      (((code.1 : ℝ) + (s.1.val : ℝ) / k) / n₁) *
          ((a.1 + (j.1.val : ℤ) * n₁ : ℤ) : ℝ) +
        (((code.2 : ℝ) + (s.2.val : ℝ) / k) / n₂) *
          ((a.2 + (j.2.val : ℤ) * n₂ : ℤ) : ℝ) =
      b + u + (m : ℝ) + (s.1.val : ℝ) * j.1.val / k +
        (s.2.val : ℝ) * j.2.val / k := by
    dsimp [b, u, m]
    push_cast
    field_simp
    ring
  change cis
    ((((code.1 : ℝ) + (s.1.val : ℝ) / k) / n₁) *
        ((a.1 + (j.1.val : ℤ) * n₁ : ℤ) : ℝ) +
      (((code.2 : ℝ) + (s.2.val : ℝ) / k) / n₂) *
        ((a.2 + (j.2.val : ℤ) * n₂ : ℤ) : ℝ)) = _
  rw [hangle]
  simp only [cis_add, cis_int, mul_one]
  rw [← gridCharacter_eq_cis k s.1 j.1, ← gridCharacter_eq_cis k s.2 j.2]
  rfl

section ActualGram

variable {ι σ : Type*} [Fintype ι] [DecidableEq σ]

/-- A genuine base finite Gram input yields the full expanded-frequency
Gram on the explicit k by k copied points. -/
theorem expanded_spectral_gram
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (a : ι → Point) (code : σ → Point)
    (baseGram : ∀ i j : σ,
      (∑ p : ι, conj (baseCharacter n₁ n₂ (code i) (a p)) *
        baseCharacter n₁ n₂ (code j) (a p)) =
        if i = j then (Fintype.card ι : ℂ) else 0)
    (v w : σ × (ZMod k × ZMod k)) :
    (∑ p : ι × (ZMod k × ZMod k),
      conj (pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p)) *
        pairCharacter (expandedFrequency k n₁ n₂ code w) (expandedPoint k n₁ n₂ a p)) =
      if v = w then (Fintype.card ι : ℂ) * (k : ℂ) ^ 2 else 0 := by
  have hfactor (v : σ × (ZMod k × ZMod k)) (p : ι × (ZMod k × ZMod k)) :
      pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p) =
      replicatedMatrix k (fun i p => baseCharacter n₁ n₂ (code i) (a p))
        (fun p s => blockPhase k n₁ n₂ (a p) s) v p :=
    expanded_character_factor k n₁ n₂ (code v.1) (a p.1) v.2 p.2
  simp_rw [hfactor]
  exact replicated_spectral_gram k _ _ baseGram
    (fun p s => conj_cis_mul _) v w

end ActualGram

section FiniteCompleteness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def blockSynthesis (n₁ n₂ : ℕ) (a code : ι → Point) :
    (ι × (ZMod k × ZMod k) → ℂ) →ₗ[ℂ] (ι × (ZMod k × ZMod k) → ℂ) where
  toFun c p := ∑ v : ι × (ZMod k × ZMod k), c v *
    pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p)
  map_add' c d := by
    funext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring

theorem analysis_block_synthesis
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (a code : ι → Point)
    (baseGram : ∀ i j : ι,
      (∑ p : ι, conj (baseCharacter n₁ n₂ (code i) (a p)) *
        baseCharacter n₁ n₂ (code j) (a p)) =
        if i = j then (Fintype.card ι : ℂ) else 0)
    (c : ι × (ZMod k × ZMod k) → ℂ) (v : ι × (ZMod k × ZMod k)) :
    (∑ p : ι × (ZMod k × ZMod k),
      conj (pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p)) *
        blockSynthesis k n₁ n₂ a code c p) =
      ((Fintype.card ι : ℂ) * (k : ℂ) ^ 2) * c v := by
  change (∑ p : ι × (ZMod k × ZMod k),
    conj (pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p)) *
      ∑ w : ι × (ZMod k × ZMod k), c w *
        pairCharacter (expandedFrequency k n₁ n₂ code w) (expandedPoint k n₁ n₂ a p)) = _
  calc
    _ = ∑ w : ι × (ZMod k × ZMod k), c w *
        ∑ p : ι × (ZMod k × ZMod k),
          conj (pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p)) *
            pairCharacter (expandedFrequency k n₁ n₂ code w) (expandedPoint k n₁ n₂ a p) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      simp_rw [expanded_spectral_gram k n₁ n₂ a code baseGram]
      simp [mul_ite, mul_comm]

theorem blockSynthesis_injective
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (a code : ι → Point)
    (baseGram : ∀ i j : ι,
      (∑ p : ι, conj (baseCharacter n₁ n₂ (code i) (a p)) *
        baseCharacter n₁ n₂ (code j) (a p)) =
        if i = j then (Fintype.card ι : ℂ) else 0) :
    Function.Injective (blockSynthesis k n₁ n₂ a code) := by
  intro c d h
  funext v
  let _ : Nonempty ι := ⟨v.1⟩
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hi := congrArg (fun f : ι × (ZMod k × ZMod k) → ℂ =>
    ∑ p : ι × (ZMod k × ZMod k),
      conj (pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p)) * f p) h
  rw [analysis_block_synthesis k n₁ n₂ a code baseGram,
    analysis_block_synthesis k n₁ n₂ a code baseGram] at hi
  exact mul_left_cancel₀ (mul_ne_zero hcard (pow_ne_zero 2 hk)) hi

theorem blockSynthesis_surjective
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (a code : ι → Point)
    (baseGram : ∀ i j : ι,
      (∑ p : ι, conj (baseCharacter n₁ n₂ (code i) (a p)) *
        baseCharacter n₁ n₂ (code j) (a p)) =
        if i = j then (Fintype.card ι : ℂ) else 0) :
    Function.Surjective (blockSynthesis k n₁ n₂ a code) :=
  LinearMap.surjective_of_injective (blockSynthesis_injective k n₁ n₂ a code baseGram)

/-- Completeness on the copied finite set accompanies the proved Gram
matrix, supplying the finite coefficient expansion used by an L2 bridge. -/
theorem every_expanded_function_expansion
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (a code : ι → Point)
    (baseGram : ∀ i j : ι,
      (∑ p : ι, conj (baseCharacter n₁ n₂ (code i) (a p)) *
        baseCharacter n₁ n₂ (code j) (a p)) =
        if i = j then (Fintype.card ι : ℂ) else 0)
    (f : ι × (ZMod k × ZMod k) → ℂ) :
    ∃ c : ι × (ZMod k × ZMod k) → ℂ, ∀ p,
      f p = ∑ v : ι × (ZMod k × ZMod k), c v *
        pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p) := by
  obtain ⟨c, hc⟩ := blockSynthesis_surjective k n₁ n₂ a code baseGram f
  exact ⟨c, fun p => (congrFun hc p).symm⟩


/-- The proved finite expansion precludes repeated copied integer points. -/
theorem expandedPoint_injective_of_gram
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (a code : ι → Point)
    (baseGram : ∀ i j : ι,
      (∑ p : ι, conj (baseCharacter n₁ n₂ (code i) (a p)) *
        baseCharacter n₁ n₂ (code j) (a p)) =
        if i = j then (Fintype.card ι : ℂ) else 0) :
    Function.Injective (expandedPoint k n₁ n₂ a) := by
  intro p q h
  by_contra hpq
  obtain ⟨c, hc⟩ := every_expanded_function_expansion k n₁ n₂ a code baseGram
    (fun r => if r = p then (1 : ℂ) else 0)
  have hsum :
      (∑ v : ι × (ZMod k × ZMod k), c v *
        pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a p)) =
      (∑ v : ι × (ZMod k × ZMod k), c v *
        pairCharacter (expandedFrequency k n₁ n₂ code v) (expandedPoint k n₁ n₂ a q)) := by
    rw [h]
  have hvalue := (hc p).trans (hsum.trans (hc q).symm)
  simp [Ne.symm hpq] at hvalue

/-- The positive Gram diagonal precludes repeated expanded real frequencies. -/
theorem expandedFrequency_injective_of_gram
    (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂] (a code : ι → Point)
    (baseGram : ∀ i j : ι,
      (∑ p : ι, conj (baseCharacter n₁ n₂ (code i) (a p)) *
        baseCharacter n₁ n₂ (code j) (a p)) =
        if i = j then (Fintype.card ι : ℂ) else 0) :
    Function.Injective (expandedFrequency k n₁ n₂ code) := by
  intro v w h
  by_contra hvw
  let _ : Nonempty ι := ⟨v.1⟩
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hdiag := expanded_spectral_gram k n₁ n₂ a code baseGram v v
  have hoff := expanded_spectral_gram k n₁ n₂ a code baseGram v w
  simp only [ite_true] at hdiag
  have hzero : (Fintype.card ι : ℂ) * (k : ℂ) ^ 2 = 0 := by
    rw [← hdiag]
    simpa only [← h, ite_eq_right hvw] using hoff
  exact (mul_ne_zero hcard (pow_ne_zero 2 hk)) hzero

end FiniteCompleteness


section ConcreteSeed

/-- The integer representative of the actual seed's finite coordinates. -/
def seedLift (a : FugledeSeeds.G) : Point := (a.1.val, a.2.val)

def seedPoint (i : FugledeSeeds.FrequencyIndex) : Point :=
  seedLift (FugledeSeeds.aPoint i.swap)

def seedCode (i : FugledeSeeds.FrequencyIndex) : Point :=
  seedLift (FugledeSeeds.spectrumPoint i)

theorem baseCharacter_seedLift (ξ a : FugledeSeeds.G) :
    baseCharacter 60 12 (seedLift ξ) (seedLift a) =
      FugledeSeeds.character ξ a := by
  simp [baseCharacter, cis, seedLift, FugledeSeeds.character]

/-- This base Gram input is the proved 60-point seed Gram, not an assumption. -/
theorem seed_base_gram (i j : FugledeSeeds.FrequencyIndex) :
    (∑ p : FugledeSeeds.FrequencyIndex,
      conj (baseCharacter 60 12 (seedCode i) (seedPoint p)) *
        baseCharacter 60 12 (seedCode j) (seedPoint p)) =
      if i = j then (Fintype.card FugledeSeeds.FrequencyIndex : ℂ) else 0 := by
  simp only [seedCode, seedPoint, baseCharacter_seedLift]
  have h := FugledeSeeds.actual_character_gram i j
  simp only [Fintype.sum_prod_type] at h ⊢
  rw [Finset.sum_comm]
  convert h using 1 <;> norm_num [FugledeSeeds.FrequencyIndex, Fintype.card_prod]

def seedBlockPoint (p : FugledeSeeds.FrequencyIndex × (ZMod k × ZMod k)) : Point :=
  expandedPoint k 60 12 seedPoint p

noncomputable def seedBlockFrequency
    (v : FugledeSeeds.FrequencyIndex × (ZMod k × ZMod k)) : Frequency :=
  expandedFrequency k 60 12 seedCode v

theorem seed_expanded_gram
    (v w : FugledeSeeds.FrequencyIndex × (ZMod k × ZMod k)) :
    (∑ p : FugledeSeeds.FrequencyIndex × (ZMod k × ZMod k),
      conj (pairCharacter (seedBlockFrequency k v) (seedBlockPoint k p)) *
        pairCharacter (seedBlockFrequency k w) (seedBlockPoint k p)) =
      if v = w then (60 : ℂ) * (k : ℂ) ^ 2 else 0 := by
  have h := expanded_spectral_gram k 60 12 seedPoint seedCode seed_base_gram v w
  norm_num [FugledeSeeds.FrequencyIndex, Fintype.card_prod] at h
  exact h

theorem seed_every_expanded_function
    (f : FugledeSeeds.FrequencyIndex × (ZMod k × ZMod k) → ℂ) :
    ∃ c : FugledeSeeds.FrequencyIndex × (ZMod k × ZMod k) → ℂ, ∀ p,
      f p = ∑ v : FugledeSeeds.FrequencyIndex × (ZMod k × ZMod k), c v *
        pairCharacter (seedBlockFrequency k v) (seedBlockPoint k p) :=
  every_expanded_function_expansion k 60 12 seedPoint seedCode seed_base_gram f


theorem seedBlockPoint_injective : Function.Injective (seedBlockPoint k) :=
  expandedPoint_injective_of_gram k 60 12 seedPoint seedCode seed_base_gram

theorem seedBlockFrequency_injective : Function.Injective (seedBlockFrequency k) :=
  expandedFrequency_injective_of_gram k 60 12 seedPoint seedCode seed_base_gram

/-- The 97 by 97 block has 564540 orthogonal indexed exponentials. -/
theorem seed97_gram
    (v w : FugledeSeeds.FrequencyIndex × (ZMod 97 × ZMod 97)) :
    (∑ p : FugledeSeeds.FrequencyIndex × (ZMod 97 × ZMod 97),
      conj (pairCharacter (seedBlockFrequency 97 v) (seedBlockPoint 97 p)) *
        pairCharacter (seedBlockFrequency 97 w) (seedBlockPoint 97 p)) =
      if v = w then (564540 : ℂ) else 0 := by
  have h := seed_expanded_gram 97 v w
  norm_num at h
  exact h

theorem seed97_every_function
    (f : FugledeSeeds.FrequencyIndex × (ZMod 97 × ZMod 97) → ℂ) :
    ∃ c : FugledeSeeds.FrequencyIndex × (ZMod 97 × ZMod 97) → ℂ, ∀ p,
      f p = ∑ v : FugledeSeeds.FrequencyIndex × (ZMod 97 × ZMod 97), c v *
        pairCharacter (seedBlockFrequency 97 v) (seedBlockPoint 97 p) :=
  seed_every_expanded_function 97 f

end ConcreteSeed

end FugledeBlockSpectrum

#print axioms FugledeBlockSpectrum.grid_character_product
#print axioms FugledeBlockSpectrum.grid_character_sum
#print axioms FugledeBlockSpectrum.grid_character_gram
#print axioms FugledeBlockSpectrum.replicated_gram_factor
#print axioms FugledeBlockSpectrum.replicated_spectral_gram
#print axioms FugledeBlockSpectrum.cis_add
#print axioms FugledeBlockSpectrum.cis_int
#print axioms FugledeBlockSpectrum.conj_cis_mul
#print axioms FugledeBlockSpectrum.gridCharacter_eq_cis
#print axioms FugledeBlockSpectrum.expanded_character_factor
#print axioms FugledeBlockSpectrum.expanded_spectral_gram
#print axioms FugledeBlockSpectrum.analysis_block_synthesis
#print axioms FugledeBlockSpectrum.blockSynthesis_injective
#print axioms FugledeBlockSpectrum.blockSynthesis_surjective
#print axioms FugledeBlockSpectrum.every_expanded_function_expansion
#print axioms FugledeBlockSpectrum.expandedPoint_injective_of_gram
#print axioms FugledeBlockSpectrum.expandedFrequency_injective_of_gram
#print axioms FugledeBlockSpectrum.baseCharacter_seedLift
#print axioms FugledeBlockSpectrum.seed_base_gram
#print axioms FugledeBlockSpectrum.seed_expanded_gram
#print axioms FugledeBlockSpectrum.seed_every_expanded_function
#print axioms FugledeBlockSpectrum.seedBlockPoint_injective
#print axioms FugledeBlockSpectrum.seedBlockFrequency_injective
#print axioms FugledeBlockSpectrum.seed97_gram
#print axioms FugledeBlockSpectrum.seed97_every_function
