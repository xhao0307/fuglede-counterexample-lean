import SpectralSlices
import FourierCube
import CubeCharacters
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Complete exponential systems on actual finite unions of integer cubes.
The finite expansion input is supplied by ConcreteSpectrum for the actual
97-block witness. The continuous completeness is proved in this module. -/
set_option Elab.async false
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
namespace FugledeSpectralBridge
open MeasureTheory Set
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section

variable {d : ℕ}
abbrev UnionL2 (F : Finset (Fin d → ℤ)) :=
  Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))

def e (F : Finset (Fin d → ℤ)) (ξ : Fin d → ℝ) : UnionL2 F :=
  (FugledeTarget.exponentialCharacter_memLp
    (FugledeCube.volume_cubeUnion_ne_top F) ξ).toLp
      (FugledeTarget.exponentialCharacter ξ)

theorem inner_e_eq_integral (F : Finset (Fin d → ℤ)) (ξ : Fin d → ℝ)
    (g : UnionL2 F) :
    ⟪e F ξ, g⟫_ℂ = ∫ x in FugledeCube.cubeUnion F,
      conj (FugledeTarget.exponentialCharacter ξ x) * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(FugledeTarget.exponentialCharacter_memLp
    (FugledeCube.volume_cubeUnion_ne_top F) ξ).coeFn_toLp] with x hx
  change ⟪e F ξ x, g x⟫_ℂ = _
  rw [show e F ξ x = FugledeTarget.exponentialCharacter ξ x from hx]
  simp [mul_comm]

/-- A genuine spanning finite character matrix detects every finite vector. -/
theorem finite_coefficients_detect_zero {α σ : Type*} [Fintype α] [Fintype σ]
    (B : σ → α → ℂ)
    (hExpansion : ∀ w : α → ℂ, ∃ c : σ → ℂ, ∀ a, w a = ∑ i, c i * B i a)
    (v : α → ℂ) (hzero : ∀ i, (∑ a, conj (B i a) * v a) = 0) :
    ∀ a, v a = 0 := by
  classical
  intro a
  obtain ⟨c, hc⟩ := hExpansion (fun p => if p = a then 1 else 0)
  calc
    v a = ∑ p : α, conj (if p = a then (1 : ℂ) else 0) * v p := by simp
    _ = ∑ p : α, conj (∑ i : σ, c i * B i p) * v p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [hc]
    _ = ∑ i : σ, conj (c i) * ∑ p : α, conj (B i p) * v p := by
      simp_rw [map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by simp_rw [hzero]; simp

/-- Zero on each actual translated cube is zero in the union L2 space. -/
theorem eq_zero_of_slices_ae_zero (F : Finset (Fin d → ℤ)) (g : UnionL2 F)
    (hzero : ∀ f ∈ F, FugledeSlices.slice F f g =ᵐ[volume.restrict FugledeCube.unitCube] 0) :
    g = 0 := by
  classical
  let gFun : (Fin d → ℝ) → ℂ := g
  have hg : (g : (Fin d → ℝ) → ℂ) =ᵐ[volume.restrict (FugledeCube.cubeUnion F)] 0 := by
    change gFun =ᵐ[volume.restrict (FugledeCube.cubeUnion F)] 0
    rw [FugledeCube.cubeUnion_eq_iUnion]
    apply (ae_eq_restrict_biUnion_finset_iff FugledeCube.cubeAt F _ _).mpr
    intro f hf
    have hp : ∀ᵐ u ∂volume.restrict FugledeCube.unitCube,
        g (FugledeCube.intVec f + u) = 0 := hzero f hf
    have hmap := ((Homeomorph.addLeft (FugledeCube.intVec f)).measurableEmbedding.ae_map_iff
      (p := fun x : Fin d → ℝ => gFun x = 0)
      (μ := volume.restrict FugledeCube.unitCube)).mpr hp
    change ∀ᵐ x ∂Measure.map (fun u : Fin d → ℝ => FugledeCube.intVec f + u)
      (volume.restrict FugledeCube.unitCube), gFun x = 0 at hmap
    rw [(FugledeSlices.cube_translation_preserving f).map_eq] at hmap
    exact hmap
  apply Lp.ext
  exact hg.trans (Lp.coeFn_zero ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))).symm

theorem weightedSlices_factor (F : Finset (Fin d → ℤ)) (ξ : Fin d → ℝ)
    (g : UnionL2 F) (u : Fin d → ℝ) :
    FugledeSlices.weightedSlices F ξ g u =
      conj (FugledeTarget.exponentialCharacter ξ u) *
        ∑ f ∈ F, conj (FugledeTarget.exponentialCharacter ξ (FugledeCube.intVec f)) *
          FugledeSlices.slice F f g u := by
  classical
  unfold FugledeSlices.weightedSlices
  simp_rw [FugledeSlices.weightedSlice, FugledeSlices.phase,
    FugledeCharacters.character_add_point, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

/-- Vanishing actual weighted slice sums annihilate every finite slice vector. -/
theorem slices_ae_zero_of_weightedSlices_ae_zero {σ : Type*} [Fintype σ]
    (F : Finset (Fin d → ℤ)) (freq : σ → Fin d → ℝ)
    (hExpansion : ∀ w : F → ℂ, ∃ c : σ → ℂ, ∀ f : F,
      w f = ∑ i, c i * FugledeTarget.exponentialCharacter (freq i) (FugledeCube.intVec f.val))
    (g : UnionL2 F)
    (hzero : ∀ i, FugledeSlices.weightedSlices F (freq i) g =ᵐ[volume.restrict FugledeCube.unitCube] 0) :
    ∀ f ∈ F, FugledeSlices.slice F f g =ᵐ[volume.restrict FugledeCube.unitCube] 0 := by
  classical
  have hall : ∀ᵐ u ∂volume.restrict FugledeCube.unitCube, ∀ i,
      FugledeSlices.weightedSlices F (freq i) g u = 0 := Filter.eventually_all.mpr hzero
  have hvec : ∀ᵐ u ∂volume.restrict FugledeCube.unitCube,
      ∀ f : F, FugledeSlices.slice F f.val g u = 0 := by
    filter_upwards [hall] with u hu
    apply finite_coefficients_detect_zero (α := F) (σ := σ)
      (fun i (f : F) => FugledeTarget.exponentialCharacter (freq i) (FugledeCube.intVec f.val))
      hExpansion (fun (f : F) => FugledeSlices.slice F f.val g u)
    intro i
    have h := hu i
    rw [weightedSlices_factor] at h
    have hn : conj (FugledeTarget.exponentialCharacter (freq i) u) ≠ 0 := by
      simpa using FugledeCharacters.character_ne_zero (freq i) u
    have hs := (mul_eq_zero.mp h).resolve_left hn
    simpa only [← Finset.sum_coe_sort F] using hs
  intro f hf
  filter_upwards [hvec] with u hu
  exact hu ⟨f, hf⟩

/-- True continuous Fourier completeness plus true finite expansion yields completeness. -/
theorem eq_zero_of_all_shifted_coefficients {σ : Type*} [Fintype σ]
    (F : Finset (Fin d → ℤ)) (freq : σ → Fin d → ℝ)
    (hExpansion : ∀ w : F → ℂ, ∃ c : σ → ℂ, ∀ f : F,
      w f = ∑ i, c i * FugledeTarget.exponentialCharacter (freq i) (FugledeCube.intVec f.val))
    (g : UnionL2 F)
    (hzero : ∀ i (z : Fin d → ℤ),
      (∫ x in FugledeCube.cubeUnion F,
        conj (FugledeTarget.exponentialCharacter (freq i + FugledeCube.intVec z) x) * g x) = 0) :
    g = 0 := by
  apply eq_zero_of_slices_ae_zero F g
  apply slices_ae_zero_of_weightedSlices_ae_zero F freq hExpansion g
  intro i
  apply FugledeFourier.ae_eq_zero_of_integer_fourier_integrals
    (FugledeSlices.weightedSlices_memLp F (freq i) g)
  intro z
  rw [← FugledeCharacters.coefficient_eq_weightedSlices_fourier]
  exact hzero i z

def spectrum {σ : Type*} (freq : σ → Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.range (fun p : σ × (Fin d → ℤ) => freq p.1 + FugledeCube.intVec p.2)

/-- The closed complex span of the actual indexed spectrum is all of union L2. -/
theorem spectrum_closedSpan_top {σ : Type*} [Fintype σ]
    (F : Finset (Fin d → ℤ)) (freq : σ → Fin d → ℝ)
    (hExpansion : ∀ w : F → ℂ, ∃ c : σ → ℂ, ∀ f : F,
      w f = ∑ i, c i * FugledeTarget.exponentialCharacter (freq i) (FugledeCube.intVec f.val)) :
    Submodule.topologicalClosure
      (Submodule.span ℂ (Set.range fun ξ : spectrum freq => e F ξ.val)) = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro g hg
  apply eq_zero_of_all_shifted_coefficients F freq hExpansion g
  intro i z
  rw [← inner_e_eq_integral]
  apply Submodule.inner_right_of_mem_orthogonal _ hg
  apply Submodule.subset_span
  exact ⟨⟨freq i + FugledeCube.intVec z, ⟨(i, z), rfl⟩⟩, rfl⟩

end
end FugledeSpectralBridge

#print axioms FugledeSpectralBridge.inner_e_eq_integral
#print axioms FugledeSpectralBridge.finite_coefficients_detect_zero
#print axioms FugledeSpectralBridge.eq_zero_of_all_shifted_coefficients
#print axioms FugledeSpectralBridge.spectrum_closedSpan_top
