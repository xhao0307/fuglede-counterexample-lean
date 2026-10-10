import CubeGeometry
import CanonicalDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Actual translated L2 slices on integer half-open cubes and their finite
complex-exponential weighted sum.  No spectrality or orthogonality is
assumed here.
-/
set_option Elab.async false
set_option debug.skipKernelTC false
namespace FugledeSlices
open Set MeasureTheory
open scoped BigOperators ComplexConjugate

variable {d : ℕ}
abbrev RPoint (d : ℕ) := Fin d → ℝ
abbrev IPoint (d : ℕ) := Fin d → ℤ

/-- Translation is measure preserving between the actual half-open cubes. -/
theorem cube_translation_preserving (f : IPoint d) :
    MeasurePreserving (fun u : RPoint d => FugledeCube.intVec f + u)
      (volume.restrict FugledeCube.unitCube)
      (volume.restrict (FugledeCube.cubeAt f)) := by
  have hpre : (fun u : RPoint d => FugledeCube.intVec f + u) ⁻¹'
      FugledeCube.cubeAt f = FugledeCube.unitCube := by
    ext u
    simp [FugledeCube.cubeAt, FugledeCube.translate]
  simpa only [hpre] using
    (measurePreserving_add_left volume (FugledeCube.intVec f)).restrict_preimage
      (FugledeCube.measurableSet_cubeAt f)

lemma cube_subset_union (F : Finset (IPoint d)) {f : IPoint d} (hf : f ∈ F) :
    FugledeCube.cubeAt f ⊆ FugledeCube.cubeUnion F := by
  intro x hx
  exact ⟨f, hf, hx⟩

noncomputable def slice (F : Finset (IPoint d)) (f : IPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) : RPoint d → ℂ :=
  fun u => g (FugledeCube.intVec f + u)

/-- Restricting a true union-L2 function to an actual translated cube is L2. -/
theorem slice_memLp (F : Finset (IPoint d)) {f : IPoint d} (hf : f ∈ F)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    MemLp (slice F f g) 2 (volume.restrict FugledeCube.unitCube) := by
  have hc : MemLp (g : RPoint d → ℂ) 2
      (volume.restrict (FugledeCube.cubeAt f)) :=
    MemLp.mono_measure
      (Measure.restrict_mono_set volume (cube_subset_union F hf)) (Lp.memLp g)
  exact hc.comp_measurePreserving (cube_translation_preserving f)

noncomputable def phase (ξ : RPoint d) (f : IPoint d) (u : RPoint d) : ℂ :=
  conj (FugledeTarget.exponentialCharacter ξ (FugledeCube.intVec f + u))

theorem phase_continuous (ξ : RPoint d) (f : IPoint d) : Continuous (phase ξ f) :=
  Complex.continuous_conj.comp
    ((FugledeTarget.continuous_exponentialCharacter ξ).comp
      (continuous_const.add continuous_id))

theorem phase_norm (ξ : RPoint d) (f : IPoint d) (u : RPoint d) :
    ‖phase ξ f u‖ = 1 := by
  simp [phase, FugledeTarget.norm_exponentialCharacter]

noncomputable def weightedSlice (F : Finset (IPoint d)) (ξ : RPoint d) (f : IPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) : RPoint d → ℂ :=
  fun u => phase ξ f u * slice F f g u

/-- The multiplier is the actual conjugate complex exponential, with norm one. -/
theorem weightedSlice_memLp (F : Finset (IPoint d)) (ξ : RPoint d)
    {f : IPoint d} (hf : f ∈ F)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    MemLp (weightedSlice F ξ f g) 2 (volume.restrict FugledeCube.unitCube) := by
  have hs := slice_memLp F hf g
  apply hs.of_le
  · exact (phase_continuous ξ f).aestronglyMeasurable.mul hs.aestronglyMeasurable
  · exact ae_of_all _ (fun u => by simp [weightedSlice, phase_norm])

noncomputable def weightedSlices (F : Finset (IPoint d)) (ξ : RPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) : RPoint d → ℂ :=
  fun u => ∑ f ∈ F, weightedSlice F ξ f g u

theorem weightedSlices_memLp (F : Finset (IPoint d)) (ξ : RPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    MemLp (weightedSlices F ξ g) 2 (volume.restrict FugledeCube.unitCube) :=
  memLp_finsetSum F (fun _ hf => weightedSlice_memLp F ξ hf g)

/-- The unit-cube restriction has its actual finite Lebesgue measure. -/
lemma unitCube_finiteMeasure :
    IsFiniteMeasure (volume.restrict (FugledeCube.unitCube : Set (RPoint d))) := by
  apply isFiniteMeasure_restrict.mpr
  rw [FugledeCube.volume_unitCube]
  simp

lemma union_finiteMeasure (F : Finset (IPoint d)) :
    IsFiniteMeasure (volume.restrict (FugledeCube.cubeUnion F)) :=
  isFiniteMeasure_restrict.mpr (FugledeCube.volume_cubeUnion_ne_top F)

theorem slice_integrable (F : Finset (IPoint d)) {f : IPoint d} (hf : f ∈ F)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    Integrable (slice F f g) (volume.restrict FugledeCube.unitCube) := by
  let _ := (unitCube_finiteMeasure :
    IsFiniteMeasure (volume.restrict (FugledeCube.unitCube : Set (RPoint d))))
  exact MemLp.integrable (by norm_num) (slice_memLp F hf g)

theorem weightedSlice_integrable (F : Finset (IPoint d)) (ξ : RPoint d)
    {f : IPoint d} (hf : f ∈ F)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    Integrable (weightedSlice F ξ f g) (volume.restrict FugledeCube.unitCube) := by
  let _ := (unitCube_finiteMeasure :
    IsFiniteMeasure (volume.restrict (FugledeCube.unitCube : Set (RPoint d))))
  exact MemLp.integrable (by norm_num) (weightedSlice_memLp F ξ hf g)

theorem weightedSlices_integrable (F : Finset (IPoint d)) (ξ : RPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    Integrable (weightedSlices F ξ g) (volume.restrict FugledeCube.unitCube) := by
  let _ := (unitCube_finiteMeasure :
    IsFiniteMeasure (volume.restrict (FugledeCube.unitCube : Set (RPoint d))))
  exact MemLp.integrable (by norm_num) (weightedSlices_memLp F ξ g)

theorem unionLp_integrable (F : Finset (IPoint d))
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    Integrable (g : RPoint d → ℂ) (volume.restrict (FugledeCube.cubeUnion F)) := by
  let _ := union_finiteMeasure F
  exact MemLp.integrable (by norm_num) (Lp.memLp g)

/-- This is the true exponential multiplier for every finite union L2 function. -/
theorem character_weight_memLp (F : Finset (IPoint d)) (ξ : RPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    MemLp (fun x => conj (FugledeTarget.exponentialCharacter ξ x) * g x) 2
      (volume.restrict (FugledeCube.cubeUnion F)) := by
  apply (Lp.memLp g).of_le
  · exact (Complex.continuous_conj.comp
      (FugledeTarget.continuous_exponentialCharacter ξ)).aestronglyMeasurable.mul
        (Lp.memLp g).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by simp [FugledeTarget.norm_exponentialCharacter])

theorem character_weight_integrable (F : Finset (IPoint d)) (ξ : RPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    Integrable (fun x => conj (FugledeTarget.exponentialCharacter ξ x) * g x)
      (volume.restrict (FugledeCube.cubeUnion F)) := by
  let _ := union_finiteMeasure F
  exact MemLp.integrable (by norm_num) (character_weight_memLp F ξ g)

/-- Actual integrability makes finite-union decomposition valid. -/
theorem integral_union_eq_sum_slices (F : Finset (IPoint d)) (h : RPoint d → ℂ)
    (hh : IntegrableOn h (FugledeCube.cubeUnion F) volume) :
    (∫ x in FugledeCube.cubeUnion F, h x) =
      ∑ f ∈ F, ∫ u in FugledeCube.unitCube, h (FugledeCube.intVec f + u) := by
  classical
  rw [FugledeCube.cubeUnion_eq_iUnion]
  rw [integral_biUnion_finset F (fun f _ => FugledeCube.measurableSet_cubeAt f)
    (FugledeCube.cubeAt_pairwise_disjoint F)
    (fun _ hf => hh.mono_set (cube_subset_union F hf))]
  apply Finset.sum_congr rfl
  intro f _
  rw [FugledeCube.cubeAt_eq_image]
  exact (measurePreserving_add_left volume (FugledeCube.intVec f)).setIntegral_image_emb
    (Homeomorph.addLeft (FugledeCube.intVec f)).measurableEmbedding h FugledeCube.unitCube

/-- Specialization to actual union-L2 functions, with integrability discharged. -/
theorem integral_unionLp_eq_sum_slices (F : Finset (IPoint d))
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    (∫ x in FugledeCube.cubeUnion F, g x) =
      ∑ f ∈ F, ∫ u in FugledeCube.unitCube, slice F f g u :=
  integral_union_eq_sum_slices F g (unionLp_integrable F g)

/-- The finite weighted slice sum gives the actual character coefficient. -/
theorem integral_character_weight_eq_integral_weightedSlices
    (F : Finset (IPoint d)) (ξ : RPoint d)
    (g : Lp ℂ 2 (volume.restrict (FugledeCube.cubeUnion F))) :
    (∫ x in FugledeCube.cubeUnion F,
      conj (FugledeTarget.exponentialCharacter ξ x) * g x) =
      ∫ u in FugledeCube.unitCube, weightedSlices F ξ g u := by
  classical
  calc
    _ = ∑ f ∈ F, ∫ u in FugledeCube.unitCube, weightedSlice F ξ f g u :=
      integral_union_eq_sum_slices F _ (character_weight_integrable F ξ g)
    _ = _ :=
      (integral_finsetSum F (fun _ hf => weightedSlice_integrable F ξ hf g)).symm

#print axioms cube_translation_preserving
#print axioms slice_memLp
#print axioms weightedSlice_memLp
#print axioms weightedSlices_memLp
#print axioms weightedSlices_integrable
#print axioms character_weight_memLp
#print axioms integral_union_eq_sum_slices
#print axioms integral_unionLp_eq_sum_slices
#print axioms integral_character_weight_eq_integral_weightedSlices
end FugledeSlices
