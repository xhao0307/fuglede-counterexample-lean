import CubeSampling
import Mathlib.Topology.Bornology.Constructions

/-!
Geometry and measure of actual finite unions of integer half-open cubes.
These conditions are part of the full Euclidean Fuglede target, rather than
a replacement definition of spectrality or tiling.
-/
namespace FugledeCube

set_option debug.skipKernelTC false

open Set MeasureTheory
open scoped ENNReal

variable {d : Type*} [Fintype d]

def cubeAt (f : d → ℤ) : Set (d → ℝ) := translate (intVec f) unitCube

omit [Fintype d] in
theorem unitCube_eq_pi : (unitCube : Set (d → ℝ)) =
    Set.pi Set.univ (fun _ : d => Set.Ico (0 : ℝ) 1) := by
  ext u
  simp [unitCube, Set.mem_pi]

theorem measurableSet_unitCube : MeasurableSet (unitCube : Set (d → ℝ)) := by
  rw [unitCube_eq_pi]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

theorem volume_unitCube : volume (unitCube : Set (d → ℝ)) = 1 := by
  rw [unitCube_eq_pi, Real.volume_pi_Ico]
  simp

theorem measurableSet_cubeAt (f : d → ℤ) : MeasurableSet (cubeAt f) := by
  exact measurableSet_unitCube.preimage (measurable_id.sub measurable_const)

theorem volume_cubeAt (f : d → ℤ) : volume (cubeAt f) = 1 := by
  have h := (measurePreserving_sub_right volume (intVec f)).measure_preimage
    measurableSet_unitCube.nullMeasurableSet
  exact h.trans volume_unitCube

omit [Fintype d] in
theorem cubeUnion_eq_iUnion (F : Finset (d → ℤ)) :
    cubeUnion F = ⋃ f ∈ F, cubeAt f := by
  ext x
  simp [cubeUnion, cubeAt, translate]

theorem measurableSet_cubeUnion (F : Finset (d → ℤ)) :
    MeasurableSet (cubeUnion F) := by
  rw [cubeUnion_eq_iUnion]
  exact MeasurableSet.biUnion F.countable_toSet (fun f _ => measurableSet_cubeAt f)

omit [Fintype d] in
theorem cubeAt_pairwise_disjoint (F : Finset (d → ℤ)) :
    (F : Set (d → ℤ)).PairwiseDisjoint cubeAt := by
  intro f _ g _ hfg
  apply Set.disjoint_left.mpr
  intro x hxf hxg
  apply hfg
  funext i
  have hf : ⌊x i⌋ = f i := Int.floor_eq_iff.mpr
    ⟨by have := hxf i; change 0 ≤ x i - (f i : ℝ) ∧ _ at this; linarith,
     by have := hxf i; change _ ∧ x i - (f i : ℝ) < 1 at this; linarith⟩
  have hg : ⌊x i⌋ = g i := Int.floor_eq_iff.mpr
    ⟨by have := hxg i; change 0 ≤ x i - (g i : ℝ) ∧ _ at this; linarith,
     by have := hxg i; change _ ∧ x i - (g i : ℝ) < 1 at this; linarith⟩
  exact hf.symm.trans hg

theorem volume_cubeUnion (F : Finset (d → ℤ)) :
    volume (cubeUnion F) = (F.card : ℝ≥0∞) := by
  rw [cubeUnion_eq_iUnion, measure_biUnion_finset (cubeAt_pairwise_disjoint F)
    (fun f _ => measurableSet_cubeAt f)]
  simp only [volume_cubeAt, Finset.sum_const, nsmul_eq_mul, mul_one]

omit [Fintype d] in
theorem cubeAt_eq_image (f : d → ℤ) :
    cubeAt f = (fun u => intVec f + u) '' unitCube := by
  ext x
  constructor
  · intro hx
    refine ⟨x - intVec f, hx, ?_⟩
    dsimp
    rw [add_comm, sub_add_cancel]
  · rintro ⟨u, hu, rfl⟩
    simpa [cubeAt, translate, add_sub_cancel_left] using hu

omit [Fintype d] in
theorem isBounded_unitCube : Bornology.IsBounded (unitCube : Set (d → ℝ)) := by
  apply (Bornology.IsBounded.pi (fun _ : d => Metric.isBounded_Icc (0 : ℝ) 1)).subset
  intro u hu i _
  exact ⟨(hu i).1, (hu i).2.le⟩

theorem isBounded_cubeAt (f : d → ℤ) : Bornology.IsBounded (cubeAt f) := by
  rw [cubeAt_eq_image]
  exact (isometry_add_left (intVec f)).lipschitzWith.isBounded_image isBounded_unitCube

theorem isBounded_cubeUnion (F : Finset (d → ℤ)) :
    Bornology.IsBounded (cubeUnion F) := by
  rw [cubeUnion_eq_iUnion]
  exact (Bornology.isBounded_biUnion_finset F).mpr (fun f _ => isBounded_cubeAt f)

theorem volume_cubeUnion_pos (F : Finset (d → ℤ)) (hF : F.Nonempty) :
    0 < volume (cubeUnion F) := by
  rw [volume_cubeUnion]
  exact_mod_cast Finset.card_pos.mpr hF

theorem volume_cubeUnion_ne_top (F : Finset (d → ℤ)) :
    volume (cubeUnion F) ≠ ⊤ := by
  rw [volume_cubeUnion]
  exact ENNReal.natCast_ne_top _

end FugledeCube

#print axioms FugledeCube.measurableSet_cubeUnion
#print axioms FugledeCube.cubeAt_pairwise_disjoint
#print axioms FugledeCube.volume_cubeUnion
#print axioms FugledeCube.isBounded_cubeUnion
