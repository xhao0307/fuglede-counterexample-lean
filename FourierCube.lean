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
import CubeGeometry
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

/-! Integer Fourier completeness on the actual half-open unit cube.
The torus transport and change from Ioc to Ico are proved here. -/
set_option Elab.async false
set_option debug.skipKernelTC false
set_option maxRecDepth 1000000
namespace FugledeFourier
open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal
noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

def iocCube : Set (d → ℝ) := {u | ∀ i, u i ∈ Ioc (0 : ℝ) (0 + 1)}
lemma measurableSet_iocCube : MeasurableSet (iocCube : Set (d → ℝ)) := by
  exact MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
lemma unitCube_ae_eq_iocCube : (FugledeCube.unitCube : Set (d → ℝ)) =ᵐ[volume] iocCube := by
  rw [FugledeCube.unitCube_eq_pi]
  have h := Measure.ae_eq_set_pi (I := Set.univ) (μ := fun _ : d => (volume : Measure ℝ))
    (s := fun _ => Ico (0 : ℝ) 1) (t := fun _ => Ioc (0 : ℝ) 1)
    (fun _ _ => Ico_ae_eq_Ioc)
  rw [volume_pi]
  simpa [iocCube, Set.pi] using h
lemma restrict_unitCube_eq_iocCube :
    volume.restrict (FugledeCube.unitCube : Set (d → ℝ)) = volume.restrict iocCube :=
  Measure.restrict_congr_set unitCube_ae_eq_iocCube

def torusEquiv : UnitAddTorus d ≃ᵐ (iocCube : Set (d → ℝ)) :=
  UnitAddTorus.measurableEquivPiIoc (fun _ : d => 0)
def torusMap (t : UnitAddTorus d) : d → ℝ := (torusEquiv t).val
lemma torusMap_measurableEmbedding : MeasurableEmbedding (torusMap : UnitAddTorus d → d → ℝ) :=
  (MeasurableEmbedding.subtype_coe measurableSet_iocCube).comp torusEquiv.measurableEmbedding
lemma torusMap_measurePreserving :
    MeasurePreserving (torusMap : UnitAddTorus d → d → ℝ) volume
      (volume.restrict FugledeCube.unitCube) := by
  have he : MeasurePreserving (torusEquiv : UnitAddTorus d ≃ᵐ iocCube) volume
      (Measure.comap Subtype.val volume) :=
    UnitAddTorus.measurePreserving_equivPiIoc (fun _ : d => 0)
  have hs : MeasurePreserving (Subtype.val : iocCube → d → ℝ)
      (Measure.comap Subtype.val volume) (volume.restrict iocCube) :=
    ⟨measurable_subtype_coe, by
      exact map_comap_subtype_coe (s := (iocCube : Set (d → ℝ)))
        measurableSet_iocCube (volume : Measure (d → ℝ))⟩
  rw [restrict_unitCube_eq_iocCube]
  exact hs.comp he
omit [Fintype d] in
lemma torusMap_quotient (t : UnitAddTorus d) :
    (fun i => (torusMap t i : UnitAddCircle)) = t :=
  torusEquiv.symm_apply_apply t

/-- Actual complex exponential at an arbitrary integer frequency. -/
def integerCharacter (z : d → ℤ) (u : d → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (z i : ℝ) * u i : ℝ) : ℂ))
lemma mFourier_quotient (z : d → ℤ) (u : d → ℝ) :
    UnitAddTorus.mFourier z (fun i => (u i : UnitAddCircle)) = integerCharacter z u := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  unfold integerCharacter
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
lemma mFourier_torusMap (z : d → ℤ) (t : UnitAddTorus d) :
    UnitAddTorus.mFourier z t = integerCharacter z (torusMap t) := by
  rw [← mFourier_quotient, torusMap_quotient]

abbrev CubeL2 (d : Type*) [Fintype d] :=
  Lp ℂ 2 (volume.restrict (FugledeCube.unitCube : Set (d → ℝ)))
abbrev TorusL2 (d : Type*) [Fintype d] := Lp ℂ 2 (volume : Measure (UnitAddTorus d))
def pullback (g : CubeL2 d) : TorusL2 d :=
  Lp.compMeasurePreserving torusMap torusMap_measurePreserving g
lemma pullback_injective : Function.Injective (pullback : CubeL2 d → TorusL2 d) :=
  (Lp.isometry_compMeasurePreserving torusMap_measurePreserving).injective
lemma coe_pullback (g : CubeL2 d) : pullback g =ᵐ[volume] g ∘ torusMap :=
  Lp.coeFn_compMeasurePreserving g torusMap_measurePreserving
lemma pullback_fourierCoeff (g : CubeL2 d) (z : d → ℤ) :
    UnitAddTorus.mFourierCoeff (pullback g) z =
      ∫ u in FugledeCube.unitCube, conj (integerCharacter z u) * g u := by
  unfold UnitAddTorus.mFourierCoeff
  calc
    _ = ∫ t : UnitAddTorus d, conj (integerCharacter z (torusMap t)) * g (torusMap t) := by
      apply integral_congr_ae
      filter_upwards [coe_pullback g] with t ht
      rw [UnitAddTorus.mFourier_neg, mFourier_torusMap, ht, smul_eq_mul]
      rfl
    _ = _ := torusMap_measurePreserving.integral_comp torusMap_measurableEmbedding
      (fun u => conj (integerCharacter z u) * g u)

/-- All integer Fourier coefficients determine an L² function on the half-open cube. -/
theorem eq_zero_of_integer_fourier_integrals (g : CubeL2 d)
    (hzero : ∀ z : d → ℤ,
      (∫ u in FugledeCube.unitCube, conj (integerCharacter z u) * g u) = 0) : g = 0 := by
  have hcoeff (z : d → ℤ) : UnitAddTorus.mFourierCoeff (pullback g) z = 0 := by
    rw [pullback_fourierCoeff, hzero]
  have hr : UnitAddTorus.mFourierBasis.repr (pullback g) = 0 := by
    ext z
    rw [UnitAddTorus.mFourierBasis_repr, hcoeff]
    simp
  have hp : pullback g = 0 := UnitAddTorus.mFourierBasis.repr.injective (by simpa using hr)
  apply pullback_injective
  simpa [pullback] using hp

/-- The same conclusion for an ordinary square-integrable representative. -/
theorem ae_eq_zero_of_integer_fourier_integrals {g : (d → ℝ) → ℂ}
    (hg : MemLp g 2 (volume.restrict FugledeCube.unitCube))
    (hzero : ∀ z : d → ℤ,
      (∫ u in FugledeCube.unitCube, conj (integerCharacter z u) * g u) = 0) :
    g =ᵐ[volume.restrict FugledeCube.unitCube] 0 := by
  have hLp : hg.toLp g = 0 := by
    apply eq_zero_of_integer_fourier_integrals
    intro z
    calc
      _ = ∫ u in FugledeCube.unitCube, conj (integerCharacter z u) * g u := by
        apply integral_congr_ae
        filter_upwards [hg.coeFn_toLp] with u hu
        rw [hu]
      _ = 0 := hzero z
  apply hg.coeFn_toLp.symm.trans
  rw [hLp]
  exact Lp.coeFn_zero ℂ 2 (volume.restrict FugledeCube.unitCube)

end
end FugledeFourier
#print axioms FugledeFourier.eq_zero_of_integer_fourier_integrals
#print axioms FugledeFourier.ae_eq_zero_of_integer_fourier_integrals
#print axioms FugledeFourier.torusMap_measurePreserving
#print axioms FugledeFourier.pullback_fourierCoeff
