import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure

namespace FugledeCube

variable {d : Type*}

def intVec (z : d → ℤ) : d → ℝ := fun i => z i

def unitCube : Set (d → ℝ) := {u | ∀ i, 0 ≤ u i ∧ u i < 1}

def cubeUnion (F : Finset (d → ℤ)) : Set (d → ℝ) :=
  {x | ∃ f ∈ F, x - intVec f ∈ unitCube}

def translate (t : d → ℝ) (S : Set (d → ℝ)) : Set (d → ℝ) :=
  {x | x - t ∈ S}

noncomputable def sampleCarry (u t : d → ℝ) : d → ℤ := fun i => -⌊u i - t i⌋

lemma coordinate_membership (u t : ℝ) (z f : ℤ) :
    (0 ≤ u + (z : ℝ) - t - f ∧ u + (z : ℝ) - t - f < 1) ↔
      z = -⌊u - t⌋ + f := by
  have hfloor : ⌊u + (z : ℝ) - t⌋ = ⌊u - t⌋ + z := by
    have heq : u + (z : ℝ) - t = (u - t) + (z : ℝ) := by ring
    rw [heq, Int.floor_add_intCast]
  constructor
  · rintro ⟨hl, hu⟩
    have hf : ⌊u + (z : ℝ) - t⌋ = f :=
      Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    rw [hfloor] at hf
    linarith
  · intro hz
    have hf : ⌊u + (z : ℝ) - t⌋ = f := by rw [hfloor]; linarith
    obtain ⟨hl, hu⟩ := Int.floor_eq_iff.mp hf
    constructor <;> linarith

/-- Integer half-open cubes admit an exact sampling rule, even on their boundaries. -/
theorem sampling_membership (F : Finset (d → ℤ)) (u t : d → ℝ) (z : d → ℤ) :
    u + intVec z ∈ translate t (cubeUnion F) ↔
      ∃ f ∈ F, z = sampleCarry u t + f := by
  constructor
  · rintro ⟨f, hf, hmem⟩
    refine ⟨f, hf, ?_⟩
    funext i
    exact (coordinate_membership (u i) (t i) (z i) (f i)).mp (hmem i)
  · rintro ⟨f, hf, hz⟩
    refine ⟨f, hf, ?_⟩
    intro i
    exact (coordinate_membership (u i) (t i) (z i) (f i)).mpr (congrFun hz i)

def IntegerTiles (F : Finset (d → ℤ)) : Prop :=
  ∃ C : Set (d → ℤ), ∀ z : d → ℤ,
    ∃! p : F × C, p.1.val + p.2.val = z

lemma integerTiles_of_unique_sampling (F : Finset (d → ℤ)) (u : d → ℝ)
    (T : Set (d → ℝ))
    (h : ∀ z : d → ℤ, ∃! t : T, u + intVec z ∈ translate t.val (cubeUnion F)) :
    IntegerTiles F := by
  classical
  let C : Set (d → ℤ) := sampleCarry u '' T
  refine ⟨C, fun z => ?_⟩
  obtain ⟨t, ht, huniq⟩ := h z
  obtain ⟨f, hf, hzf⟩ := (sampling_membership F u t.val z).mp ht
  have hc : sampleCarry u t.val ∈ C := Set.mem_image_of_mem _ t.property
  refine ⟨(⟨f, hf⟩, ⟨sampleCarry u t.val, hc⟩), ?_, ?_⟩
  · exact (add_comm _ _).trans hzf.symm
  · intro p hp
    obtain ⟨s, hs, hsc⟩ := p.2.property
    have hsmem : u + intVec z ∈ translate s (cubeUnion F) := by
      apply (sampling_membership F u s z).mpr
      refine ⟨p.1.val, p.1.property, ?_⟩
      simpa only [hsc, add_comm] using hp.symm
    have hst : s = t.val := congrArg Subtype.val (huniq ⟨s, hs⟩ hsmem)
    have hpc : p.2.val = sampleCarry u t.val := by simpa only [hst] using hsc.symm
    have hpf : p.1.val = f := by
      apply add_right_cancel (b := sampleCarry u t.val)
      calc
        p.1.val + sampleCarry u t.val = z := by simpa only [hpc] using hp
        _ = f + sampleCarry u t.val := by simpa only [add_comm] using hzf
    apply Prod.ext
    · exact Subtype.ext hpf
    · exact Subtype.ext hpc

open MeasureTheory Set

/-- This input is the canonical a.e. covering and a.e. disjointness definition,
without assuming any discrete structure on the real translation set. -/
theorem integerTiles_of_countable_tiling [Fintype d] (F : Finset (d → ℤ))
    (htile : ∃ T : Set (d → ℝ), T.Countable ∧
      volume (univ \ (⋃ t ∈ T, translate t (cubeUnion F))) = 0 ∧
      (∀ {t₁ t₂ : d → ℝ}, t₁ ∈ T → t₂ ∈ T → t₁ ≠ t₂ →
        volume (translate t₁ (cubeUnion F) ∩ translate t₂ (cubeUnion F)) = 0)) :
    IntegerTiles F := by
  classical
  obtain ⟨T, hT, hcover, hdisjoint⟩ := htile
  have : Countable T := hT.to_subtype
  have hcover' : ∀ᵐ x ∂volume, ∃ t : T, x ∈ translate t.val (cubeUnion F) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hcover] with x hx
    have hx' : x ∈ ⋃ t ∈ T, translate t (cubeUnion F) := by simpa using hx
    obtain ⟨t, ht, hx⟩ := mem_iUnion₂.mp hx'
    exact ⟨⟨t, ht⟩, hx⟩
  have hpair (s t : T) : ∀ᵐ x ∂volume,
      x ∈ translate s.val (cubeUnion F) → x ∈ translate t.val (cubeUnion F) → s = t := by
    by_cases hst : s = t
    · exact Filter.Eventually.of_forall (fun _ _ _ => hst)
    · have hn := hdisjoint s.property t.property (Subtype.coe_ne_coe.mpr hst)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hn] with x hx
      exact fun hs ht => (hx ⟨hs, ht⟩).elim
  have hpairs : ∀ᵐ x ∂volume, ∀ s t : T,
      x ∈ translate s.val (cubeUnion F) → x ∈ translate t.val (cubeUnion F) → s = t :=
    ae_all_iff.mpr (fun s => ae_all_iff.mpr (hpair s))
  have hunique : ∀ᵐ x ∂volume, ∃! t : T, x ∈ translate t.val (cubeUnion F) := by
    filter_upwards [hcover', hpairs] with x hx huniq
    obtain ⟨t, ht⟩ := hx
    exact ⟨t, ht, fun s hs => huniq s t hs ht⟩
  have hgrid : ∀ᵐ u ∂volume, ∀ z : d → ℤ,
      ∃! t : T, u + intVec z ∈ translate t.val (cubeUnion F) := by
    apply ae_all_iff.mpr
    intro z
    exact (measurePreserving_add_right volume (intVec z)).quasiMeasurePreserving.ae hunique
  obtain ⟨u, hu⟩ := hgrid.exists
  exact integerTiles_of_unique_sampling F u T hu

end FugledeCube

#print axioms FugledeCube.coordinate_membership
#print axioms FugledeCube.sampling_membership
#print axioms FugledeCube.integerTiles_of_unique_sampling
#print axioms FugledeCube.integerTiles_of_countable_tiling
