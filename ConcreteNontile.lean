import FiniteNontile
import TilingTransfer
import CubeGeometry
import CanonicalDefinitions
import Mathlib.Data.Fin.VecNotation

/-!
The actual 97-block planar set from arXiv:2607.15632v1 is bounded,
measurable, has positive finite volume, and cannot tile by arbitrary
countable real translations. Spectrality is still a separate obligation.
-/
namespace FugledeConcrete

set_option debug.skipKernelTC false

open Set MeasureTheory
open scoped ENNReal

abbrev Point := ℤ × ℤ

def toVec (p : Point) : Fin 2 → ℤ := ![p.1, p.2]
def toPair (p : Fin 2 → ℤ) : Point := (p 0, p 1)

theorem toPair_toVec (p : Point) : toPair (toVec p) = p := rfl

theorem toVec_toPair (p : Fin 2 → ℤ) : toVec (toPair p) = p := by
  funext i
  fin_cases i <;> rfl

theorem toPair_add (p q : Fin 2 → ℤ) : toPair (p + q) = toPair p + toPair q := rfl

theorem toVec_add (p q : Point) : toVec (p + q) = toVec p + toVec q := by
  funext i
  fin_cases i <;> rfl

theorem toVec_injective : Function.Injective toVec := by
  intro p q h
  exact (toPair_toVec p).symm.trans ((congrArg toPair h).trans (toPair_toVec q))

/-- Direct coverage of raw pairs implies the true subtype-pair bijection. -/
theorem tiles_of_direct {G : Type*} [DecidableEq G] [Add G]
    (A B : Finset G) (h : FugledeTransfer.DirectTiling A B) :
    FugledeNontile.Tiles A B := by
  constructor
  · intro p q hpq
    obtain ⟨r, _, huniq⟩ := h (FugledeNontile.sumMap A B p)
    have hp : (p.1.val, p.2.val) = r := huniq _ ⟨p.1.property, p.2.property, rfl⟩
    have hq : (q.1.val, q.2.val) = r := huniq _
      ⟨q.1.property, q.2.property, hpq.symm⟩
    have heq := hp.trans hq.symm
    exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
      (Subtype.ext (congrArg Prod.snd heq))
  · intro g
    obtain ⟨r, ⟨ha, hb, heq⟩, _⟩ := h g
    exact ⟨(⟨r.1, ha⟩, ⟨r.2, hb⟩), heq⟩

def baseSet : Finset (ZMod 60 × ZMod 12) := FugledeNontile.Aplus
def pairBlock : Finset Point := FugledeTransfer.blockCopies 60 12 97 baseSet
def vectorBlock : Finset (Fin 2 → ℤ) := pairBlock.image toVec
def omega : Set (Fin 2 → ℝ) := FugledeCube.cubeUnion vectorBlock

theorem baseSet_card : baseSet.card = 60 := FugledeNontile.card_Aplus

theorem pairBlock_card : pairBlock.card = 564540 := by
  rw [pairBlock, FugledeTransfer.card_blockCopies 60 12 97 (by decide) (by decide),
    baseSet_card]
  norm_num

theorem vectorBlock_card : vectorBlock.card = 564540 := by
  rw [vectorBlock, Finset.card_image_of_injective _ toVec_injective, pairBlock_card]

theorem pairBlock_nontile : ¬ ∃ T : Set Point, ∀ z : Point,
    ∃! p : pairBlock × T, p.1.val + p.2.val = z := by
  apply FugledeTransfer.sixty_point_block97_nontiling baseSet baseSet_card
  rintro ⟨B, hB⟩
  exact FugledeNontile.Aplus_no_complement ⟨B, tiles_of_direct baseSet B hB⟩

/-- Coordinate equivalence preserves unique-representation lattice tilings. -/
theorem pair_tiles_of_vector_tiles (F : Finset Point)
    (ht : FugledeCube.IntegerTiles (F.image toVec)) :
    ∃ T : Set Point, ∀ z : Point, ∃! p : F × T, p.1.val + p.2.val = z := by
  classical
  obtain ⟨C, hC⟩ := ht
  let T : Set Point := toPair '' C
  refine ⟨T, fun z => ?_⟩
  obtain ⟨v, hv, huniq⟩ := hC (toVec z)
  obtain ⟨a, ha, heqa⟩ := Finset.mem_image.mp v.1.property
  have ht : toPair v.2.val ∈ T := Set.mem_image_of_mem _ v.2.property
  have hva : toPair v.1.val = a := by rw [← heqa, toPair_toVec]
  refine ⟨(⟨a, ha⟩, ⟨toPair v.2.val, ht⟩), ?_, ?_⟩
  · have h := congrArg toPair hv
    simpa only [toPair_add, toPair_toVec, hva] using h
  · intro p hp
    obtain ⟨c, hc, heqc⟩ := p.2.property
    have hcv : c = toVec p.2.val := by rw [← heqc, toVec_toPair]
    let w : (F.image toVec) × C :=
      (⟨toVec p.1.val, Finset.mem_image_of_mem _ p.1.property⟩, ⟨c, hc⟩)
    have hw : w.1.val + w.2.val = toVec z := by
      change toVec p.1.val + c = toVec z
      rw [hcv, ← toVec_add, hp]
    have hwv : w = v := huniq w hw
    have hfirst : p.1.val = a := by
      have h := congrArg (fun q : (F.image toVec) × C => toPair q.1.val) hwv
      simpa only [w, toPair_toVec, hva] using h
    have hsecond : p.2.val = toPair v.2.val := by
      have h := congrArg (fun q : (F.image toVec) × C => toPair q.2.val) hwv
      simpa only [w, heqc] using h
    exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)

theorem vectorBlock_nontile : ¬ FugledeCube.IntegerTiles vectorBlock := by
  intro h
  exact pairBlock_nontile (pair_tiles_of_vector_tiles pairBlock h)

theorem omega_nontile : ¬ FugledeTarget.tilesByTranslation omega := by
  intro h
  exact vectorBlock_nontile (FugledeCube.integerTiles_of_countable_tiling vectorBlock h)

theorem omega_measurable : MeasurableSet omega := FugledeCube.measurableSet_cubeUnion _
theorem omega_bounded : Bornology.IsBounded omega := FugledeCube.isBounded_cubeUnion _
theorem omega_volume : volume omega = 564540 := by
  rw [omega, FugledeCube.volume_cubeUnion, vectorBlock_card]
  norm_num

theorem omega_positive_volume : 0 < volume omega := by rw [omega_volume]; norm_num
theorem omega_finite_volume : volume omega ≠ ⊤ := by rw [omega_volume]; simp

end FugledeConcrete

#print axioms FugledeConcrete.pairBlock_nontile
#print axioms FugledeConcrete.omega_nontile
#print axioms FugledeConcrete.omega_volume
#print axioms FugledeConcrete.omega_measurable
#print axioms FugledeConcrete.omega_bounded
