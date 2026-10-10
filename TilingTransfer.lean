import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option debug.skipKernelTC false

/-!
Finite counting and rectangular geometry for the non-tiling direction of
Proposition 2.1(ii), Tao Zhang, arXiv:2607.15632v1.

The full non-tiling implication for rectangular finite cyclic groups is
proved here. Spectrality and the Euclidean passage are separate modules.
-/

namespace FugledeTransfer

open Finset

def translate {α : Type*} [DecidableEq α] [Add α] (v : α) (s : Finset α) :
    Finset α := s.image (v + ·)

theorem card_translate {α : Type*} [DecidableEq α] [AddLeftCancelSemigroup α]
    (v : α) (s : Finset α) : (translate v s).card = s.card := by
  exact Finset.card_image_of_injective s (fun _ _ h => add_left_cancel h)

theorem mem_translate {H : Type*} [DecidableEq H] [AddCommGroup H]
    (v x : H) (F : Finset H) : x ∈ translate v F ↔ x - v ∈ F := by
  constructor
  · intro hx
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hx
    have h : x - v = a := by rw [← hax, add_sub_cancel_left]
    exact h.symm ▸ ha
  · intro hx
    refine Finset.mem_image.mpr ⟨x - v, hx, ?_⟩
    rw [add_comm, sub_add_cancel]

/-- The actual packing estimate: disjoint equal-size translates inside a
finite container occupy `centers.card * tile.card` points. -/
theorem packed_translates_card_le {α : Type*} [DecidableEq α]
    [AddLeftCancelSemigroup α] (centers tile container : Finset α)
    (hdisjoint : (centers : Set α).PairwiseDisjoint (fun v => translate v tile))
    (hcontained : ∀ v ∈ centers, translate v tile ⊆ container) :
    centers.card * tile.card ≤ container.card := by
  have hsubset : centers.biUnion (fun v => translate v tile) ⊆ container := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
    exact hcontained v hv hxv
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_biUnion hdisjoint] at hcard
  simpa only [card_translate, Finset.sum_const, Nat.nsmul_eq_mul] using hcard

/-- A strict finite-volume inequality supplies a point avoiding every
translated boundary ring. No tiling or transference conclusion is assumed. -/
theorem exists_avoiding_translates {α : Type*} [DecidableEq α]
    [AddLeftCancelSemigroup α] (centers ring target : Finset α)
    (hvolume : centers.card * ring.card < target.card) :
    ∃ x ∈ target, ∀ v ∈ centers, x ∉ translate v ring := by
  have hbad : (centers.biUnion (fun v => translate v ring)).card < target.card :=
    lt_of_le_of_lt (Finset.card_biUnion_le_card_mul centers _ ring.card
      (fun v _ => (card_translate v ring).le)) hvolume
  obtain ⟨x, hx, hbadx⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  refine ⟨x, hx, ?_⟩
  intro v hv hxv
  exact hbadx (Finset.mem_biUnion.mpr ⟨v, hv, hxv⟩)

noncomputable def meetingCenters {H : Type*} [DecidableEq H] [AddCommGroup H]
    (F box : Finset H) (T : Set H) : Finset H := by
  classical
  exact ((box ×ˢ F).image (fun p => p.1 - p.2)).filter (· ∈ T)

theorem mem_meetingCenters {H : Type*} [DecidableEq H] [AddCommGroup H]
    (F box : Finset H) (T : Set H) (t : H) :
    t ∈ meetingCenters F box T ↔
      t ∈ T ∧ ∃ z ∈ box, z ∈ translate t F := by
  classical
  constructor
  · intro h
    obtain ⟨himage, ht⟩ := Finset.mem_filter.mp h
    obtain ⟨⟨z, a⟩, hp, hza⟩ := Finset.mem_image.mp himage
    obtain ⟨hz, ha⟩ := Finset.mem_product.mp hp
    refine ⟨ht, z, hz, Finset.mem_image.mpr ⟨a, ha, ?_⟩⟩
    rw [← hza, sub_add_cancel]
  · rintro ⟨ht, z, hz, hzt⟩
    obtain ⟨a, ha, hza⟩ := Finset.mem_image.mp hzt
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(z, a), Finset.mem_product.mpr ⟨hz, ha⟩, ?_⟩, ht⟩
    rw [← hza, add_sub_cancel_right]

theorem unique_center_of_direct_tiling
    {H : Type*} [DecidableEq H] [AddCommGroup H]
    (F : Finset H) (T : Set H)
    (tiling : ∀ z : H, ∃! p : F × T, p.1.val + p.2.val = z) (z : H) :
    ∃! t : H, t ∈ T ∧ z ∈ translate t F := by
  obtain ⟨p, hp, hunique⟩ := tiling z
  refine ⟨p.2.val, ⟨p.2.property,
    Finset.mem_image.mpr ⟨p.1.val, p.1.property, (add_comm _ _).trans hp⟩⟩, ?_⟩
  rintro t ⟨ht, hzt⟩
  obtain ⟨a, ha, haz⟩ := Finset.mem_image.mp hzt
  have heq : (⟨a, ha⟩, ⟨t, ht⟩) = p :=
    hunique (⟨a, ha⟩, ⟨t, ht⟩) ((add_comm _ _).trans haz)
  exact congrArg (fun q : F × T => q.2.val) heq

theorem translates_pairwise_disjoint
    {H : Type*} [DecidableEq H] [AddCommGroup H]
    (F : Finset H) (T : Set H)
    (tiling : ∀ z : H, ∃! p : F × T, p.1.val + p.2.val = z) :
    T.PairwiseDisjoint (fun t => translate t F) := by
  intro t ht u hu htu
  apply Finset.disjoint_left.mpr
  intro z hzt hzu
  obtain ⟨v, _, hunique⟩ := unique_center_of_direct_tiling F T tiling z
  exact htu ((hunique t ⟨ht, hzt⟩).trans (hunique u ⟨hu, hzu⟩).symm)

def DirectTiling {G : Type*} [DecidableEq G] [Add G] (A B : Finset G) : Prop :=
  ∀ g : G, ∃! p : G × G, p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = g

/-- Exact local periodic membership and a partition of one representative
cell descend to a direct tiling of the quotient. The full block-to-lattice
bridge is not among the assumptions. -/
theorem local_partition_descends
    {H G : Type*} [DecidableEq H] [DecidableEq G]
    [AddCommGroup H] [AddCommGroup G]
    (π : H →+ G) (A : Finset G) (F cell centers : Finset H)
    (representatives : ∀ g : G, ∃ z ∈ cell, π z = g)
    (partition : ∀ z ∈ cell, ∃! t : H, t ∈ centers ∧ z ∈ translate t F)
    (periodic : ∀ t ∈ centers, ∀ z ∈ cell,
      z ∈ translate t F ↔ π (z - t) ∈ A) :
    DirectTiling A (centers.image π) := by
  intro g
  obtain ⟨z, hz, hπz⟩ := representatives g
  obtain ⟨t, ⟨ht, hzt⟩, hunique⟩ := partition z hz
  have ha : g - π t ∈ A := by
    have h := (periodic t ht z hz).mp hzt
    simpa only [map_sub, hπz] using h
  refine ⟨(g - π t, π t), ⟨ha, Finset.mem_image.mpr ⟨t, ht, rfl⟩,
    sub_add_cancel g (π t)⟩, ?_⟩
  intro p hp
  obtain ⟨t', ht', hπt'⟩ := Finset.mem_image.mp hp.2.1
  have hresidue : π (z - t') = p.1 := by
    rw [map_sub, hπz, hπt']
    exact sub_eq_iff_eq_add.mpr hp.2.2.symm
  have hzt' : z ∈ translate t' F :=
    (periodic t' ht' z hz).mpr (hresidue.symm ▸ hp.1)
  have htt' : t' = t := hunique t' ⟨ht', hzt'⟩
  have hp₂ : p.2 = π t := by simpa only [htt'] using hπt'.symm
  apply Prod.ext
  · exact (sub_eq_iff_eq_add.mpr hp.2.2.symm).symm.trans
      (congrArg (g - ·) hp₂)
  · exact hp₂

/-- Keep the observation size symbolic while normalizing the quadratic. -/
theorem counting_square_gap_of_large
    (a k n₁ n₂ N : ℤ) (ha : 0 < a) (hk : 0 < k)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hgap : 8 * n₁ * n₂ < a * k)
    (hN₁ : 1 ≤ N)
    (hlarge : (a * k + 16 * k * n₁ * n₂) * (n₁ + n₂) +
      32 * (k * n₁ * n₂) ^ 2 + 1 ≤ N) :
    8 * n₁ * n₂ * (N + 2 * k * n₁) * (N + 2 * k * n₂) <
      a * k * (N - n₁) * (N - n₂) := by
  let D := (a * k + 16 * k * n₁ * n₂) * (n₁ + n₂)
  let C := 32 * (k * n₁ * n₂) ^ 2
  have hak : 0 ≤ a * k := (mul_pos ha hk).le
  have hC : 0 ≤ C := mul_nonneg (by decide) (sq_nonneg _)
  have hN : D + C + 1 ≤ N := hlarge
  have hintegergap : 1 ≤ a * k - 8 * n₁ * n₂ := by omega
  have hquadratic : C < N ^ 2 - D * N := by
    have h₁ := mul_nonneg (show 0 ≤ N - D - C - 1 by linarith)
      (show 0 ≤ N by linarith)
    have h₂ := mul_nonneg hC (show 0 ≤ N - 1 by linarith)
    nlinarith
  have hgain := mul_nonneg (show 0 ≤ a * k - 8 * n₁ * n₂ - 1 by linarith)
    (sq_nonneg N)
  have hconstant : 0 ≤ a * k * n₁ * n₂ :=
    mul_nonneg (mul_nonneg hak hn₁.le) hn₂.le
  have hidentity :
      a * k * (N - n₁) * (N - n₂) -
        8 * n₁ * n₂ * (N + 2 * k * n₁) * (N + 2 * k * n₂) =
      (a * k - 8 * n₁ * n₂) * N ^ 2 - D * N + a * k * n₁ * n₂ - C := by
    dsimp [D, C]
    ring
  nlinarith [hidentity]

/-- The large observation square can be chosen explicitly. This replaces
the asymptotic step in the boundary-counting argument by integer arithmetic. -/
theorem exists_large_counting_square
    (a k n₁ n₂ : ℤ) (ha : 0 < a) (hk : 0 < k)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hgap : 8 * n₁ * n₂ < a * k) :
    ∃ N : ℤ, k * n₁ < N ∧ k * n₂ < N ∧
      8 * n₁ * n₂ * (N + 2 * k * n₁) * (N + 2 * k * n₂) <
        a * k * (N - n₁) * (N - n₂) := by
  let D := (a * k + 16 * k * n₁ * n₂) * (n₁ + n₂)
  let C := 32 * (k * n₁ * n₂) ^ 2
  let N := D + C + k * n₁ + k * n₂ + n₁ + n₂ + 1
  have hak : 0 ≤ a * k := (mul_pos ha hk).le
  have hkn₁ : 0 ≤ k * n₁ := (mul_pos hk hn₁).le
  have hkn₂ : 0 ≤ k * n₂ := (mul_pos hk hn₂).le
  have hkn₁n₂ : 0 ≤ k * n₁ * n₂ := mul_nonneg hkn₁ hn₂.le
  have hD : 0 ≤ D := by
    exact mul_nonneg (add_nonneg hak (by nlinarith [hkn₁n₂]))
      (add_nonneg hn₁.le hn₂.le)
  have hC : 0 ≤ C := mul_nonneg (by decide) (sq_nonneg _)
  have hN : D + C + 1 ≤ N := by dsimp [N]; linarith
  have hN₁ : 1 ≤ N := by linarith
  have hbig₁ : k * n₁ < N := by dsimp [N]; linarith
  have hbig₂ : k * n₂ < N := by dsimp [N]; linarith
  exact ⟨N, hbig₁, hbig₂, counting_square_gap_of_large a k n₁ n₂ N ha hk
    hn₁ hn₂ hgap hN₁ hN⟩

abbrev Point := ℤ × ℤ

def rectangle (lo hi : Point) : Finset Point :=
  Finset.Ico lo.1 hi.1 ×ˢ Finset.Ico lo.2 hi.2

theorem mem_rectangle (lo hi x : Point) :
    x ∈ rectangle lo hi ↔
      lo.1 ≤ x.1 ∧ x.1 < hi.1 ∧ lo.2 ≤ x.2 ∧ x.2 < hi.2 := by
  simp only [rectangle, Finset.mem_product, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨h₁, h₂, h₃, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩

theorem card_rectangle (lo hi : Point) (h₁ : lo.1 ≤ hi.1) (h₂ : lo.2 ≤ hi.2) :
    ((rectangle lo hi).card : ℤ) = (hi.1 - lo.1) * (hi.2 - lo.2) := by
  rw [rectangle, Finset.card_product, Nat.cast_mul,
    Int.card_Ico_of_le _ _ h₁, Int.card_Ico_of_le _ _ h₂]

def boundaryRing (n₁ n₂ k : ℤ) : Finset Point :=
  rectangle (-n₁, -n₂) ((k + 1) * n₁, (k + 1) * n₂) \
    rectangle (n₁, n₂) ((k - 1) * n₁, (k - 1) * n₂)

theorem card_boundaryRing (n₁ n₂ k : ℤ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hk : 2 ≤ k) : ((boundaryRing n₁ n₂ k).card : ℤ) = 8 * k * n₁ * n₂ := by
  have hsubset : rectangle (n₁, n₂) ((k - 1) * n₁, (k - 1) * n₂) ⊆
      rectangle (-n₁, -n₂) ((k + 1) * n₁, (k + 1) * n₂) := by
    intro z hz
    have hz' := (mem_rectangle _ _ _).mp hz
    apply (mem_rectangle _ _ _).mpr
    constructor
    · linarith [hz'.1]
    constructor
    · nlinarith [hz'.2.1]
    constructor
    · linarith [hz'.2.2.1]
    · nlinarith [hz'.2.2.2]
  have houter₁ : -n₁ ≤ (k + 1) * n₁ := by
    nlinarith [mul_nonneg (show 0 ≤ k + 2 by omega) hn₁.le]
  have houter₂ : -n₂ ≤ (k + 1) * n₂ := by
    nlinarith [mul_nonneg (show 0 ≤ k + 2 by omega) hn₂.le]
  have hinner₁ : n₁ ≤ (k - 1) * n₁ := by
    nlinarith [mul_nonneg (show 0 ≤ k - 2 by omega) hn₁.le]
  have hinner₂ : n₂ ≤ (k - 1) * n₂ := by
    nlinarith [mul_nonneg (show 0 ≤ k - 2 by omega) hn₂.le]
  have hcard := congrArg (fun n : ℕ => (n : ℤ))
    (Finset.card_sdiff_add_card_eq_card hsubset)
  simp only [Nat.cast_add] at hcard
  rw [card_rectangle (-n₁, -n₂) ((k + 1) * n₁, (k + 1) * n₂) houter₁ houter₂,
    card_rectangle (n₁, n₂) ((k - 1) * n₁, (k - 1) * n₂) hinner₁ hinner₂] at hcard
  change ((boundaryRing n₁ n₂ k).card : ℤ) + _ = _ at hcard
  nlinarith [hcard]

/-- Every block tile that meets an observation square is inside the square
expanded by one block width in each coordinate. -/
theorem block_translate_contained_of_meeting
    (F : Finset Point) (n₁ n₂ k N : ℤ) (v : Point)
    (shape : F ⊆ rectangle (0, 0) (k * n₁, k * n₂))
    (meeting : ∃ z ∈ rectangle (0, 0) (N, N), z ∈ translate v F) :
    translate v F ⊆
      rectangle (-k * n₁, -k * n₂) (N + k * n₁, N + k * n₂) := by
  obtain ⟨z, hz, hzv⟩ := meeting
  obtain ⟨a, ha, hza⟩ := Finset.mem_image.mp hzv
  have hz' := (mem_rectangle _ _ _).mp hz
  have ha' := (mem_rectangle _ _ _).mp (shape ha)
  have heq₁ : v.1 + a.1 = z.1 := congrArg Prod.fst hza
  have heq₂ : v.2 + a.2 = z.2 := congrArg Prod.snd hza
  intro w hw
  obtain ⟨b, hb, hwb⟩ := Finset.mem_image.mp hw
  have hb' := (mem_rectangle _ _ _).mp (shape hb)
  have hw₁ : v.1 + b.1 = w.1 := congrArg Prod.fst hwb
  have hw₂ : v.2 + b.2 = w.2 := congrArg Prod.snd hwb
  apply (mem_rectangle _ _ _).mpr
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The finite center count is derived from the real lattice tiling
partition, rather than supplied as a separate assumption. -/
theorem block_tiling_meeting_card_bound
    (F : Finset Point) (T : Set Point) (n₁ n₂ k N : ℤ)
    (shape : F ⊆ rectangle (0, 0) (k * n₁, k * n₂))
    (tiling : ∀ z : Point, ∃! p : F × T, p.1.val + p.2.val = z) :
    (meetingCenters F (rectangle (0, 0) (N, N)) T).card * F.card ≤
      (rectangle (-k * n₁, -k * n₂) (N + k * n₁, N + k * n₂)).card := by
  apply packed_translates_card_le
  · intro t ht u hu htu
    exact translates_pairwise_disjoint F T tiling
      ((mem_meetingCenters F _ T t).mp ht).1
      ((mem_meetingCenters F _ T u).mp hu).1 htu
  · intro v hv
    exact block_translate_contained_of_meeting F n₁ n₂ k N v shape
      ((mem_meetingCenters F _ T v).mp hv).2

def gridOrigin (n₁ n₂ : ℤ) (j : ℕ × ℕ) : Point :=
  ((j.1 : ℤ) * n₁, (j.2 : ℤ) * n₂)

theorem coordinate_cell_index_unique (n i j z : ℤ) (hn : 0 < n)
    (hi : 0 ≤ z - i * n ∧ z - i * n < n)
    (hj : 0 ≤ z - j * n ∧ z - j * n < n) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hm := mul_le_mul_of_nonneg_right (show i + 1 ≤ j by omega) hn.le
    nlinarith
  · exact h
  · have hm := mul_le_mul_of_nonneg_right (show j + 1 ≤ i by omega) hn.le
    nlinarith

theorem grid_cell_indices_unique (n₁ n₂ : ℤ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (i j : ℕ × ℕ) (z : Point)
    (hi : z ∈ translate (gridOrigin n₁ n₂ i) (rectangle (0, 0) (n₁, n₂)))
    (hj : z ∈ translate (gridOrigin n₁ n₂ j) (rectangle (0, 0) (n₁, n₂))) : i = j := by
  have hi' := (mem_rectangle _ _ _).mp ((mem_translate _ _ _).mp hi)
  have hj' := (mem_rectangle _ _ _).mp ((mem_translate _ _ _).mp hj)
  have h₁ := coordinate_cell_index_unique n₁ i.1 j.1 z.1 hn₁
    ⟨hi'.1, hi'.2.1⟩ ⟨hj'.1, hj'.2.1⟩
  have h₂ := coordinate_cell_index_unique n₂ i.2 j.2 z.2 hn₂
    ⟨hi'.2.2.1, hi'.2.2.2⟩ ⟨hj'.2.2.1, hj'.2.2.2⟩
  exact Prod.ext (Int.ofNat_inj.mp h₁) (Int.ofNat_inj.mp h₂)

theorem grid_cell_inside_block (n₁ n₂ k : ℤ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hk : 0 ≤ k) (j : ℕ × ℕ)
    (hj : j ∈ Finset.range k.toNat ×ˢ Finset.range k.toNat) :
    translate (gridOrigin n₁ n₂ j) (rectangle (0, 0) (n₁, n₂)) ⊆
      rectangle (0, 0) (k * n₁, k * n₂) := by
  obtain ⟨hj₁, hj₂⟩ := Finset.mem_product.mp hj
  have hj₁' : (j.1 : ℤ) < k := by
    simpa only [Int.toNat_of_nonneg hk] using (Int.ofNat_lt.mpr (Finset.mem_range.mp hj₁))
  have hj₂' : (j.2 : ℤ) < k := by
    simpa only [Int.toNat_of_nonneg hk] using (Int.ofNat_lt.mpr (Finset.mem_range.mp hj₂))
  have hm₁ := mul_le_mul_of_nonneg_right (show (j.1 : ℤ) + 1 ≤ k by omega) hn₁.le
  have hm₂ := mul_le_mul_of_nonneg_right (show (j.2 : ℤ) + 1 ≤ k by omega) hn₂.le
  have hl₁ := mul_nonneg (Int.natCast_nonneg j.1) hn₁.le
  have hl₂ := mul_nonneg (Int.natCast_nonneg j.2) hn₂.le
  intro z hz
  have hz' := (mem_rectangle _ _ _).mp ((mem_translate _ _ _).mp hz)
  apply (mem_rectangle _ _ _).mpr
  change 0 ≤ z.1 ∧ z.1 < k * n₁ ∧ 0 ≤ z.2 ∧ z.2 < k * n₂
  dsimp only [gridOrigin] at hz'
  change 0 ≤ z.1 - (j.1 : ℤ) * n₁ ∧ z.1 - (j.1 : ℤ) * n₁ < n₁ ∧
    0 ≤ z.2 - (j.2 : ℤ) * n₂ ∧ z.2 - (j.2 : ℤ) * n₂ < n₂ at hz'
  constructor
  · linarith [hz'.1]
  constructor
  · nlinarith [hz'.2.1]
  constructor
  · linarith [hz'.2.2.1]
  · nlinarith [hz'.2.2.2]

/-- Surjectivity of every small representative cell supplies the required
block-cardinality lower bound; no equality or uniform fiber size is assumed. -/
theorem periodic_block_card_lower
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    (π : Point →+ G) (A : Finset G) (F : Finset Point)
    (n₁ n₂ k : ℤ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hk : 0 ≤ k)
    (periodic : ∀ z : Point, z ∈ F ↔
      z ∈ rectangle (0, 0) (k * n₁, k * n₂) ∧ π z ∈ A)
    (representatives : ∀ x : Point, ∀ g : G,
      ∃ z ∈ translate x (rectangle (0, 0) (n₁, n₂)), π z = g) :
    (A.card : ℤ) * k ^ 2 ≤ (F.card : ℤ) := by
  classical
  let lift : (ℕ × ℕ) × G → Point := fun p =>
    Classical.choose (representatives (gridOrigin n₁ n₂ p.1) p.2)
  have hlift (p : (ℕ × ℕ) × G) :
      lift p ∈ translate (gridOrigin n₁ n₂ p.1) (rectangle (0, 0) (n₁, n₂)) ∧
      π (lift p) = p.2 := Classical.choose_spec
        (representatives (gridOrigin n₁ n₂ p.1) p.2)
  let domain := (Finset.range k.toNat ×ˢ Finset.range k.toNat) ×ˢ A
  have hmaps : Set.MapsTo lift domain F := by
    intro p hp
    obtain ⟨hj, ha⟩ := Finset.mem_product.mp hp
    apply (periodic (lift p)).mpr
    exact ⟨grid_cell_inside_block n₁ n₂ k hn₁ hn₂ hk p.1 hj (hlift p).1,
      (hlift p).2.symm ▸ ha⟩
  have hinj : Set.InjOn lift domain := by
    intro p _ q _ hpq
    have hindex : p.1 = q.1 := grid_cell_indices_unique n₁ n₂ hn₁ hn₂ p.1 q.1
      (lift p) (hlift p).1 (hpq.symm ▸ (hlift q).1)
    have hresidue : p.2 = q.2 := (hlift p).2.symm.trans
      ((congrArg π hpq).trans (hlift q).2)
    exact Prod.ext hindex hresidue
  have hcard := Finset.card_le_card_of_injOn lift hmaps hinj
  have hcardZ := Int.ofNat_le.mpr hcard
  dsimp only [domain] at hcardZ
  simp only [Finset.card_product, Finset.card_range, Nat.cast_mul,
    Int.toNat_of_nonneg hk] at hcardZ
  nlinarith [hcardZ]

/-- Quantitative finite counting supplies a complete small observation cell
whose origin avoids all the block-tile boundary rings that can affect it. -/
theorem exists_ring_avoiding_origin
    (F : Finset Point) (T : Set Point) (a n₁ n₂ k : ℤ)
    (ha : 0 < a) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hk : 3 ≤ k)
    (hgap : 8 * n₁ * n₂ < a * k)
    (shape : F ⊆ rectangle (0, 0) (k * n₁, k * n₂))
    (cardinality : a * k ^ 2 ≤ (F.card : ℤ))
    (tiling : ∀ z : Point, ∃! p : F × T, p.1.val + p.2.val = z) :
    ∃ N : ℤ, ∃ x ∈ rectangle (0, 0) (N - n₁, N - n₂),
      ∀ v ∈ meetingCenters F (rectangle (0, 0) (N, N)) T,
        x ∉ translate v (boundaryRing n₁ n₂ k) := by
  have hkpos : 0 < k := by omega
  obtain ⟨N, hN₁, hN₂, hNvolume⟩ :=
    exists_large_counting_square a k n₁ n₂ ha hkpos hn₁ hn₂ hgap
  have hkn₁ : 0 < k * n₁ := mul_pos hkpos hn₁
  have hkn₂ : 0 < k * n₂ := mul_pos hkpos hn₂
  have hn₁N : n₁ < N := by
    nlinarith [mul_nonneg (show 0 ≤ k - 1 by omega) hn₁.le]
  have hn₂N : n₂ < N := by
    nlinarith [mul_nonneg (show 0 ≤ k - 1 by omega) hn₂.le]
  have hpacked := block_tiling_meeting_card_bound F T n₁ n₂ k N shape tiling
  have hpackedZ := Int.ofNat_le.mpr hpacked
  rw [Nat.cast_mul,
    card_rectangle (-k * n₁, -k * n₂) (N + k * n₁, N + k * n₂)
      (by dsimp; linarith) (by dsimp; linarith)] at hpackedZ
  have hlower := mul_le_mul_of_nonneg_left cardinality
    (Int.natCast_nonneg (meetingCenters F (rectangle (0, 0) (N, N)) T).card)
  have hpackedLower := hlower.trans hpackedZ
  have htarget := card_rectangle (0, 0) (N - n₁, N - n₂)
    (by dsimp; linarith) (by dsimp; linarith)
  have hring := card_boundaryRing n₁ n₂ k hn₁ hn₂ (by omega)
  have hscaled := mul_le_mul_of_nonneg_left hpackedLower
    (show 0 ≤ 8 * n₁ * n₂ by nlinarith [mul_pos hn₁ hn₂])
  have hstrict :
      ((meetingCenters F (rectangle (0, 0) (N, N)) T).card : ℤ) *
        ((boundaryRing n₁ n₂ k).card : ℤ) * (a * k) <
      ((rectangle (0, 0) (N - n₁, N - n₂)).card : ℤ) * (a * k) := by
    rw [hring, htarget]
    nlinarith [hscaled, hNvolume]
  have hstrictZ := lt_of_mul_lt_mul_right hstrict (mul_pos ha hkpos).le
  have hstrictNat :
      (meetingCenters F (rectangle (0, 0) (N, N)) T).card *
        (boundaryRing n₁ n₂ k).card <
      (rectangle (0, 0) (N - n₁, N - n₂)).card := by
    apply Int.ofNat_lt.mp
    simpa only [Nat.cast_mul] using hstrictZ
  obtain ⟨x, hx, hav⟩ := exists_avoiding_translates _ _ _ hstrictNat
  exact ⟨N, x, hx, hav⟩

/-- A unit-cell-sized observation box meeting a block and avoiding its ring
is wholly inside the block. The hypothesis is actual pointwise overlap. -/
theorem observation_box_inside_block
    (n₁ n₂ k : ℤ) (x v : Point) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (overlap : ∃ z ∈ translate x (rectangle (0, 0) (n₁, n₂)),
      z ∈ translate v (rectangle (0, 0) (k * n₁, k * n₂)))
    (avoids : x ∉ translate v (boundaryRing n₁ n₂ k)) :
    translate x (rectangle (0, 0) (n₁, n₂)) ⊆
      translate v (rectangle (0, 0) (k * n₁, k * n₂)) := by
  obtain ⟨z, hz₁, hz₂⟩ := overlap
  obtain ⟨a, ha, hza⟩ := Finset.mem_image.mp hz₁
  obtain ⟨b, hb, hzb⟩ := Finset.mem_image.mp hz₂
  have ha' := (mem_rectangle (0, 0) (n₁, n₂) a).mp ha
  have hb' := (mem_rectangle (0, 0) (k * n₁, k * n₂) b).mp hb
  have heq : x + a = v + b := hza.trans hzb.symm
  have heq₁ : x.1 + a.1 = v.1 + b.1 := congrArg Prod.fst heq
  have heq₂ : x.2 + a.2 = v.2 + b.2 := congrArg Prod.snd heq
  have hout : x - v ∈
      rectangle (-n₁, -n₂) ((k + 1) * n₁, (k + 1) * n₂) := by
    apply (mem_rectangle _ _ _).mpr
    change -n₁ ≤ x.1 - v.1 ∧ x.1 - v.1 < (k + 1) * n₁ ∧
      -n₂ ≤ x.2 - v.2 ∧ x.2 - v.2 < (k + 1) * n₂
    constructor
    · omega
    constructor
    · nlinarith
    constructor
    · omega
    · nlinarith
  have hinner : x - v ∈ rectangle (n₁, n₂) ((k - 1) * n₁, (k - 1) * n₂) := by
    by_contra h
    apply avoids
    apply Finset.mem_image.mpr
    refine ⟨x - v, Finset.mem_sdiff.mpr ⟨hout, h⟩, ?_⟩
    rw [add_comm, sub_add_cancel]
  have hx' := (mem_rectangle _ _ _).mp hinner
  intro w hw
  obtain ⟨c, hc, hwc⟩ := Finset.mem_image.mp hw
  have hc' := (mem_rectangle (0, 0) (n₁, n₂) c).mp hc
  apply Finset.mem_image.mpr
  refine ⟨x - v + c, ?_, ?_⟩
  · apply (mem_rectangle _ _ _).mpr
    change n₁ ≤ x.1 - v.1 ∧ x.1 - v.1 < (k - 1) * n₁ ∧
      n₂ ≤ x.2 - v.2 ∧ x.2 - v.2 < (k - 1) * n₂ at hx'
    change 0 ≤ x.1 - v.1 + c.1 ∧ x.1 - v.1 + c.1 < k * n₁ ∧
      0 ≤ x.2 - v.2 + c.2 ∧ x.2 - v.2 + c.2 < k * n₂
    constructor
    · omega
    constructor
    · nlinarith
    constructor
    · omega
    · nlinarith
  · calc
      v + (x - v + c) = (v + (x - v)) + c := (add_assoc _ _ _).symm
      _ = x + c := by rw [add_comm v, sub_add_cancel]
      _ = w := hwc

/-- The complete finite-counting and local-descent argument. The remaining
construction inputs are the cardinality of the periodic block and the
representative property of the rectangular quotient cell. -/
theorem rectangular_tiling_descent
    {G : Type*} [DecidableEq G] [AddCommGroup G]
    (π : Point →+ G) (A : Finset G) (F : Finset Point)
    (T : Set Point) (n₁ n₂ k : ℤ)
    (hA : 0 < (A.card : ℤ)) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hk : 3 ≤ k)
    (hgap : 8 * n₁ * n₂ < (A.card : ℤ) * k)
    (cardinality : (A.card : ℤ) * k ^ 2 ≤ (F.card : ℤ))
    (periodic : ∀ z : Point, z ∈ F ↔
      z ∈ rectangle (0, 0) (k * n₁, k * n₂) ∧ π z ∈ A)
    (representatives : ∀ x : Point, ∀ g : G,
      ∃ z ∈ translate x (rectangle (0, 0) (n₁, n₂)), π z = g)
    (tiling : ∀ z : Point, ∃! p : F × T, p.1.val + p.2.val = z) :
    ∃ B : Finset G, DirectTiling A B := by
  classical
  have shape : F ⊆ rectangle (0, 0) (k * n₁, k * n₂) :=
    fun z hz => ((periodic z).mp hz).1
  obtain ⟨N, x, hx, hav⟩ := exists_ring_avoiding_origin F T A.card n₁ n₂ k
    hA hn₁ hn₂ hk hgap shape cardinality tiling
  let cell := translate x (rectangle (0, 0) (n₁, n₂))
  let centers := meetingCenters F cell T
  have hcell : cell ⊆ rectangle (0, 0) (N, N) := by
    intro z hz
    obtain ⟨c, hc, hcz⟩ := Finset.mem_image.mp hz
    have hx' := (mem_rectangle _ _ _).mp hx
    have hc' := (mem_rectangle _ _ _).mp hc
    have hz₁ : x.1 + c.1 = z.1 := congrArg Prod.fst hcz
    have hz₂ : x.2 + c.2 = z.2 := congrArg Prod.snd hcz
    apply (mem_rectangle _ _ _).mpr
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  have hcenters : centers ⊆ meetingCenters F (rectangle (0, 0) (N, N)) T := by
    intro v hv
    obtain ⟨hvT, z, hz, hzv⟩ := (mem_meetingCenters F cell T v).mp hv
    exact (mem_meetingCenters F _ T v).mpr ⟨hvT, z, hcell hz, hzv⟩
  have hcontained (v : Point) (hv : v ∈ centers) :
      cell ⊆ translate v (rectangle (0, 0) (k * n₁, k * n₂)) := by
    obtain ⟨_, z, hz, hzv⟩ := (mem_meetingCenters F cell T v).mp hv
    apply observation_box_inside_block n₁ n₂ k x v hn₁ hn₂
    · refine ⟨z, hz, ?_⟩
      obtain ⟨a, ha, hza⟩ := Finset.mem_image.mp hzv
      exact Finset.mem_image.mpr ⟨a, shape ha, hza⟩
    · exact hav v (hcenters hv)
  have hpartition : ∀ z ∈ cell, ∃! v : Point,
      v ∈ centers ∧ z ∈ translate v F := by
    intro z hz
    obtain ⟨v, ⟨hvT, hzv⟩, hunique⟩ := unique_center_of_direct_tiling F T tiling z
    refine ⟨v, ⟨(mem_meetingCenters F cell T v).mpr ⟨hvT, z, hz, hzv⟩, hzv⟩, ?_⟩
    intro u hu
    exact hunique u ⟨((mem_meetingCenters F cell T u).mp hu.1).1, hu.2⟩
  have hperiodic : ∀ v ∈ centers, ∀ z ∈ cell,
      z ∈ translate v F ↔ π (z - v) ∈ A := by
    intro v hv z hz
    have hblock : z - v ∈ rectangle (0, 0) (k * n₁, k * n₂) :=
      (mem_translate v z _).mp (hcontained v hv hz)
    constructor
    · intro h
      exact ((periodic (z - v)).mp ((mem_translate v z F).mp h)).2
    · intro h
      exact (mem_translate v z F).mpr ((periodic (z - v)).mpr ⟨hblock, h⟩)
  exact ⟨centers.image π,
    local_partition_descends π A F cell centers (representatives x) hpartition hperiodic⟩

def quotientMap (n₁ n₂ : ℕ) : Point →+ (ZMod n₁ × ZMod n₂) where
  toFun z := ((z.1 : ZMod n₁), (z.2 : ZMod n₂))
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp

theorem coordinate_representative (n : ℕ) [NeZero n] (x : ℤ) (g : ZMod n) :
    ∃ z ∈ Finset.Ico x (x + n), (z : ZMod n) = g := by
  have hval : (g.val : ℤ) ∈ Finset.Ico 0 (n : ℤ) :=
    Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (ZMod.val_lt g)⟩
  have hmod : (g.val : ℤ) ∈ (Finset.Ico x (x + n)).image (fun z => z % (n : ℤ)) := by
    rw [Int.image_Ico_emod x (n : ℤ) (Int.natCast_nonneg n)]
    exact hval
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hmod
  refine ⟨z, hz, ?_⟩
  calc
    (z : ZMod n) = ((z % (n : ℤ) : ℤ) : ZMod n) := (ZMod.intCast_mod z n).symm
    _ = ((g.val : ℤ) : ZMod n) := congrArg (fun z : ℤ => (z : ZMod n)) heq
    _ = g := by simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val g

theorem quotient_cell_representatives (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (x : Point) (g : ZMod n₁ × ZMod n₂) :
    ∃ z ∈ translate x (rectangle (0, 0) (n₁, n₂)), quotientMap n₁ n₂ z = g := by
  obtain ⟨z₁, hz₁, hg₁⟩ := coordinate_representative n₁ x.1 g.1
  obtain ⟨z₂, hz₂, hg₂⟩ := coordinate_representative n₂ x.2 g.2
  refine ⟨(z₁, z₂), (mem_translate _ _ _).mpr ?_, Prod.ext hg₁ hg₂⟩
  apply (mem_rectangle _ _ _).mpr
  obtain ⟨hl₁, hu₁⟩ := Finset.mem_Ico.mp hz₁
  obtain ⟨hl₂, hu₂⟩ := Finset.mem_Ico.mp hz₂
  change 0 ≤ z₁ - x.1 ∧ z₁ - x.1 < n₁ ∧ 0 ≤ z₂ - x.2 ∧ z₂ - x.2 < n₂
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The rectangular periodic block is the set described in equation (3)
of the source, equivalently by its quotient residues inside the large box. -/
def latticeBlock (n₁ n₂ k : ℕ) (A : Finset (ZMod n₁ × ZMod n₂)) : Finset Point :=
  (rectangle (0, 0) ((k : ℤ) * n₁, (k : ℤ) * n₂)).filter
    (fun z => quotientMap n₁ n₂ z ∈ A)

def representative {n₁ n₂ : ℕ} (a : ZMod n₁ × ZMod n₂) : Point :=
  (a.1.val, a.2.val)

/-- The original block construction: canonical representatives of A plus
the k by k grid of period vectors. -/
def blockCopies (n₁ n₂ k : ℕ) (A : Finset (ZMod n₁ × ZMod n₂)) : Finset Point :=
  ((Finset.range k ×ˢ Finset.range k) ×ˢ A).image
    (fun p => gridOrigin n₁ n₂ p.1 + representative p.2)

theorem coordinate_block_decomposition (n k : ℕ) [NeZero n] (hn : 0 < n)
    (z : ℤ) (a : ZMod n) (hz : 0 ≤ z ∧ z < (k : ℤ) * n)
    (ha : (z : ZMod n) = a) :
    ∃ j ∈ Finset.range k, z = (a.val : ℤ) + (j : ℤ) * n := by
  obtain ⟨j, hj⟩ := (ZMod.intCast_eq_iff n z a).mp ha
  have hnZ : 0 < (n : ℤ) := Int.ofNat_lt.mpr hn
  have hval₀ : 0 ≤ (a.val : ℤ) := Int.natCast_nonneg _
  have hvaln : (a.val : ℤ) < n := Int.ofNat_lt.mpr (ZMod.val_lt a)
  have hj₀ : 0 ≤ j := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show j ≤ -1 by omega) hnZ.le
    nlinarith
  have hjk : j < k := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_left (show (k : ℤ) ≤ j by omega) hnZ.le
    nlinarith
  refine ⟨j.toNat, Finset.mem_range.mpr ?_, ?_⟩
  · apply Int.ofNat_lt.mp
    simpa only [Int.toNat_of_nonneg hj₀] using hjk
  · rw [Int.toNat_of_nonneg hj₀]
    nlinarith [hj]

/-- The quotient-membership block is exactly the original finite grid
construction, rather than an unrelated periodic approximation. -/
theorem blockCopies_eq_latticeBlock (n₁ n₂ k : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (A : Finset (ZMod n₁ × ZMod n₂)) :
    blockCopies n₁ n₂ k A = latticeBlock n₁ n₂ k A := by
  classical
  let _ : NeZero n₁ := ⟨Nat.ne_of_gt hn₁⟩
  let _ : NeZero n₂ := ⟨Nat.ne_of_gt hn₂⟩
  ext z
  constructor
  · intro hz
    obtain ⟨⟨j, a⟩, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hj, ha⟩ := Finset.mem_product.mp hp
    have hrepa : representative a ∈ rectangle (0, 0) (n₁, n₂) := by
      apply (mem_rectangle _ _ _).mpr
      exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (ZMod.val_lt a.1),
        Int.natCast_nonneg _, Int.ofNat_lt.mpr (ZMod.val_lt a.2)⟩
    have hcell : gridOrigin n₁ n₂ j + representative a ∈
        translate (gridOrigin n₁ n₂ j) (rectangle (0, 0) (n₁, n₂)) :=
      Finset.mem_image.mpr ⟨representative a, hrepa, rfl⟩
    have hblock := grid_cell_inside_block n₁ n₂ k (Int.ofNat_lt.mpr hn₁)
      (Int.ofNat_lt.mpr hn₂) (Int.natCast_nonneg k) j (by simpa using hj) hcell
    have hquotient : quotientMap n₁ n₂ (gridOrigin n₁ n₂ j + representative a) = a := by
      ext <;> simp [quotientMap, gridOrigin, representative]
    exact Finset.mem_filter.mpr ⟨hblock, hquotient.symm ▸ ha⟩
  · intro hz
    obtain ⟨hzblock, ha⟩ := Finset.mem_filter.mp hz
    have hz' := (mem_rectangle _ _ _).mp hzblock
    let a := quotientMap n₁ n₂ z
    obtain ⟨j₁, hj₁, heq₁⟩ := coordinate_block_decomposition n₁ k hn₁ z.1 a.1
      ⟨hz'.1, hz'.2.1⟩ rfl
    obtain ⟨j₂, hj₂, heq₂⟩ := coordinate_block_decomposition n₂ k hn₂ z.2 a.2
      ⟨hz'.2.2.1, hz'.2.2.2⟩ rfl
    apply Finset.mem_image.mpr
    refine ⟨((j₁, j₂), a), Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hj₁, hj₂⟩, ha⟩, ?_⟩
    apply Prod.ext
    · change (j₁ : ℤ) * n₁ + (a.1.val : ℤ) = z.1
      nlinarith [heq₁]
    · change (j₂ : ℤ) * n₂ + (a.2.val : ℤ) = z.2
      nlinarith [heq₂]

theorem card_blockCopies (n₁ n₂ k : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (A : Finset (ZMod n₁ × ZMod n₂)) :
    (blockCopies n₁ n₂ k A).card = A.card * k ^ 2 := by
  classical
  let _ : NeZero n₁ := ⟨Nat.ne_of_gt hn₁⟩
  let _ : NeZero n₂ := ⟨Nat.ne_of_gt hn₂⟩
  have hrepa (a : ZMod n₁ × ZMod n₂) :
      representative a ∈ rectangle (0, 0) (n₁, n₂) :=
    (mem_rectangle _ _ _).mpr ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (ZMod.val_lt a.1),
      Int.natCast_nonneg _, Int.ofNat_lt.mpr (ZMod.val_lt a.2)⟩
  have hcell (p : (ℕ × ℕ) × (ZMod n₁ × ZMod n₂)) :
      gridOrigin n₁ n₂ p.1 + representative p.2 ∈
        translate (gridOrigin n₁ n₂ p.1) (rectangle (0, 0) (n₁, n₂)) :=
    Finset.mem_image.mpr ⟨representative p.2, hrepa p.2, rfl⟩
  have hquotient (p : (ℕ × ℕ) × (ZMod n₁ × ZMod n₂)) :
      quotientMap n₁ n₂ (gridOrigin n₁ n₂ p.1 + representative p.2) = p.2 := by
    ext <;> simp [quotientMap, gridOrigin, representative]
  have hinj : Function.Injective (fun p : (ℕ × ℕ) × (ZMod n₁ × ZMod n₂) =>
      gridOrigin n₁ n₂ p.1 + representative p.2) := by
    intro p q hpq
    change gridOrigin n₁ n₂ p.1 + representative p.2 =
      gridOrigin n₁ n₂ q.1 + representative q.2 at hpq
    have hqcell : gridOrigin n₁ n₂ p.1 + representative p.2 ∈
        translate (gridOrigin n₁ n₂ q.1) (rectangle (0, 0) (n₁, n₂)) := by
      rw [hpq]
      exact hcell q
    have hindex := grid_cell_indices_unique n₁ n₂ (Int.ofNat_lt.mpr hn₁)
      (Int.ofNat_lt.mpr hn₂) p.1 q.1 _ (hcell p) hqcell
    have hresidue := (hquotient p).symm.trans
      ((congrArg (quotientMap n₁ n₂) hpq).trans (hquotient q))
    exact Prod.ext hindex hresidue
  rw [blockCopies, Finset.card_image_of_injective _ hinj,
    Finset.card_product, Finset.card_product, Finset.card_range]
  ring

/-- Full finite-to-lattice non-tiling transfer for rectangular cyclic groups.
The large block is defined directly by the actual quotient membership. -/
theorem latticeBlock_nontiling
    (n₁ n₂ k : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (A : Finset (ZMod n₁ × ZMod n₂)) (hA : A.Nonempty)
    (hgap : 8 * n₁ * n₂ < A.card * k)
    (nontiling : ¬ ∃ B : Finset (ZMod n₁ × ZMod n₂), DirectTiling A B) :
    ¬ ∃ T : Set Point, ∀ z : Point,
      ∃! p : latticeBlock n₁ n₂ k A × T, p.1.val + p.2.val = z := by
  classical
  let _ : NeZero n₁ := ⟨Nat.ne_of_gt hn₁⟩
  let _ : NeZero n₂ := ⟨Nat.ne_of_gt hn₂⟩
  have hApos : 0 < (A.card : ℤ) := Int.ofNat_lt.mpr (Finset.card_pos.mpr hA)
  have hn₁Z : 0 < (n₁ : ℤ) := Int.ofNat_lt.mpr hn₁
  have hn₂Z : 0 < (n₂ : ℤ) := Int.ofNat_lt.mpr hn₂
  have hgapZ : 8 * (n₁ : ℤ) * n₂ < (A.card : ℤ) * k := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Int.ofNat_lt.mpr hgap
  have hcardA : A.card ≤ n₁ * n₂ := by
    simpa only [Fintype.card_prod, ZMod.card] using Finset.card_le_univ A
  have hcardAZ : (A.card : ℤ) ≤ (n₁ : ℤ) * n₂ := by
    simpa only [Nat.cast_mul] using Int.ofNat_le.mpr hcardA
  have hk : 3 ≤ (k : ℤ) := by
    by_contra h
    have hk₂ : (k : ℤ) ≤ 2 := by omega
    have hm := mul_le_mul_of_nonneg_left hk₂ (Int.natCast_nonneg A.card)
    nlinarith
  have periodic : ∀ z : Point, z ∈ latticeBlock n₁ n₂ k A ↔
      z ∈ rectangle (0, 0) ((k : ℤ) * n₁, (k : ℤ) * n₂) ∧ quotientMap n₁ n₂ z ∈ A := by
    intro z
    exact Finset.mem_filter
  have representatives := quotient_cell_representatives n₁ n₂
  have cardinality := periodic_block_card_lower (quotientMap n₁ n₂) A
    (latticeBlock n₁ n₂ k A) n₁ n₂ k hn₁Z hn₂Z (Int.natCast_nonneg k)
    periodic representatives
  rintro ⟨T, hT⟩
  exact nontiling (rectangular_tiling_descent (quotientMap n₁ n₂) A
    (latticeBlock n₁ n₂ k A) T n₁ n₂ k hApos hn₁Z hn₂Z hk hgapZ
    cardinality periodic representatives hT)

/-- Proposition 2.1(ii), non-tiling direction, for the explicit A[k] grid.
All integer-lattice translation sets are quantified, including infinite ones. -/
theorem blockCopies_nontiling
    (n₁ n₂ k : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (A : Finset (ZMod n₁ × ZMod n₂)) (hA : A.Nonempty)
    (hgap : 8 * n₁ * n₂ < A.card * k)
    (nontiling : ¬ ∃ B : Finset (ZMod n₁ × ZMod n₂), DirectTiling A B) :
    ¬ ∃ T : Set Point, ∀ z : Point,
      ∃! p : blockCopies n₁ n₂ k A × T, p.1.val + p.2.val = z := by
  rw [blockCopies_eq_latticeBlock n₁ n₂ k hn₁ hn₂ A]
  exact latticeBlock_nontiling n₁ n₂ k hn₁ hn₂ A hA hgap nontiling

/-- The quantitative block size used by the 60-point planar construction. -/
theorem sixty_point_block97_nontiling
    (A : Finset (ZMod 60 × ZMod 12)) (cardA : A.card = 60)
    (nontiling : ¬ ∃ B : Finset (ZMod 60 × ZMod 12), DirectTiling A B) :
    ¬ ∃ T : Set Point, ∀ z : Point,
      ∃! p : blockCopies 60 12 97 A × T, p.1.val + p.2.val = z := by
  apply blockCopies_nontiling 60 12 97 (by decide) (by decide) A
  · apply Finset.card_pos.mp
    rw [cardA]
    decide
  · rw [cardA]
    decide
  · exact nontiling

end FugledeTransfer

#print axioms FugledeTransfer.packed_translates_card_le
#print axioms FugledeTransfer.exists_avoiding_translates
#print axioms FugledeTransfer.mem_meetingCenters
#print axioms FugledeTransfer.translates_pairwise_disjoint
#print axioms FugledeTransfer.local_partition_descends
#print axioms FugledeTransfer.exists_large_counting_square
#print axioms FugledeTransfer.card_boundaryRing
#print axioms FugledeTransfer.block_tiling_meeting_card_bound
#print axioms FugledeTransfer.exists_ring_avoiding_origin
#print axioms FugledeTransfer.periodic_block_card_lower
#print axioms FugledeTransfer.observation_box_inside_block
#print axioms FugledeTransfer.rectangular_tiling_descent
#print axioms FugledeTransfer.quotient_cell_representatives
#print axioms FugledeTransfer.latticeBlock_nontiling
#print axioms FugledeTransfer.blockCopies_eq_latticeBlock
#print axioms FugledeTransfer.card_blockCopies
#print axioms FugledeTransfer.blockCopies_nontiling
#print axioms FugledeTransfer.sixty_point_block97_nontiling

#print axioms FugledeTransfer.card_translate
#print axioms FugledeTransfer.mem_translate
#print axioms FugledeTransfer.unique_center_of_direct_tiling
#print axioms FugledeTransfer.counting_square_gap_of_large
#print axioms FugledeTransfer.mem_rectangle
#print axioms FugledeTransfer.card_rectangle
#print axioms FugledeTransfer.block_translate_contained_of_meeting
#print axioms FugledeTransfer.coordinate_cell_index_unique
#print axioms FugledeTransfer.grid_cell_indices_unique
#print axioms FugledeTransfer.grid_cell_inside_block
#print axioms FugledeTransfer.coordinate_representative
#print axioms FugledeTransfer.coordinate_block_decomposition
