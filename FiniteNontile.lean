import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Parity obstruction in Tao Zhang arXiv:2607.15632v1, Proposition4.3.
The Boolean decision below has six input bits (64 possibilities).
This module does not assume a finite nontiling conclusion.
-/
set_option Elab.async false
set_option maxRecDepth 1000000
namespace FugledeNontile
open scoped BigOperators

def rowCard (a : Fin 6 → Bool) : ℕ :=
  (Finset.univ.filter fun s => a s = true).card

def rowEven (a : Fin 6 → Bool) : ℕ :=
  (Finset.univ.filter fun s => a s = true ∧ s.val % 2 = 0).card

def shiftedComplement (a : Fin 6 → Bool) : Fin 6 → Bool :=
  fun s => !(a (s + 3))

lemma row_parity : ∀ a : Fin 6 → Bool,
    rowCard a = 3 → rowEven (shiftedComplement a) = rowEven a := by
  decide +kernel

lemma bool_eq_not_of_ne : ∀ a b : Bool, a ≠ b → a = !b := by
  decide +kernel

/-- Four size-three rows tiling by the step `(1,3)` cannot contain exactly
six even second coordinates. This is the quotient parity contradiction. -/
theorem quotient_parity_obstruction (p : Fin 4 → Fin 6 → Bool)
    (hcard : ∀ r, rowCard (p r) = 3)
    (hstep : ∀ r s, p r s ≠ p (r - 1) (s + 3))
    (heven : ∑ r : Fin 4, rowEven (p r) = 6) : False := by
  have heq (r : Fin 4) : rowEven (p r) = rowEven (p (r - 1)) := by
    have hrow : p r = shiftedComplement (p (r - 1)) := by
      funext s
      exact bool_eq_not_of_ne (p r s) (p (r - 1) (s + 3)) (hstep r s)
    rw [hrow]
    exact row_parity (p (r - 1)) (hcard (r - 1))
  have h10 := heq 1
  have h21 := heq 2
  have h32 := heq 3
  change rowEven (p 1) = rowEven (p 0) at h10
  change rowEven (p 2) = rowEven (p 1) at h21
  change rowEven (p 3) = rowEven (p 2) at h32
  norm_num [Fin.sum_univ_succ] at heven
  omega

abbrev H := Fin 12 × Fin 12
abbrev Q := Fin 4 × Fin 6

def firstMod (x : Fin 12) : Fin 4 := ⟨x.val % 4, Nat.mod_lt _ (by decide)⟩

def phi (x : H) : Q :=
  (firstMod x.1, ⟨(x.1.val + x.2.val) % 6, Nat.mod_lt _ (by decide)⟩)

def diagonal (x : H) : Fin 12 := x.1 - x.2

def rowOf (P : Finset Q) (r : Fin 4) : Fin 6 → Bool := fun s => decide ((r, s) ∈ P)

lemma row_filter_card (P : Finset Q) (r : Fin 4) (b : Fin 6 → Prop) [DecidablePred b] :
    (Finset.univ.filter fun s => (r, s) ∈ P ∧ b s).card =
      (P.filter fun q => q.1 = r ∧ b q.2).card := by
  let S := Finset.univ.filter fun s => (r, s) ∈ P ∧ b s
  have him : S.image (fun s => (r, s)) = P.filter (fun q => q.1 = r ∧ b q.2) := by
    ext ⟨r', s'⟩
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨s, ⟨hp, hb⟩, hr, hs⟩
      subst r'; subst s'
      exact ⟨hp, rfl, hb⟩
    · rintro ⟨hp, hr, hb⟩
      subst r'
      exact ⟨s', ⟨hp, hb⟩, rfl, rfl⟩
  rw [← him]
  exact (Finset.card_image_of_injective S (fun _ _ h => congrArg Prod.snd h)).symm

lemma rowOf_card (P : Finset Q) (r : Fin 4) :
    rowCard (rowOf P r) = (P.filter fun q => q.1 = r).card := by
  simpa [rowCard, rowOf] using row_filter_card P r (fun _ => True)

lemma rowOf_even (P : Finset Q) (r : Fin 4) :
    rowEven (rowOf P r) = (P.filter fun q => q.1 = r ∧ q.2.val % 2 = 0).card := by
  simpa [rowEven, rowOf] using row_filter_card P r (fun s => s.val % 2 = 0)

lemma sum_rowOf_even (P : Finset Q) :
    (∑ r : Fin 4, rowEven (rowOf P r)) = (P.filter fun q => q.2.val % 2 = 0).card := by
  calc
    _ = ∑ r : Fin 4, ((P.filter fun q => q.2.val % 2 = 0).filter fun q => q.1 = r).card := by
      apply Finset.sum_congr rfl
      intro r _
      rw [rowOf_even]
      congr 1
      ext q
      simp [and_comm, and_left_comm, and_assoc]
    _ = _ := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter
        (P.filter fun q => q.2.val % 2 = 0) (Finset.univ : Finset (Fin 4)) Prod.fst

lemma card_filter_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (C : Finset α) (f : α → β) (b : β → Prop) [DecidablePred b]
    (hi : Set.InjOn f (C : Set α)) :
    ((C.image f).filter b).card = (C.filter fun x => b (f x)).card := by
  rw [Finset.filter_image]
  apply Finset.card_image_iff.mpr
  exact hi.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)

lemma firstMod_fiber : ∀ r : Fin 4,
    (Finset.univ.filter fun x : Fin 12 => firstMod x = r).card = 3 := by
  decide +kernel

lemma phi_diagonal_parity : ∀ x : H, (phi x).2.val % 2 = (diagonal x).val % 2 := by
  decide +kernel

/-- These are the quotient row sizes forced by a full first-coordinate projection. -/
lemma projected_row_card (C : Finset H) (hc : C.card = 12)
    (hi : Set.InjOn Prod.fst (C : Set H)) (hphi : Set.InjOn phi (C : Set H))
    (r : Fin 4) : rowCard (rowOf (C.image phi) r) = 3 := by
  have hall : C.image Prod.fst = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_iff.mpr hi, hc]
    simp
  rw [rowOf_card, card_filter_image C phi (fun q => q.1 = r) hphi]
  change (C.filter fun x => firstMod x.1 = r).card = 3
  rw [← card_filter_image C Prod.fst (fun x => firstMod x = r) hi, hall]
  exact firstMod_fiber r

/-- A full diagonal projection forces precisely six even quotient second coordinates. -/
lemma projected_even_card (C : Finset H) (hc : C.card = 12)
    (hi : Set.InjOn diagonal (C : Set H)) (hphi : Set.InjOn phi (C : Set H)) :
    (∑ r : Fin 4, rowEven (rowOf (C.image phi) r)) = 6 := by
  have hall : C.image diagonal = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_iff.mpr hi, hc]
    simp
  rw [sum_rowOf_even, card_filter_image C phi (fun q => q.2.val % 2 = 0) hphi]
  have heq : C.filter (fun x => (phi x).2.val % 2 = 0) =
      C.filter (fun x => (diagonal x).val % 2 = 0) := by
    apply Finset.filter_congr
    intro x _
    rw [phi_diagonal_parity]
  rw [heq, ← card_filter_image C diagonal (fun x => x.val % 2 = 0) hi, hall]
  decide +kernel

def V0 : Finset H := Finset.univ.image fun k : Fin 12 => (0, k)
def V1 : Finset H := Finset.univ.image fun k : Fin 12 => (k, k)
def v2Point (p : Fin 6 × Fin 2) : H :=
  (⟨(4 * p.1.val + p.2.val) % 12, Nat.mod_lt _ (by decide)⟩,
   ⟨(2 * p.1.val + 2 * p.2.val) % 12, Nat.mod_lt _ (by decide)⟩)
def V2 : Finset H := Finset.univ.image v2Point
def step : Q := (1, 3)

lemma V0_membership : ∀ x : H, x ∈ V0 ↔ x.1 = 0 := by decide +kernel
lemma V1_membership : ∀ x : H, x ∈ V1 ↔ x.1 = x.2 := by decide +kernel
lemma V2_membership : ∀ x : H, x ∈ V2 ↔ phi x = 0 ∨ phi x = step := by
  decide +kernel
lemma card_V0 : V0.card = 12 := by decide +kernel
lemma zero_V0 : (0 : H) ∈ V0 := by decide +kernel
lemma zero_V1 : (0 : H) ∈ V1 := by decide +kernel
lemma zero_V2 : (0 : H) ∈ V2 := by decide +kernel
lemma step_ne_zero : step ≠ 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma phi_sub : ∀ a b : H, phi (a - b) = phi a - phi b := by
  decide +kernel

def sumMap {α : Type*} [Add α] (V C : Finset α) (p : V × C) : α := p.1.val + p.2.val
def Tiles {α : Type*} [Add α] (V C : Finset α) : Prop := Function.Bijective (sumMap V C)

lemma complement_cancel {α : Type*} [Add α] {V C : Finset α} (h : Tiles V C)
    {a b : α} (ha : a ∈ C) (hb : b ∈ C)
    {v w : α} (hv : v ∈ V) (hw : w ∈ V) (heq : v + a = w + b) : a = b := by
  have hp : ((⟨v, hv⟩, ⟨a, ha⟩) : V × C) = (⟨w, hw⟩, ⟨b, hb⟩) := h.1 heq
  exact congrArg (fun p : V × C => p.2.val) hp

lemma common_card {C : Finset H} (h0 : Tiles V0 C) : C.card = 12 := by
  have h := Fintype.card_congr (Equiv.ofBijective (sumMap V0 C) h0)
  simp only [Fintype.card_prod, Fintype.card_coe, card_V0, H, Fintype.card_fin] at h
  omega

lemma common_first_injective {C : Finset H} (h0 : Tiles V0 C) :
    Set.InjOn Prod.fst (C : Set H) := by
  intro a ha b hb hab
  have hd : b - a ∈ V0 := (V0_membership (b - a)).mpr (by
    change b.1 - a.1 = 0
    rw [hab, sub_self])
  apply complement_cancel h0 ha hb hd zero_V0
  simp

lemma common_diagonal_injective {C : Finset H} (h1 : Tiles V1 C) :
    Set.InjOn diagonal (C : Set H) := by
  intro a ha b hb hab
  have heq : (b.1 - a.1) - (b.2 - a.2) = (b.1 - b.2) - (a.1 - a.2) := by abel
  have hd : b - a ∈ V1 := (V1_membership (b - a)).mpr (by
    change b.1 - a.1 = b.2 - a.2
    apply sub_eq_zero.mp
    rw [heq]
    exact sub_eq_zero.mpr hab.symm)
  apply complement_cancel h1 ha hb hd zero_V1
  simp

lemma common_phi_injective {C : Finset H} (h2 : Tiles V2 C) :
    Set.InjOn phi (C : Set H) := by
  intro a ha b hb hab
  have hd : b - a ∈ V2 := (V2_membership (b - a)).mpr (Or.inl (by
    rw [phi_sub, hab, sub_self]))
  apply complement_cancel h2 ha hb hd zero_V2
  simp

lemma common_step_forbidden {C : Finset H} (h2 : Tiles V2 C)
    {a b : H} (ha : a ∈ C) (hb : b ∈ C) : phi a ≠ phi b + step := by
  intro hab
  have hd : a - b ∈ V2 := (V2_membership (a - b)).mpr (Or.inr (by
    rw [phi_sub, hab, add_sub_cancel_left]))
  have heq : b = a := complement_cancel h2 hb ha hd zero_V2 (by simp)
  have hz : (0 : Q) = step := by
    apply add_left_cancel (a := phi a)
    simpa [heq] using hab
  exact step_ne_zero hz.symm

lemma predecessor_step : ∀ r : Fin 4, ∀ s : Fin 6, (r - 1, s + 3) + step = (r, s) := by
  decide +kernel

lemma projected_step {C : Finset H} (hc : C.card = 12) (h2 : Tiles V2 C) :
    ∀ r s, rowOf (C.image phi) r s ≠ rowOf (C.image phi) (r - 1) (s + 3) := by
  let P := C.image phi
  have hd : Disjoint P (P.image fun q => q + step) := by
    apply Finset.disjoint_left.mpr
    intro q hq hqs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨qb, hqb, hqbq⟩ := Finset.mem_image.mp hqs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hqb
    exact common_step_forbidden h2 ha hb hqbq.symm
  have hpc : P.card = 12 := (Finset.card_image_iff.mpr (common_phi_injective h2)).trans hc
  have hi : Function.Injective (fun q : Q => q + step) := fun _ _ h => add_right_cancel h
  have hall : P ∪ P.image (fun q => q + step) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hi, hpc]
    simp [Q]
  intro r s
  by_cases hp : (r, s) ∈ P
  · have hn : (r - 1, s + 3) ∉ P := by
      intro hs
      apply Finset.disjoint_left.mp hd hp
      exact Finset.mem_image.mpr ⟨(r - 1, s + 3), hs, predecessor_step r s⟩
    simp [rowOf, P, hp, hn]
  · have him : (r, s) ∈ P.image (fun q => q + step) := by
      have hu : (r, s) ∈ P ∪ P.image (fun q => q + step) := by rw [hall]; exact Finset.mem_univ _
      exact (Finset.mem_union.mp hu).resolve_left hp
    obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp him
    have hpred : q = (r - 1, s + 3) := add_right_cancel (hqeq.trans (predecessor_step r s).symm)
    have hpmem : (r - 1, s + 3) ∈ P := hpred ▸ hq
    simp [rowOf, P, hp, hpmem]

/-- The three actual seed sets have no common finite tiling complement. -/
theorem no_common_complement (C : Finset H)
    (h0 : Tiles V0 C) (h1 : Tiles V1 C) (h2 : Tiles V2 C) : False := by
  have hc := common_card h0
  exact quotient_parity_obstruction (rowOf (C.image phi))
    (projected_row_card C hc (common_first_injective h0) (common_phi_injective h2))
    (projected_step hc h2)
    (projected_even_card C hc (common_diagonal_injective h1) (common_phi_injective h2))

abbrev G := Fin 60 × Fin 12
def residue12 (x : Fin 60) : Fin 12 := ⟨x.val % 12, Nat.mod_lt _ (by decide)⟩
def residue5 (x : Fin 60) : Fin 5 := ⟨x.val % 5, Nat.mod_lt _ (by decide)⟩
def projection (g : G) : H := (residue12 g.1, g.2)
def layer (g : G) : Fin 5 := residue5 g.1
def crt (h : H) (t : Fin 5) : G :=
  (⟨(25 * h.1.val + 36 * t.val) % 60, Nat.mod_lt _ (by decide)⟩, h.2)

def apmem (g : G) : Prop :=
  ((layer g = 0 ∨ layer g = 1 ∨ layer g = 2) ∧ projection g ∈ V0) ∨
  (layer g = 3 ∧ projection g ∈ V2) ∨ (layer g = 4 ∧ projection g ∈ V1)
instance (g : G) : Decidable (apmem g) := by unfold apmem; infer_instance
def Aplus : Finset G := Finset.univ.filter apmem

lemma card_Aplus : Aplus.card = 60 := by decide +kernel
lemma projection_crt : ∀ h : H, ∀ t : Fin 5, projection (crt h t) = h := by decide +kernel
lemma layer_crt : ∀ h : H, ∀ t : Fin 5, layer (crt h t) = t := by decide +kernel
lemma crt_projection_layer : ∀ g : G, crt (projection g) (layer g) = g := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residue12_add : ∀ x y : Fin 60, residue12 (x + y) = residue12 x + residue12 y := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residue5_add : ∀ x y : Fin 60, residue5 (x + y) = residue5 x + residue5 y := by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residue5_sub_zero : ∀ x y : Fin 60, residue5 (x - y) = 0 ↔ residue5 x = residue5 y := by
  decide +kernel

lemma projection_add (a b : G) : projection (a + b) = projection a + projection b :=
  Prod.ext (residue12_add a.1 b.1) rfl
lemma layer_add (a b : G) : layer (a + b) = layer a + layer b := residue5_add a.1 b.1

lemma projection_layer_injective {a b : G}
    (hp : projection a = projection b) (hl : layer a = layer b) : a = b := by
  rw [← crt_projection_layer a, hp, hl, crt_projection_layer]

def diffLeft (g : G) : G :=
  if layer g = 4 then crt ((projection g).1, (projection g).1) 4
  else crt (0, (projection g).2 - (projection g).1)
    ⟨(layer g).val - 1, lt_of_le_of_lt (Nat.sub_le _ _) (layer g).isLt⟩
def diffRight (g : G) : G :=
  if layer g = 4 then crt (0, (projection g).1 - (projection g).2) 0
  else crt (-(projection g).1, -(projection g).1) 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma nonzero_layer_difference : ∀ g : G, layer g ≠ 0 →
    diffLeft g ∈ Aplus ∧ diffRight g ∈ Aplus ∧ diffLeft g - diffRight g = g := by
  decide +kernel

lemma complement_layer_constant {C : Finset G} (ht : Tiles Aplus C)
    {a b : G} (ha : a ∈ C) (hb : b ∈ C) : layer a = layer b := by
  by_contra hne
  have hd : layer (a - b) ≠ 0 := fun hz => hne ((residue5_sub_zero a.1 b.1).mp hz)
  obtain ⟨hl, hr, heq⟩ := nonzero_layer_difference (a - b) hd
  have heq' : diffRight (a - b) + a = diffLeft (a - b) + b := by
    simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp heq).symm
  have hab : a = b := complement_cancel ht ha hb hr hl heq'
  exact hne (congrArg layer hab)

lemma Aplus_complement_card {C : Finset G} (ht : Tiles Aplus C) : C.card = 12 := by
  have h := Fintype.card_congr (Equiv.ofBijective (sumMap Aplus C) ht)
  simp only [Fintype.card_prod, Fintype.card_coe, card_Aplus, G, Fintype.card_fin] at h
  omega

lemma complement_projection_injective {C : Finset G} (ht : Tiles Aplus C) :
    Set.InjOn projection (C : Set G) := by
  intro a ha b hb hp
  exact projection_layer_injective hp (complement_layer_constant ht ha hb)

def seed (j : Fin 3) : Finset H := if j = 0 then V0 else if j = 1 then V1 else V2
def seedLayer (j : Fin 3) : Fin 5 := if j = 0 then 0 else if j = 1 then 4 else 3
lemma seed_card : ∀ j : Fin 3, (seed j).card = 12 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma Aplus_seed_layer : ∀ a : G, ∀ j : Fin 3,
    a ∈ Aplus → layer a = seedLayer j → projection a ∈ seed j := by
  decide +kernel

/-- Every hypothetical complement projects to a common complement of all three seeds. -/
lemma projected_complement_tiles {C : Finset G} (ht : Tiles Aplus C) (j : Fin 3) :
    Tiles (seed j) (C.image projection) := by
  classical
  have hc : (C.image projection).card = 12 :=
    (Finset.card_image_iff.mpr (complement_projection_injective ht)).trans (Aplus_complement_card ht)
  obtain ⟨p0, _⟩ := ht.2 0
  let c0 := p0.2.val
  have hc0 : c0 ∈ C := p0.2.property
  apply (Fintype.bijective_iff_surjective_and_card (sumMap (seed j) (C.image projection))).mpr
  constructor
  · intro h
    obtain ⟨p, hp⟩ := ht.2 (crt h (seedLayer j + layer c0))
    change p.1.val + p.2.val = crt h (seedLayer j + layer c0) at hp
    have hl : layer p.1.val = seedLayer j := by
      apply add_right_cancel (b := layer c0)
      calc
        layer p.1.val + layer c0 = layer p.1.val + layer p.2.val := by
          rw [complement_layer_constant ht p.2.property hc0]
        _ = layer (p.1.val + p.2.val) := (layer_add _ _).symm
        _ = seedLayer j + layer c0 := by rw [hp, layer_crt]
    have ha : projection p.1.val ∈ seed j := Aplus_seed_layer p.1.val j p.1.property hl
    have hb : projection p.2.val ∈ C.image projection := Finset.mem_image_of_mem _ p.2.property
    refine ⟨(⟨projection p.1.val, ha⟩, ⟨projection p.2.val, hb⟩), ?_⟩
    change projection p.1.val + projection p.2.val = h
    rw [← projection_add, hp, projection_crt]
  · simp only [Fintype.card_prod, Fintype.card_coe, seed_card, hc, H, Fintype.card_fin]

/-- Universal finite nontiling of the actual sixty-point set, not a chosen failed complement. -/
theorem Aplus_not_tiles (C : Finset G) : ¬ Tiles Aplus C := by
  intro ht
  have h0 : Tiles V0 (C.image projection) := by simpa [seed] using projected_complement_tiles ht 0
  have h1 : Tiles V1 (C.image projection) := by simpa [seed] using projected_complement_tiles ht 1
  have h2 : Tiles V2 (C.image projection) := by simpa [seed] using projected_complement_tiles ht 2
  exact no_common_complement (C.image projection) h0 h1 h2

theorem Aplus_no_complement : ¬ ∃ C : Finset G, Tiles Aplus C := by
  rintro ⟨C, hC⟩
  exact Aplus_not_tiles C hC

end FugledeNontile
#print axioms FugledeNontile.row_parity
#print axioms FugledeNontile.quotient_parity_obstruction
#print axioms FugledeNontile.no_common_complement
#print axioms FugledeNontile.Aplus_no_complement
