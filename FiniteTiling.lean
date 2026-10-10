import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation

/-!
The actual 60-point finite tile and its 12-point complement, from
Tao Zhang arXiv:2607.15632v1. Kernel checks use an explicit inverse witness.
No nonspectrality or passage to Euclidean space is proved in this module.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace FugledeFinite
abbrev G := Fin 60 × Fin 12

def addG (x y : G) : G := (x.1 + y.1, x.2 + y.2)

def residue12 (x : Fin 60) : Fin 12 := ⟨x.val % 12, Nat.mod_lt _ (by decide)⟩
def residue5 (x : Fin 60) : Fin 5 := ⟨x.val % 5, Nat.mod_lt _ (by decide)⟩
def crt (x : Fin 12) (y : Fin 12) (t : Fin 5) : G :=
  (⟨(25*x.val+36*t.val)%60, Nat.mod_lt _ (by decide)⟩, y)

def seedF : Fin 12 → Fin 12 := ![0, 5, 0, 7, 9, 2, 10, 4, 7, 8, 10, 10]

def seedHInv : Fin 12 → Fin 12 := ![0, 4, 2, 8, 6, 9, 1, 5, 10, 11, 3, 7]

def seedB2Inv : Fin 12 → Fin 12 → Fin 12 := ![![0, 9, 2, 7, 4, 1, 0, 9, 2, 7, 4, 1],
  ![6, 5, 4, 1, 10, 11, 6, 5, 4, 1, 10, 11],
  ![8, 3, 10, 11, 6, 5, 8, 3, 10, 11, 6, 5],
  ![0, 9, 2, 7, 8, 3, 0, 9, 2, 7, 8, 3],
  ![2, 7, 4, 1, 0, 9, 2, 7, 4, 1, 0, 9],
  ![4, 1, 10, 11, 6, 5, 4, 1, 10, 11, 6, 5],
  ![10, 11, 6, 5, 8, 3, 10, 11, 6, 5, 8, 3],
  ![2, 7, 8, 3, 0, 9, 2, 7, 8, 3, 0, 9],
  ![4, 1, 0, 9, 2, 7, 4, 1, 0, 9, 2, 7],
  ![10, 11, 6, 5, 4, 1, 10, 11, 6, 5, 4, 1],
  ![6, 5, 8, 3, 10, 11, 6, 5, 8, 3, 10, 11],
  ![8, 3, 0, 9, 2, 7, 8, 3, 0, 9, 2, 7]]

def inB2 (x y : Fin 12) : Prop :=
  ∃ a : Fin 3, ∃ b : Fin 2, ∃ c : Fin 2,
    x.val = (3*c.val+4*a.val)%12 ∧ y.val = (4*a.val+6*b.val)%12

instance (x y : Fin 12) : Decidable (inB2 x y) := by unfold inB2; infer_instance

def amem (g : G) : Prop :=
  let x := residue12 g.1
  let t := residue5 g.1
  (t = 0 ∧ g.2 = 0) ∨ ((t = 3 ∨ t = 4) ∧ g.2 = -x) ∨
    ((t = 1 ∨ t = 2) ∧ inB2 x g.2)

instance (g : G) : Decidable (amem g) := by unfold amem; infer_instance

def tmem (g : G) : Prop := g = crt (seedF g.2) g.2 0
instance (g : G) : Decidable (tmem g) := by unfold tmem; infer_instance

def Aminus : Finset G := Finset.univ.filter amem

def Tminus : Finset G := Finset.univ.filter tmem

def witnessY (g : G) : Fin 12 :=
  if residue5 g.1 = 0 then g.2
  else if residue5 g.1 = 3 ∨ residue5 g.1 = 4 then
    seedHInv (residue12 g.1 + g.2)
  else seedB2Inv (residue12 g.1) g.2

def witnessA (g : G) : G :=
  crt (residue12 g.1 - seedF (witnessY g)) (g.2 - witnessY g) (residue5 g.1)

def witnessT (g : G) : G := crt (seedF (witnessY g)) (witnessY g) 0

/-- Finite decision checks the arithmetic of each explicit inverse, not an
exhaustive search over all possible pairs of representations. -/
theorem witness_check : ∀ g : G,
    amem (witnessA g) ∧ tmem (witnessT g) ∧ addG (witnessA g) (witnessT g) = g := by
  decide +kernel

theorem card_Aminus : Aminus.card = 60 := by decide +kernel

theorem card_Tminus : Tminus.card = 12 := by decide +kernel

def representationMap (p : Aminus × Tminus) : G := addG p.1.val p.2.val

/-- This proves genuine unique coverage of the finite group. -/
theorem Aminus_tiles : Function.Bijective representationMap := by
  apply (Fintype.bijective_iff_surjective_and_card representationMap).mpr
  constructor
  · intro g
    obtain ⟨ha, ht, heq⟩ := witness_check g
    have ha' : witnessA g ∈ Aminus := by simpa [Aminus] using ha
    have ht' : witnessT g ∈ Tminus := by simpa [Tminus] using ht
    exact ⟨(⟨witnessA g, ha'⟩, ⟨witnessT g, ht'⟩), heq⟩
  · simp only [Fintype.card_prod, Fintype.card_coe, card_Aminus, card_Tminus,
      G, Fintype.card_fin]

end FugledeFinite
#print axioms FugledeFinite.witness_check
#print axioms FugledeFinite.card_Aminus
#print axioms FugledeFinite.card_Tminus
#print axioms FugledeFinite.Aminus_tiles
