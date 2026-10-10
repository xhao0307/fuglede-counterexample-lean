import BlockSpectrum
import ConcreteNontile
import FiniteSpectral

set_option debug.skipKernelTC false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-!
The proved copied spectrum, on exactly the integer vector block used in
ConcreteNontile. Finite orthogonality and completeness are derived from
seed97, without additional Gram or expansion hypotheses.
-/

namespace FugledeConcreteSpectrum

open scoped BigOperators ComplexConjugate

abbrev Index := FugledeSeeds.FrequencyIndex × (ZMod 97 × ZMod 97)

def point (p : Index) : Fin 2 → ℤ :=
  FugledeConcrete.toVec (FugledeBlockSpectrum.seedBlockPoint 97 p)

noncomputable def frequency (ξ : Index) : Fin 2 → ℝ :=
  ![(FugledeBlockSpectrum.seedBlockFrequency 97 ξ).1,
    (FugledeBlockSpectrum.seedBlockFrequency 97 ξ).2]

theorem point_injective : Function.Injective point :=
  FugledeConcrete.toVec_injective.comp (FugledeBlockSpectrum.seedBlockPoint_injective 97)

theorem frequency_injective : Function.Injective frequency := by
  intro ξ η h
  apply FugledeBlockSpectrum.seedBlockFrequency_injective 97
  have h₁ := congrFun h 0
  have h₂ := congrFun h 1
  exact Prod.ext h₁ h₂

/-- Membership follows from the original symbolic grid construction. -/
theorem seedBlockPoint_mem_pairBlock (p : Index) :
    FugledeBlockSpectrum.seedBlockPoint 97 p ∈ FugledeConcrete.pairBlock := by
  apply Finset.mem_image.mpr
  refine ⟨((p.2.1.val, p.2.2.val), FugledeSeeds.aPoint p.1.swap), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt p.2.1),
        Finset.mem_range.mpr (ZMod.val_lt p.2.2)⟩
    · exact FugledeSpectral.aPoint_mem_nontile p.1.swap
  · change FugledeTransfer.gridOrigin 60 12 (p.2.1.val, p.2.2.val) +
      FugledeTransfer.representative (n₁ := 60) (n₂ := 12)
        (FugledeSeeds.aPoint p.1.swap) =
      FugledeBlockSpectrum.seedBlockPoint 97 p
    simp only [FugledeTransfer.gridOrigin, FugledeTransfer.representative,
      FugledeBlockSpectrum.seedBlockPoint, FugledeBlockSpectrum.expandedPoint,
      FugledeBlockSpectrum.seedPoint, FugledeBlockSpectrum.seedLift]
    exact add_comm _ _

theorem point_mem_vectorBlock (p : Index) : point p ∈ FugledeConcrete.vectorBlock :=
  Finset.mem_image.mpr ⟨FugledeBlockSpectrum.seedBlockPoint 97 p,
    seedBlockPoint_mem_pairBlock p, rfl⟩

theorem point_image_card : (Finset.univ.image point).card = 564540 := by
  rw [Finset.card_image_of_injective _ point_injective]
  norm_num [Index, FugledeSeeds.FrequencyIndex, Fintype.card_prod, ZMod.card]

/-- No enumeration of the 564540-point block is used. -/
theorem point_image_eq_vectorBlock :
    Finset.univ.image point = FugledeConcrete.vectorBlock := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact point_mem_vectorBlock p
  · rw [FugledeConcrete.vectorBlock_card, point_image_card]

/-- The target's canonical vector character is the actual copied character. -/
theorem character_at_point (ξ p : Index) :
    FugledeTarget.exponentialCharacter (frequency ξ) (FugledeCube.intVec (point p)) =
      FugledeBlockSpectrum.pairCharacter
        (FugledeBlockSpectrum.seedBlockFrequency 97 ξ)
        (FugledeBlockSpectrum.seedBlockPoint 97 p) := by
  simp [FugledeTarget.exponentialCharacter, frequency, FugledeCube.intVec,
    point, FugledeConcrete.toVec, FugledeBlockSpectrum.pairCharacter,
    FugledeBlockSpectrum.cis, Fin.sum_univ_two]

/-- Actual finite orthogonality on vectorBlock, stated in canonical characters. -/
theorem finite_gram (ξ η : Index) :
    (∑ f ∈ FugledeConcrete.vectorBlock,
      conj (FugledeTarget.exponentialCharacter (frequency ξ) (FugledeCube.intVec f)) *
        FugledeTarget.exponentialCharacter (frequency η) (FugledeCube.intVec f)) =
      if ξ = η then (564540 : ℂ) else 0 := by
  rw [← point_image_eq_vectorBlock, Finset.sum_image]
  · simpa only [character_at_point] using FugledeBlockSpectrum.seed97_gram ξ η
  · intro p _ q _ hpq
    exact point_injective hpq

/-- Every function on the true finite block expands in the actual copied spectrum. -/
theorem finite_expansion (v : FugledeConcrete.vectorBlock → ℂ) :
    ∃ c : Index → ℂ, ∀ f : FugledeConcrete.vectorBlock,
      v f = ∑ ξ : Index, c ξ *
        FugledeTarget.exponentialCharacter (frequency ξ) (FugledeCube.intVec f.val) := by
  obtain ⟨c, hc⟩ := FugledeBlockSpectrum.seed97_every_function
    (fun p => v ⟨point p, point_mem_vectorBlock p⟩)
  refine ⟨c, fun f => ?_⟩
  have hf : f.val ∈ Finset.univ.image point := by
    rw [point_image_eq_vectorBlock]
    exact f.property
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hf
  have hsub : (⟨point p, point_mem_vectorBlock p⟩ : FugledeConcrete.vectorBlock) = f :=
    Subtype.ext hp
  simpa only [← character_at_point, hsub, hp] using hc p

end FugledeConcreteSpectrum

#print axioms FugledeConcreteSpectrum.point_injective
#print axioms FugledeConcreteSpectrum.frequency_injective
#print axioms FugledeConcreteSpectrum.seedBlockPoint_mem_pairBlock
#print axioms FugledeConcreteSpectrum.point_mem_vectorBlock
#print axioms FugledeConcreteSpectrum.point_image_card
#print axioms FugledeConcreteSpectrum.point_image_eq_vectorBlock
#print axioms FugledeConcreteSpectrum.character_at_point
#print axioms FugledeConcreteSpectrum.finite_gram
#print axioms FugledeConcreteSpectrum.finite_expansion
