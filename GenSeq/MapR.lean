import Mathlib
import GenSeq.OrderedSpan

variable (n : ℕ)

/-- The stabiliser of `(0 : Fin (n+1))` in `Equiv.Perm (Fin (n+1))`.
    This is the copy of `Sn` sitting inside `S_{n+1}` that fixes the first point. -/
def stabZero : Subgroup (Equiv.Perm (Fin (n + 1))) :=
  MulAction.stabilizer (Equiv.Perm (Fin (n + 1))) (0 : Fin (n + 1))

/-- The map R : Perm(Fin n) →* Perm(Fin(n+1)) that embeds via successor.
    It extends σ to act by the successor map on nonzero elements and fixes 0. -/
def mapR : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.extendDomainHom (finSuccAboveEquiv 0)

/-- `mapR` fixes 0 pointwise. -/
theorem mapR_apply_zero (σ : Equiv.Perm (Fin n)) : mapR n σ 0 = 0 :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)

/-- `mapR n` is injective (as `extendDomainHom` always is). -/
theorem mapR_injective : Function.Injective (mapR n) :=
  Equiv.Perm.extendDomainHom_injective _

/-- The range of `mapR` is contained in the stabiliser of 0. -/
theorem mapR_range_le_stabZero : (mapR n).range ≤ stabZero n := by
  intro τ hτ
  simp only [MonoidHom.mem_range] at hτ
  obtain ⟨σ, rfl⟩ := hτ
  simp [stabZero, MulAction.mem_stabilizer_iff, mapR_apply_zero]

/-- The stabiliser of 0 is contained in the range of `mapR`.
    Every permutation fixing 0 arises from some permutation of Fin n. -/
theorem stabZero_le_mapR_range : stabZero n ≤ (mapR n).range := by
  intro τ hτ
  simp only [stabZero, MulAction.mem_stabilizer_iff] at hτ
  -- hτ : τ 0 = 0. Define σ k := (τ k.succ).pred (h k).
  -- Then mapR σ = τ because: mapR σ 0 = 0 = τ 0, and for i ≠ 0,
  -- mapR σ i = (finSuccAboveEquiv 0 (σ (i.pred hi))) = (σ (i.pred hi)).succ
  --          = ((τ (i.pred hi).succ).pred _).succ = τ (i.pred hi).succ = τ i.
  sorry

/-- (Proposition 5.10) `mapR` is a group isomorphism from Perm(Fin n) to `stabZero n`. -/
theorem mapR_range_eq_stabZero : (mapR n).range = stabZero n :=
  le_antisymm (mapR_range_le_stabZero n) (stabZero_le_mapR_range n)

/-- (Proposition 5.11) If `l` generates all of `Perm (Fin n)`, then `l.map (mapR n)`
    generates `(mapR n).range` (= `stabZero n` by `mapR_range_eq_stabZero`). -/
theorem mapR_preserves_isGeneratingSeq (l : List (Equiv.Perm (Fin n))) :
    IsGeneratingSeq l ⊤ →
    IsGeneratingSeq (l.map (mapR n)) (mapR n).range := by
  intro hl
  unfold IsGeneratingSeq at *
  rw [← image_orderedSpan_of_hom, ← hl, Subgroup.coe_top, Set.image_univ, MonoidHom.coe_range]
