import Mathlib
import GenSeq.OrderedSpan
import GenSeq.MapR

/-! # Sambale sequence and Theorem 5.16

Definitions and proofs following Schwiering (2023), Chapter 5. -/

/-! ## Helper arithmetic -/

/-- `capLog n = I(n) = ⌈log₂ n⌉`, the number of levels in `Ξ_n`. -/
def capLog (n : ℕ) : ℕ := Nat.clog 2 n

/-- `strideCount n i = J(n,i) = min(n − 2^i, 2^i)`, swaps at level `i` for `Sn`. -/
def strideCount (n i : ℕ) : ℕ := min (n - 2^i) (2^i)

/-- When `j < strideCount n i`, the index `j + 2^i` is still inside `Fin n`. -/
private lemma strideCount_hi {n i j : ℕ} (hj : j < strideCount n i) : j + 2^i < n :=
  Nat.lt_sub_iff_add_lt.mp (lt_of_lt_of_le hj (Nat.min_le_left _ _))

private lemma strideCount_lo {n i j : ℕ} (hj : j < strideCount n i) : j < n :=
  lt_of_le_of_lt (Nat.le_add_right j (2^i)) (strideCount_hi hj)

/-! ## The permutations ξ_{n,i} -/

/-- `sambalePerm n i = ξ_{n,i}`: product of transpositions `(j, j + 2^i)` for
    `j = 0, …, J(n,i) − 1`. -/
def sambalePerm (n i : ℕ) : Equiv.Perm (Fin n) :=
  ((List.range (strideCount n i)).map fun j =>
    if h : j + 2^i < n then
      Equiv.swap ⟨j, lt_of_le_of_lt (Nat.le_add_right j _) h⟩ ⟨j + 2^i, h⟩
    else (1 : Equiv.Perm (Fin n))).prod

/-- Product of pairwise-commuting involutions is itself an involution. -/
private lemma list_prod_sq_eq_one {G : Type*} [Group G] (l : List G)
    (hinv : ∀ x ∈ l, x * x = 1)
    (hcomm : ∀ x ∈ l, ∀ y ∈ l, Commute x y) :
    l.prod * l.prod = 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons]
    have ha2 : a * a = 1 := hinv a List.mem_cons_self
    have ht_sq : t.prod * t.prod = 1 := ih
      (fun x hx => hinv x (List.mem_cons_of_mem a hx))
      (fun x hx y hy => hcomm x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
    have hcomm_ta : Commute t.prod a :=
      Commute.list_prod_left t a (fun x hx =>
        (hcomm a List.mem_cons_self x (List.mem_cons_of_mem a hx)).symm)
    calc (a * t.prod) * (a * t.prod)
        = a * (t.prod * a) * t.prod := by group
      _ = a * (a * t.prod) * t.prod := by rw [hcomm_ta]
      _ = (a * a) * (t.prod * t.prod) := by group
      _ = 1 := by rw [ha2, ht_sq, mul_one]

/-- (Proposition 5.15) Each `ξ_{n,i}` is an involution. The transpositions `(j, j+2^i)` are
    pairwise disjoint because if `j < j'` then `j < 2^i ≤ j' < j' + 2^i`. -/
theorem sambalePerm_mul_self (n i : ℕ) : sambalePerm n i * sambalePerm n i = 1 := by
  unfold sambalePerm
  apply list_prod_sq_eq_one
  · -- Each element is an involution
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hjn : j + 2 ^ i < n := strideCount_hi hj
    simp only [dif_pos hjn, Equiv.swap_mul_self]
  · -- Elements pairwise commute (swaps on disjoint supports)
    intro x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨j₁, hj₁, rfl⟩ := hx
    obtain ⟨j₂, hj₂, rfl⟩ := hy
    have hjn₁ : j₁ + 2 ^ i < n := strideCount_hi hj₁
    have hjn₂ : j₂ + 2 ^ i < n := strideCount_hi hj₂
    simp only [dif_pos hjn₁, dif_pos hjn₂]
    by_cases hjne : j₁ = j₂
    · subst hjne; exact Commute.refl _
    · apply Equiv.Perm.Disjoint.commute
      have hj₁lt : j₁ < 2 ^ i := lt_of_lt_of_le hj₁ (Nat.min_le_right _ _)
      have hj₂lt : j₂ < 2 ^ i := lt_of_lt_of_le hj₂ (Nat.min_le_right _ _)
      intro x
      by_cases hx₁ : x.val = j₁
      · right
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; exact absurd (congr_arg Fin.val h) (show x.val ≠ j₂ from by omega)
        · intro h; exact absurd (congr_arg Fin.val h) (show x.val ≠ j₂ + 2 ^ i from by omega)
      · by_cases hx₂ : x.val = j₁ + 2 ^ i
        · right
          apply Equiv.swap_apply_of_ne_of_ne
          · intro h; exact absurd (congr_arg Fin.val h) (show x.val ≠ j₂ from by omega)
          · intro h; exact absurd (congr_arg Fin.val h) (show x.val ≠ j₂ + 2 ^ i from by omega)
        · left
          apply Equiv.swap_apply_of_ne_of_ne
          · intro h; exact hx₁ (congr_arg Fin.val h)
          · intro h; exact hx₂ (congr_arg Fin.val h)

/-! ## The Sambale sequence Ξ_n -/

/-- The Sambale generating sequence `Ξ_n ⊆ Perm(Fin n)`:
    `Ξ_0 = Ξ_1 = []` and `Ξ_{n+2} = Ξ_{n+1}.map R ++ [ξ_{n+2,0}, …, ξ_{n+2,I(n+2)−1}]`. -/
def sambale : (n : ℕ) → List (Equiv.Perm (Fin n))
  | 0     => []
  | 1     => []
  | n + 2 =>
    (sambale (n + 1)).map (mapR (n + 1)) ++
    (List.range (capLog (n + 2))).map (sambalePerm (n + 2))

/-! ## Key sub-lemma (step (i) of Theorem 5.16) -/

/-- The binary-representation step: for `m : Fin n` with binary digits `s_k`, the ordered
    product `∏_k ξ_{n,k}^{s_k}` (as a `List.prod`) maps `0` to `m`.

    Remaining goal:
      n : ℕ, hn : 0 < n, s : Fin (capLog n) → Fin 2, m : Fin n,
      hm : m.val = ∑ k : Fin (capLog n), (s k).val * 2 ^ k.val
      ⊢ ((List.range (capLog n)).map (fun k => sambalePerm n k ^
             if hk : k < capLog n then (s ⟨k, hk⟩).val else 0) |>.prod) (⟨0, hn⟩ : Fin n)
          = m -/
theorem sambalePerm_prod_apply_zero
    {n : ℕ} (hn : 0 < n)
    (s : Fin (capLog n) → Fin 2)
    (m : Fin n)
    (hm : m.val = ∑ k : Fin (capLog n), (s k).val * 2 ^ k.val) :
    ((List.range (capLog n)).map (fun k =>
        sambalePerm n k ^ if hk : k < capLog n then (s ⟨k, hk⟩).val else 0)
      |>.prod) (⟨0, hn⟩ : Fin n) = m := by
  -- Strategy: induct on K = capLog n, maintaining the invariant that after processing
  -- bits 0..K-1 the partial prefix product applied to 0 equals ∑_{k<K} s_k 2^k.
  --
  -- At bit K with running position i₀ = ∑_{k<K} s_k 2^k < 2^K:
  --   s_K = 0 → factor is 1, position unchanged.
  --   s_K = 1 → sambalePerm n K contains swap(i₀, i₀ + 2^K); all other swaps in
  --              sambalePerm n K have j ≠ i₀ and j+2^K ≠ i₀ (since i₀ < 2^K ≤ j'
  --              for all other j'), so they fix i₀ by Equiv.swap_apply_of_ne_of_ne.
  --              Thus (sambalePerm n K) i₀ = i₀ + 2^K.
  --
  -- Useful: `Fin.val_fin_lt`, `Nat.sum_range_bits`, `List.prod_map_reverse`
  sorry

/-! ## Monotonicity of orderedSpan under list concatenation -/

/-- `orderedSpan` is monotone under right-appending. -/
private lemma orderedSpan_append_le_right {G : Type*} [Group G] (l l' : List G) :
    orderedSpan l ⊆ orderedSpan (l ++ l') := by
  induction l' using List.reverseRecOn with
  | nil => simp
  | append_singleton l' g ih =>
    rw [← List.append_assoc, orderedSpan_append_singleton]
    exact Set.Subset.trans ih Set.subset_union_left

/-- `orderedSpan` is monotone under left-prepending. -/
private lemma orderedSpan_append_le_left {G : Type*} [Group G] (l l' : List G) :
    orderedSpan l' ⊆ orderedSpan (l ++ l') := by
  induction l' using List.reverseRecOn with
  | nil =>
    simp only [List.append_nil, orderedSpan_nil]
    exact Set.singleton_subset_iff.mpr (one_mem_orderedSpan l)
  | append_singleton l' g ih =>
    intro x hx
    rw [orderedSpan_append_singleton] at hx
    rw [← List.append_assoc, orderedSpan_append_singleton]
    simp only [Set.mem_union, Set.mem_image] at hx ⊢
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact Or.inl (ih hx)
    · exact Or.inr (Set.mem_image_of_mem _ (ih hy))

/-! ## Main theorem -/

/-- Helper: every permutation of a 0-element or 1-element set is the identity. -/
private lemma perm_fin_zero_eq_one (σ : Equiv.Perm (Fin 0)) : σ = 1 :=
  Equiv.ext (fun x => x.elim0)

private lemma perm_fin_one_eq_one (σ : Equiv.Perm (Fin 1)) : σ = 1 :=
  Equiv.ext (fun x => Subsingleton.elim _ _)

/-- (Theorem 5.16) The Sambale sequence `Ξ_n` is a generating sequence for all of `Sn`. -/
theorem sambale_isGeneratingSeq (n : ℕ) : IsGeneratingSeq (sambale n) ⊤ := by
  induction n with
  | zero =>
    -- S_0 = {id} = orderedSpan [].
    simp only [IsGeneratingSeq, sambale, orderedSpan, Subgroup.coe_top]
    symm; apply Set.eq_univ_of_forall; intro σ
    exact Set.mem_singleton_iff.mpr (perm_fin_zero_eq_one σ)
  | succ n ih =>
    cases n with
    | zero =>
      -- S_1 = {id} = orderedSpan [].
      simp only [IsGeneratingSeq, sambale, orderedSpan, Subgroup.coe_top]
      symm; apply Set.eq_univ_of_forall; intro σ
      exact Set.mem_singleton_iff.mpr (perm_fin_one_eq_one σ)
    | succ m =>
      -- IH: Ξ_{m+1} generates S_{m+1}. Goal: Ξ_{m+2} generates S_{m+2}.
      simp only [IsGeneratingSeq, Subgroup.coe_top] at ih ⊢
      -- (mapR (m+1)).range = stabZero (m+1) generates the stabilizer of 0.
      have h_stab : orderedSpan ((sambale (m + 1)).map (mapR (m + 1))) =
          ↑(mapR (m + 1)).range :=
        (mapR_preserves_isGeneratingSeq (m + 1) (sambale (m + 1)) ih).symm
      change Set.univ = orderedSpan (sambale (m + 2))
      simp only [sambale]
      -- For any σ : Perm(Fin(m+2)):
      --   1. Write σ(0) in binary: σ(0) = ∑_k s_k 2^k.
      --   2. Let π_s = ∏_k ξ^{s_k}_{m+2,k}. By sambalePerm_prod_apply_zero, π_s(0) = σ(0).
      --   3. π_s⁻¹ * σ fixes 0, so lies in stabZero = span(Ξ_{m+1}.map R).
      --   4. π_s ∈ span([ξ_{m+2,0},…]) ⊆ span(Ξ_{m+2}).
      --   5. σ = π_s * (π_s⁻¹ * σ) ∈ span(Ξ_{m+2}).
      --
      -- Remaining goal:
      --   m : ℕ, ih : Set.univ = orderedSpan (sambale (m + 1)),
      --   h_stab : orderedSpan ((sambale (m+1)).map (mapR (m+1))) = ↑(mapR (m+1)).range
      --   ⊢ Set.univ = orderedSpan ((sambale (m+1)).map (mapR (m+1)) ++
      --                              (List.range (capLog (m+2))).map (sambalePerm (m+2)))
      --
      -- Strategy (depends on sambalePerm_prod_apply_zero):
      -- Let A = Ξ_{m+1}.map R, B = ξ_list. Show ∀ σ, σ ∈ orderedSpan (A ++ B).
      -- (1) Extract binary digits s of σ(0).val; let π_s be the product of ξ^{s_k}.
      --     By sambalePerm_prod_apply_zero, π_s 0 = σ 0.
      -- (2) π_s ∈ orderedSpan B (each factor ξ^{s_k} with s_k∈{0,1} is in orderedSpan B
      --     since ξ^0=1∈orderedSpan and ξ^1=ξ∈orderedSpan; use involutivity for ξ^0=1).
      -- (3) π_s⁻¹ * σ fixes 0: (π_s⁻¹*σ) 0 = π_s⁻¹ (σ 0) = π_s⁻¹ (π_s 0) = 0.
      --     So π_s⁻¹*σ ∈ stabZero (m+1) = (mapR (m+1)).range.
      --     By mapR_range_eq_stabZero and h_stab: π_s⁻¹*σ ∈ orderedSpan A.
      -- (4) Need: orderedSpan A × orderedSpan B → orderedSpan (A ++ B).
      --     Generalise: ∀ a ∈ orderedSpan A, ∀ b ∈ orderedSpan B,
      --       b * a ∈ orderedSpan (A ++ B)  [note: orderedSpan appends to LEFT].
      --     This follows by induction on A using orderedSpan_append_le_left/right.
      --     Actually need π_s * (π_s⁻¹*σ): π_s from B-part of orderedSpan (A++B),
      --     π_s⁻¹*σ from A-part; their product σ is in orderedSpan (A++B) by a
      --     "product-membership" lemma. Prove helper:
      --       orderedSpan_mul_mem : b ∈ orderedSpan l₂ → a ∈ orderedSpan l₁ →
      --         b * a ∈ orderedSpan (l₁ ++ l₂)
      --     by induction on l₂.
      sorry
