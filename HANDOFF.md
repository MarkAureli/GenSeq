# HANDOFF.md — GenSeq

## Goal

Formalise **Theorem 5.16** from Schwiering's master's thesis (2023): the Sambale sequence
`Ξ_n` is a **generating sequence** (called "complete sequence" in the thesis) for the
symmetric group `Sn`.

The thesis works exclusively in `Sn`. We lift Definition 5.1 to arbitrary groups, call the
notion a *generating sequence*, and then prove Theorem 5.16 in the specialised `Sn` setting.

---

## Mathematical Content

### Notation

- `[n]` = {1, …, n} (1-indexed in the thesis; 0-indexed `Fin n` in Lean)
- `Sn` = symmetric group on `[n]` = `Equiv.Perm (Fin n)` in Lean
- `Sn^1` = pointwise stabiliser of 1 in `Sn+1`, i.e., permutations fixing 1

---

### Definition: Ordered Span and Generating Sequence

Let `G` be a group and `l = [g₁, …, gₘ]` a finite list in `G`.

The **ordered span** of `l` is:
```
⟪⟫l⟫⟫ = { gₘ^{bₘ} * … * g₁^{b₁} | bᵢ ∈ {0, 1} }  ⊆  G
```

The list `l` is a **generating sequence** for `H ≤ G` iff `H = ⟪⟫l⟫⟫` (as sets).

**Note:** When all `gᵢ` are involutions (`gᵢ² = 1`), varying `bᵢ ∈ {0,1}` covers all
products of subsets of `{g₁, …, gₘ}` in order, and `gᵢ^{-1} = gᵢ`. This is the key
property exploited by the proof.

*Lean definition sketch:*
```lean
def orderedSpan {G : Type*} [Group G] : List G → Set G
  | []      => {1}
  | l ++ [g] => orderedSpan l ∪ (orderedSpan l).image (· * g)

def IsGeneratingSeq {G : Type*} [Group G] (l : List G) (H : Subgroup G) : Prop :=
  ↑H = orderedSpan l
```

---

### Definition 5.9: The Map R

For `n : ℕ`, define `R : Equiv.Perm (Fin n) → Equiv.Perm (Fin (n+1))` by:
```
R(σ)(0)   = 0
R(σ)(i+1) = σ(i) + 1      (i : Fin n)
```
This embeds `Sn` into `Sn+1` as the stabiliser of `0` (= `Sn+1^0` in 0-indexed notation).

In Lean, `R` corresponds to `Equiv.Perm.extendDomain` along the embedding
`Fin.succEmb : Fin n ↪ Fin (n+1)` mapping `i ↦ i.castSucc + 1` ... or more precisely
`Fin.succ : Fin n → Fin (n+1)`.

---

### Proposition 5.10: R is an Isomorphism

`R` is a group isomorphism from `Sn` to `Sn+1^0` (stabiliser of `0` in `Sn+1`).

*Proof sketch:* Show R is a group homomorphism (direct calculation), then exhibit the
left-inverse `P(σ)(i) = σ(i+1) - 1`.

---

### Proposition 5.11: R Preserves Generating Sequences

If `l` is a generating sequence for `H ≤ Sn`, then `l.map R` is a generating sequence
for `R(H) ≤ Sn+1`.

*Proof sketch:* `⟪⟫R(l)⟫⟫ = R(⟪⟫l⟫⟫)` because R is a group homomorphism. Then use the
fact that `⟪⟫l⟫⟫ = H` by assumption.

---

### Definition 5.12: The Sambale Sequence `Ξ_n`

**Helper functions** (1-indexed in thesis; translate to 0-indexed for Lean):
```
I : ℕ → ℕ,       I(n)   = ⌈log₂ n⌉       -- = Nat.clog 2 n in Lean
J : ℕ → ℕ → ℕ,   J(n,i) = min(n - 2^i, 2^i)   -- 0-indexed: i ∈ {0,…,I(n)-1}
```

Values of `I`: `I(1)=0, I(2)=1, I(3)=2, I(4)=2, I(5)=3, …`
Values of `J` (0-indexed i): `J(n,i) = min(n - 2^i, 2^i)`.

**The permutations** `ξ_{n,i} ∈ Sn` for `i ∈ {0,…,I(n)-1}`:
```
ξ_{n,i} = ∏_{j=0}^{J(n,i)-1} swap(j, j + 2^i)
```
This is a product of `J(n,i)` disjoint transpositions.

**The sequence** (recursive on n):
```
Ξ_1 = []
Ξ_n = Ξ_{n-1}.map R ++ [ξ_{n,0}, …, ξ_{n,I(n)-1}]    (n > 1)
```
The `map R` lifts each element of `Ξ_{n-1} : List (Perm (Fin (n-1)))` into
`List (Perm (Fin n))`.

**Example** (1-indexed as in thesis):
```
Ξ_1 = []
Ξ_2 = [(1 2)]
Ξ_3 = [(2 3), (1 2), (1 3)]
Ξ_4 = [(3 4), (2 3), (2 4), (1 2), (1 3)(2 4)]
```

---

### Proposition 5.13: Length of `Ξ_n`

`|Ξ_n| = ∑_{n'=1}^{n} I(n') = ∑_{n'=1}^{n} ⌈log₂ n'⌉`

In particular, `|Ξ_n| ∈ Θ(n log₂ n)`.

---

### Proposition 5.14: Number of Transpositions

(i) `J(n,i) = n - 2^i  ⟺  i = I(n)-1` (i.e., only the last level uses the
    "long" stride formula).

(ii) Total transpositions across all levels across all `n`: `∑_{n'} ∑_i J(n',i) = n(n-1)/2`.

---

### Proposition 5.15: `ξ_{n,i}` is an Involution

Since the transpositions `(j, j + 2^i)` in `ξ_{n,i}` are pairwise disjoint (their supports
`{j, j + 2^i}` are disjoint for distinct `j`), their product is an involution.

*Key inequality:* `j ≤ J(n,i) ≤ 2^i`, so `j < 2^i < j + 2^i` — no two supports overlap.

---

### Theorem 5.16: `Ξ_n` is Complete in `Sn` (Main Goal)

**Statement:** For all `n : ℕ`, `Ξ_n` is a generating sequence for `Sn`.

**Proof by induction on n:**

*Base case* (`n = 1`): `Ξ_1 = []`, `⟪⟫[]⟫⟫ = {id} = S1`. ✓

*Inductive step* (`n > 1`, IH: `Ξ_{n-1}` is a generating sequence for `S_{n-1}`):

Given arbitrary `σ ∈ Sn`, we show `σ ∈ ⟪⟫Ξ_n⟫⟫`.

**Step (i): Find `π_s` that maps `0` to `σ(0)`.**
Write `σ(0)` in binary: `σ(0) = ∑_{k=0}^{I(n)-1} s_k 2^k` with `s_k ∈ {0,1}`.
Define `π_s = ξ_{n,I(n)-1}^{s_{I(n)-1}} * … * ξ_{n,0}^{s_0}`.

*Sub-induction* shows `π_s(0) = σ(0)`, so `π_s⁻¹ * σ` fixes `0`, i.e., `π_s⁻¹σ ∈ Sn^0`.

The sub-induction uses: if `i₀ = ∑_{k=0}^{K-1} s_k 2^k + 1 ≤ J(n,K)`, then
`ξ_{n,K}(i₀) = i₀ + 2^K` (because `ξ_{n,K}` contains the transposition `(i₀, i₀+2^K)`
and its supports are disjoint, so it acts as exactly that swap on `i₀`).

**Step (ii): Conclude `σ ∈ ⟪⟫Ξ_n⟫⟫`.**
By IH, `Ξ_{n-1}` generates `S_{n-1}`. By Prop 5.11, `Ξ_{n-1}.map R` generates `Sn^0`.
Since `π_s⁻¹σ ∈ Sn^0`, we have `π_s⁻¹σ ∈ ⟪⟫Ξ_{n-1}.map R⟫⟫ ⊆ ⟪⟫Ξ_n⟫⟫`.
Then `σ = π_s * (π_s⁻¹σ) ∈ ⟪⟫Ξ_n⟫⟫` since `π_s ∈ ⟪⟫Ξ_n⟫⟫` by definition.  □

---

## Lean 4 Formalization Plan

### File Structure

```
GenSeq/
  Basic.lean        -- Imports and re-exports
  OrderedSpan.lean  -- orderedSpan, IsGeneratingSeq
  MapR.lean         -- The map R, Prop 5.10, Prop 5.11
  Sambale.lean      -- I, J, ξ_{n,i}, Ξ_n, Props 5.13–5.15, Thm 5.16
```

### Step 1: `orderedSpan` and `IsGeneratingSeq`

```lean
-- In OrderedSpan.lean
import Mathlib

variable {G : Type*} [Group G]

def orderedSpan : List G → Set G
  | []      => {1}
  | l ++ [g] => orderedSpan l ∪ (· * g) '' orderedSpan l

def IsGeneratingSeq (l : List G) (H : Subgroup G) : Prop :=
  ↑H = orderedSpan l
```

Key lemmas needed:
- `one_mem_orderedSpan : 1 ∈ orderedSpan l`
- `orderedSpan_append_singleton : orderedSpan (l ++ [g]) = ...`
- `map_orderedSpan_of_hom (f : G →* H) (l : List G) : f '' orderedSpan l = orderedSpan (l.map f)`
  (used in Prop 5.11)

### Step 2: The Map R (`MapR.lean`)

```lean
-- Sn^0 = stabiliser of (0 : Fin (n+1))
def stabZero (n : ℕ) : Subgroup (Equiv.Perm (Fin (n+1))) :=
  MulAction.stabilizer (Equiv.Perm (Fin (n+1))) (0 : Fin (n+1))

-- R embeds Perm (Fin n) as stabZero n
def mapR (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n+1)) :=
  -- extendDomain along Fin.succ : Fin n ↪ Fin (n+1)
  (Equiv.Perm.extendDomain (Fin.succEmb n))  -- or similar
```

Check `Equiv.Perm.extendDomain` in Mathlib; if unavailable, define directly:
```lean
def mapR' (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun    := fun i => if h : i = 0 then 0 else Fin.succ (σ (i.pred h))
  invFun   := fun i => if h : i = 0 then 0 else Fin.succ (σ.symm (i.pred h))
  ...
```

Key lemmas:
- `mapR_isGroupHom` : `mapR` is a group homomorphism
- `mapR_image_eq_stabZero` : `(mapR n).range = stabZero n` (Prop 5.10)
- `mapR_injective` : `mapR` is injective

### Step 3: Sambale Sequence (`Sambale.lean`)

```lean
-- Helper functions
def capLog (n : ℕ) : ℕ := Nat.clog 2 n  -- = ⌈log₂ n⌉

def strideCount (n i : ℕ) : ℕ := min (n - 2^i) (2^i)

-- Single permutation ξ_{n,i} (0-indexed i)
def sambalePerm (n i : ℕ) : Equiv.Perm (Fin n) :=
  (Finset.range (strideCount n i)).prod (fun j =>
    Equiv.swap ⟨j, by omega⟩ ⟨j + 2^i, by omega⟩)

-- The Sambale sequence Ξ_n
def sambale : (n : ℕ) → List (Equiv.Perm (Fin n))
  | 0 => []
  | 1 => []
  | n + 2 =>
    (sambale (n+1)).map (mapR (n+1)) ++
    (Finset.range (capLog (n+2))).val.toList.map (sambalePerm (n+2))
```

### Step 4: Key Intermediate Lemmas

In order of dependency:

1. **`strideCount_last`** (Prop 5.14(i)):
   `strideCount n i = n - 2^i ↔ i + 1 = capLog n`

2. **`sambalePerm_involutive`** (Prop 5.15):
   `∀ n i, sambalePerm n i * sambalePerm n i = 1`
   - Show the transpositions `(j, j + 2^i)` are pairwise disjoint
   - Use `Equiv.swap_mul_self` and disjointness

3. **`mapR_preserves_genSeq`** (Prop 5.11):
   `IsGeneratingSeq l H → IsGeneratingSeq (l.map (mapR n)) (mapR n |>.range)`
   - Core: `orderedSpan (l.map f) = f '' orderedSpan l` for homomorphisms

4. **`sambalePerm_sends_zero`** (key sub-lemma for Thm 5.16 step (i)):
   For `s : Fin (capLog n) → Fin 2` (binary digits), the element
   `(Finset.range (capLog n)).prod (fun i => sambalePerm n i ^ s i)`
   maps `0` to `∑ i, s i * 2^i`.

### Step 5: Theorem 5.16

```lean
theorem sambale_isGeneratingSeq (n : ℕ) :
    IsGeneratingSeq (sambale n) ⊤ := by
  induction n with
  | zero => ...
  | one  => ...
  | succ n ih => ...
```

The inductive step:
1. Apply `mapR_preserves_genSeq` to IH → `sambale (n+1).map mapR` generates `stabZero n`
2. Show `stabZero n` = permutations fixing 0 ≅ `Sn`
3. For arbitrary `σ : Equiv.Perm (Fin (n+2))`, use `sambalePerm_sends_zero` to produce
   `π_s` with `π_s 0 = σ 0`, then `π_s⁻¹ * σ ∈ stabZero (n+1)` falls into the IH case

---

## Key Mathlib Lemmas to Locate

| Needed concept | Likely Mathlib name |
|---|---|
| Ceiling log₂ | `Nat.clog` |
| Transposition | `Equiv.swap` |
| `swap * swap = 1` | `Equiv.swap_swap` |
| Disjoint swaps commute/multiply | `Equiv.swap_mul_swap_mul_swap` or manual |
| Extend perm along embedding | `Equiv.Perm.extendDomain` |
| Stabiliser subgroup | `MulAction.stabilizer` |
| Product of Finset of perms | `Finset.prod` on `Equiv.Perm` |
| Range of group hom | `MonoidHom.range` |

---

## Implementation Order

1. `OrderedSpan.lean`: `orderedSpan`, `IsGeneratingSeq`, `map_orderedSpan_of_hom`
2. `MapR.lean`: `mapR`, `mapR_isGroupHom`, `mapR_image_eq_stabZero`
3. `Sambale.lean`:
   a. `capLog`, `strideCount`, `sambalePerm`, `sambale`
   b. `sambalePerm_involutive` (Prop 5.15)
   c. `mapR_preserves_genSeq` (Prop 5.11)
   d. `sambalePerm_sends_zero` (key step-i lemma)
   e. `sambale_isGeneratingSeq` (Theorem 5.16)

---

## Notes and Potential Pain Points

- **0-indexed vs 1-indexed**: The thesis uses 1-indexed `[n]`. All Lean code uses 0-indexed
  `Fin n`. Index translation: thesis `j ∈ [J(n,i)]` ↔ Lean `j : Fin (strideCount n i)`.

- **Recursive type of `sambale`**: Each level has type `List (Equiv.Perm (Fin n))`, so
  `mapR` must coerce `sambale (n-1)` up to type `Equiv.Perm (Fin n)` before appending.

- **`Nat.clog 2 0`**: `Nat.clog 2 0 = 0` in Mathlib (by convention), matching `I(1) = 0`
  after the shift.

- **`strideCount` bounds**: Must prove `j + 2^i < n` whenever `j < strideCount n i` to
  construct `Fin n` elements safely. This follows from `j < min(n - 2^i, 2^i) ≤ n - 2^i`.

- **Sorries as milestones**: Leave `sambalePerm_sends_zero` as a `sorry` initially and
  first close `sambale_isGeneratingSeq` conditionally on it — this validates the inductive
  structure before tackling the hardest sub-lemma.
