import Mathlib

variable {G H : Type*} [Group G] [Group H]

/-- The ordered span of a list `l = [g₁, …, gₘ]` is the set of all products
    `g₁^{b₁} * … * gₘ^{bₘ}` with `bᵢ ∈ {0, 1}`, built by `foldl` from the left. -/
def orderedSpan (l : List G) : Set G :=
  l.foldl (fun S g => S ∪ (· * g) '' S) {1}

/-- `l` is a generating sequence for subgroup `H` if `↑H = orderedSpan l` as sets. -/
def IsGeneratingSeq (l : List G) (H : Subgroup G) : Prop :=
  (H : Set G) = orderedSpan l

@[simp]
theorem orderedSpan_nil : orderedSpan ([] : List G) = {1} := rfl

theorem orderedSpan_append_singleton (l : List G) (g : G) :
    orderedSpan (l ++ [g]) = orderedSpan l ∪ (· * g) '' orderedSpan l := by
  simp [orderedSpan, List.foldl_append]

theorem one_mem_orderedSpan (l : List G) : (1 : G) ∈ orderedSpan l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    rw [orderedSpan_append_singleton]
    exact Set.mem_union_left _ ih

private lemma image_step (f : G →* H) (S : Set G) (g : G) :
    f '' (S ∪ (· * g) '' S) = f '' S ∪ (· * f g) '' (f '' S) := by
  rw [Set.image_union, Set.image_image, Set.image_image]
  congr 1
  ext x
  simp [map_mul]

/-- Group homomorphisms distribute over the ordered span:
    `f '' orderedSpan l = orderedSpan (l.map f)`. -/
theorem image_orderedSpan_of_hom (f : G →* H) (l : List G) :
    f '' orderedSpan l = orderedSpan (l.map f) := by
  induction l using List.reverseRecOn with
  | nil => simp [orderedSpan, map_one]
  | append_singleton l g ih =>
    rw [orderedSpan_append_singleton, image_step, ih, ← orderedSpan_append_singleton]
    simp [List.map_append]
