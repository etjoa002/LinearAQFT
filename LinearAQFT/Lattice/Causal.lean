/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Causal.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Prod
import Mathlib.Order.Hom.Set
import Mathlib.Data.Set.Finite.Lattice

/-!
# The causal index of the lattice `ℤ²`

Points of `ℤ²` are pairs `(t, x)`. The causal order is `(t, x) ≤ (t', x')` iff
`|x' - x| ≤ t' - t`; it is a named relation, not an instance, since `ℤ × ℤ` carries Mathlib's
product order. Regions are all subsets, ordered by inclusion; orthogonality is that of
milestone A, Example 2, and milestone E1, Definition 1. Dependence is pointwise (stage F):
`O ◁ O'` iff every finite `Y ⊆ O` has a pair of slices with `J(Y) ∩ S_{t₁} ⊆ O'`.

## Main definitions

* `LinearAQFT.Lattice.causalLE`, `Comparable`, `causalShadow` (`J`), `slices` (`S_{t₁}`).
* `LinearAQFT.Lattice.causalIndex` (E1, Proposition 2).
* `LinearAQFT.Lattice.translate`, `translateHom` (E1, Proposition 2).
-/

namespace LinearAQFT

namespace Lattice

/-- A point of the lattice: `(t, x)`, time first. -/
abbrev Point := ℤ × ℤ

/-- E1, Definition 1: the causal order `(t, x) ≤ (t', x')` iff `|x' - x| ≤ t' - t`. -/
def causalLE (p q : Point) : Prop := |q.2 - p.2| ≤ q.1 - p.1

/-- Two points are comparable if one lies in the causal future of the other. -/
def Comparable (p q : Point) : Prop := causalLE p q ∨ causalLE q p

/-- The causal shadow `J(O)`: points comparable with a point of `O`. -/
def causalShadow (O : Set Point) : Set Point := {p | ∃ q ∈ O, Comparable p q}

/-- The pair of consecutive time slices `S_{t₁} = {(t, x) : t ∈ {t₁, t₁ + 1}}`. -/
def slices (t₁ : ℤ) : Set Point := {p | p.1 = t₁ ∨ p.1 = t₁ + 1}

theorem causalLE_refl (p : Point) : causalLE p p := by simp [causalLE]

theorem causalLE_trans {p q r : Point} (h₁ : causalLE p q) (h₂ : causalLE q r) :
    causalLE p r := by
  unfold causalLE at *
  calc |r.2 - p.2| = |(r.2 - q.2) + (q.2 - p.2)| := by ring_nf
    _ ≤ |r.2 - q.2| + |q.2 - p.2| := abs_add_le _ _
    _ ≤ r.1 - p.1 := by linarith

theorem causalLE_antisymm {p q : Point} (h₁ : causalLE p q) (h₂ : causalLE q p) : p = q := by
  unfold causalLE at *
  have ht : q.1 = p.1 := by
    have := abs_nonneg (q.2 - p.2); have := abs_nonneg (p.2 - q.2); linarith
  have hx : |q.2 - p.2| ≤ 0 := by rw [ht] at h₁; simpa using h₁
  have hx' : q.2 - p.2 = 0 := abs_eq_zero.1 (le_antisymm hx (abs_nonneg _))
  exact Prod.ext ht.symm (by linarith)

theorem comparable_comm {p q : Point} : Comparable p q ↔ Comparable q p := Or.comm

theorem comparable_sub (a p q : Point) : Comparable (p - a) (q - a) ↔ Comparable p q := by
  simp only [Comparable, causalLE]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right]

/-- E1, Proposition 2: the causal index of the lattice. -/
def causalIndex : CausalIndex (Set Point) where
  Orthogonal O₁ O₂ := ∀ p ∈ O₁, ∀ q ∈ O₂, ¬ Comparable p q
  orthogonal_symm _ _ h p hp q hq hpq := h q hq p hp (comparable_comm.1 hpq)
  orthogonal_mono_left _ _ _ h₀ h p hp q hq := h p (h₀ hp) q hq
  Dependent O O' := ∀ Y : Set Point, Y.Finite → Y ⊆ O → ∃ t₁, causalShadow Y ∩ slices t₁ ⊆ O'
  dependent_mono_left _ _ _ h₀ h Y hY hYO := h Y hY (hYO.trans h₀)
  dependent_mono_right _ _ _ h h₁ Y hY hYO := (h Y hY hYO).imp fun _ ht => ht.trans h₁

theorem causalIndex_orthogonal (O₁ O₂ : Set Point) :
    causalIndex.Orthogonal O₁ O₂ ↔ ∀ p ∈ O₁, ∀ q ∈ O₂, ¬ Comparable p q := Iff.rfl

theorem causalIndex_dependent (O O' : Set Point) :
    causalIndex.Dependent O O' ↔
      ∀ Y : Set Point, Y.Finite → Y ⊆ O → ∃ t₁, causalShadow Y ∩ slices t₁ ⊆ O' := Iff.rfl

theorem causalShadow_mono {O O' : Set Point} (h : O ⊆ O') : causalShadow O ⊆ causalShadow O' :=
  fun _ ⟨q, hq, hpq⟩ => ⟨q, h hq, hpq⟩

/-- One pair of slices for the whole region gives dependence. -/
theorem causalIndex_dependent_of_slices {O O' : Set Point} {t₁ : ℤ}
    (h : causalShadow O ∩ slices t₁ ⊆ O') : causalIndex.Dependent O O' :=
  fun _ _ hYO => ⟨t₁, fun _ ⟨hp, hs⟩ => h ⟨causalShadow_mono hYO hp, hs⟩⟩

/-- Translation of regions by `a`: `O ↦ O + a = {p | p - a ∈ O}`. -/
def translateOrderIso (a : Point) : Set Point ≃o Set Point where
  toFun O := (fun p => p - a) ⁻¹' O
  invFun O := (fun p => p + a) ⁻¹' O
  left_inv O := by ext p; simp
  right_inv O := by ext p; simp
  map_rel_iff' {O O'} := by
    constructor
    · intro h p hp
      have := @h (p + a) (by simpa using hp)
      simpa using this
    · intro h p hp
      exact h hp

theorem mem_translate {a p : Point} {O : Set Point} :
    p ∈ translateOrderIso a O ↔ p - a ∈ O := Iff.rfl

theorem causalShadow_translate (a : Point) (O : Set Point) :
    causalShadow (translateOrderIso a O) = translateOrderIso a (causalShadow O) := by
  ext p
  simp only [causalShadow, mem_translate, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, hpq⟩
    exact ⟨q - a, hq, (comparable_sub a p q).2 hpq⟩
  · rintro ⟨q, hq, hpq⟩
    refine ⟨q + a, by simpa using hq, ?_⟩
    rw [← comparable_sub a]
    simpa using hpq

theorem slices_translate (a : Point) (t₁ : ℤ) :
    slices (t₁ + a.1) = translateOrderIso a (slices t₁) := by
  ext p
  simp only [slices, mem_translate, Set.mem_ofPred_eq, Prod.fst_sub]
  omega

theorem exists_slices_translate_iff (a : Point) (Y O' : Set Point) :
    (∃ t₁, causalShadow (translateOrderIso a Y) ∩ slices t₁ ⊆ translateOrderIso a O') ↔
      ∃ t₁, causalShadow Y ∩ slices t₁ ⊆ O' := by
  constructor
  · rintro ⟨t₁, h⟩
    refine ⟨t₁ - a.1, fun p hp => ?_⟩
    have h' := @h (p + a)
    simp only [causalShadow_translate, Set.mem_inter_iff, mem_translate, add_sub_cancel_right]
      at h'
    refine h' ⟨hp.1, ?_⟩
    have := hp.2
    simp only [slices, Set.mem_ofPred_eq, Prod.fst_add] at this ⊢
    omega
  · rintro ⟨t₁, h⟩
    refine ⟨t₁ + a.1, fun p hp => ?_⟩
    rw [causalShadow_translate, slices_translate] at hp
    exact h ⟨hp.1, hp.2⟩

/-- E1, Proposition 2: translation by `a` is an automorphism of the lattice causal index. -/
def translate (a : Point) : causalIndex.Aut where
  toOrderIso := translateOrderIso a
  orthogonal_iff' O₁ O₂ := by
    simp only [causalIndex_orthogonal, mem_translate]
    constructor
    · intro h p hp q hq hpq
      exact h (p + a) (by simpa using hp) (q + a) (by simpa using hq)
        (by rw [← comparable_sub a]; simpa using hpq)
    · intro h p hp q hq hpq
      exact h _ hp _ hq ((comparable_sub a p q).2 hpq)
  dependent_iff' O O' := by
    simp only [causalIndex_dependent]
    constructor
    · intro h Y hY hYO
      have hfin : (translateOrderIso a Y).Finite :=
        Set.Finite.preimage (f := fun p : Point => p - a)
          (fun _ _ _ _ h => by simpa using h) hY
      exact (exists_slices_translate_iff a Y O').1
        (h _ hfin ((translateOrderIso a).monotone hYO))
    · intro h Y hY hYO
      have hY₀ : (translateOrderIso a).symm Y ⊆ O := by
        rw [← (translateOrderIso a).le_iff_le, OrderIso.apply_symm_apply]
        exact hYO
      have hfin : ((translateOrderIso a).symm Y).Finite :=
        Set.Finite.preimage (f := fun p : Point => p + a)
          (fun _ _ _ _ h => by simpa using h) hY
      have := (exists_slices_translate_iff a ((translateOrderIso a).symm Y) O').2
        (h _ hfin hY₀)
      rwa [OrderIso.apply_symm_apply] at this

@[simp] theorem translate_apply (a : Point) (O : Set Point) :
    translate a O = (fun p => p - a) ⁻¹' O := rfl

/-- E1, Proposition 2: `a ↦ (O ↦ O + a)` is a group homomorphism into the automorphisms. -/
def translateHom : Multiplicative Point →* causalIndex.Aut where
  toFun a := translate a.toAdd
  map_one' := by
    apply CausalIndex.Iso.ext; intro O; ext p; simp
  map_mul' a b := by
    apply CausalIndex.Iso.ext; intro O; ext p
    simp [sub_sub]

end Lattice

end LinearAQFT
