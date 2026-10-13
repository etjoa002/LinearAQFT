/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LocalAlgebrasLean.Region.Basic
import LocalAlgebrasLean.Lattice.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Causal indices

A causal index is the part of a spacetime that the Haag–Kastler axioms, in the form of
[Dimock] (Commun. Math. Phys. 77 (1980) 219–228, §1), use: a preordered set of regions with an
orthogonality relation (spacelike separation) and a dependence relation (causal dependence).
Points of spacetime do not appear.

Since milestone L2 of LocalAlgebrasLean (6 Oct 2026) the orthogonality relation is the region
index of that library (`LocalAlgebrasLean.RegionIndex`), shared with every theory built on it;
a causal index extends it with the dependence relation, and its isomorphisms extend the
isomorphisms of region indices. Statements, names and field names are those of milestone A.

The orthogonality fields carry the names of `CausalOrthogonality` in kencyke/quantum-system,
so that a bridge is a one-line instance (reuse assessment, milestone A, §6). A causal index is
a structure rather than a typeclass, so that one type of regions can carry several causal
structures (for example a spacetime and its time reversal).

## Main definitions

* `LinearAQFT.CausalIndex R`: orthogonality and dependence relations on a preorder `R`.
* `LinearAQFT.CausalIndex.Iso C C'`: order isomorphisms preserving and reflecting both.
* `LinearAQFT.CausalIndex.Aut C`: the automorphism group of a causal index.
-/

namespace LinearAQFT

open LocalAlgebrasLean

/-- A causal index on a preordered set `R` of regions (milestone A, Definition 1): a symmetric
orthogonality relation, antitone in its first argument (the region index it extends), and a
dependence relation, antitone in its first and monotone in its second argument. -/
structure CausalIndex (R : Type*) [Preorder R] extends RegionIndex R where
  /-- `Dependent O O'`: the region `O` is causally dependent on the region `O'`. -/
  Dependent : R → R → Prop
  dependent_mono_left : ∀ ⦃O₀ O O' : R⦄, O₀ ≤ O → Dependent O O' → Dependent O₀ O'
  dependent_mono_right : ∀ ⦃O O' O₁ : R⦄, Dependent O O' → O' ≤ O₁ → Dependent O O₁

namespace CausalIndex

variable {R R' R'' : Type*} [Preorder R] [Preorder R'] [Preorder R'']

theorem orthogonal_mono_right (C : CausalIndex R) ⦃O₁ O₂ O₃ : R⦄ (h : O₃ ≤ O₂)
    (hO : C.Orthogonal O₁ O₂) : C.Orthogonal O₁ O₃ :=
  C.toRegionIndex.orthogonal_mono_right h hO

/-- An isomorphism of causal indices (milestone A, Definition 2): an order isomorphism of the
regions that preserves and reflects orthogonality (an isomorphism of the region indices) and
dependence. -/
structure Iso (C : CausalIndex R) (C' : CausalIndex R') extends
    C.toRegionIndex.Iso C'.toRegionIndex where
  dependent_iff' : ∀ O O' : R, C'.Dependent (toOrderIso O) (toOrderIso O') ↔ C.Dependent O O'

namespace Iso

variable {C : CausalIndex R} {C' : CausalIndex R'} {C'' : CausalIndex R''}

instance : FunLike (C.Iso C') R R' where
  coe κ := κ.toOrderIso
  coe_injective κ₁ κ₂ h := by
    obtain ⟨⟨e₁, _⟩, _⟩ := κ₁
    obtain ⟨⟨e₂, _⟩, _⟩ := κ₂
    congr
    exact DFunLike.coe_injective h

@[simp] theorem coe_toOrderIso (κ : C.Iso C') : ⇑κ.toOrderIso = ⇑κ := rfl

/-- The underlying isomorphism of region indices acts as `κ`. -/
@[simp] theorem coe_toIso (κ : C.Iso C') : ⇑κ.toIso = ⇑κ := rfl

@[ext] theorem ext {κ₁ κ₂ : C.Iso C'} (h : ∀ O, κ₁ O = κ₂ O) : κ₁ = κ₂ :=
  DFunLike.ext _ _ h

theorem orthogonal_iff (κ : C.Iso C') (O₁ O₂ : R) :
    C'.Orthogonal (κ O₁) (κ O₂) ↔ C.Orthogonal O₁ O₂ :=
  κ.orthogonal_iff' O₁ O₂

theorem dependent_iff (κ : C.Iso C') (O O' : R) :
    C'.Dependent (κ O) (κ O') ↔ C.Dependent O O' :=
  κ.dependent_iff' O O'

theorem le_iff (κ : C.Iso C') (O O' : R) : κ O ≤ κ O' ↔ O ≤ O' :=
  κ.toOrderIso.le_iff_le

/-- The identity isomorphism. -/
protected def refl (C : CausalIndex R) : C.Iso C where
  toOrderIso := OrderIso.refl R
  orthogonal_iff' _ _ := Iff.rfl
  dependent_iff' _ _ := Iff.rfl

/-- The composite of two isomorphisms, first `κ₁` then `κ₂`. -/
protected def trans (κ₁ : C.Iso C') (κ₂ : C'.Iso C'') : C.Iso C'' where
  toOrderIso := κ₁.toOrderIso.trans κ₂.toOrderIso
  orthogonal_iff' O₁ O₂ := (κ₂.orthogonal_iff (κ₁ O₁) (κ₁ O₂)).trans (κ₁.orthogonal_iff O₁ O₂)
  dependent_iff' O O' := (κ₂.dependent_iff (κ₁ O) (κ₁ O')).trans (κ₁.dependent_iff O O')

private theorem apply_symm_apply' (κ : C.Iso C') (O' : R') : κ (κ.toOrderIso.symm O') = O' :=
  κ.toOrderIso.apply_symm_apply O'

/-- The inverse isomorphism. -/
protected def symm (κ : C.Iso C') : C'.Iso C where
  toOrderIso := κ.toOrderIso.symm
  orthogonal_iff' O₁ O₂ := by
    rw [← κ.orthogonal_iff, κ.apply_symm_apply', κ.apply_symm_apply']
  dependent_iff' O O' := by
    rw [← κ.dependent_iff, κ.apply_symm_apply', κ.apply_symm_apply']

@[simp] theorem refl_apply (O : R) : CausalIndex.Iso.refl C O = O := rfl

@[simp] theorem trans_apply (κ₁ : C.Iso C') (κ₂ : C'.Iso C'') (O : R) :
    κ₁.trans κ₂ O = κ₂ (κ₁ O) := rfl

@[simp] theorem symm_apply_apply (κ : C.Iso C') (O : R) : κ.symm (κ O) = O :=
  κ.toOrderIso.symm_apply_apply O

@[simp] theorem apply_symm_apply (κ : C.Iso C') (O' : R') : κ (κ.symm O') = O' :=
  κ.toOrderIso.apply_symm_apply O'

end Iso

/-- The automorphisms of a causal index. -/
abbrev Aut (C : CausalIndex R) := C.Iso C

/-- The automorphisms of a causal index form a group under composition; `κ₁ * κ₂` is
`κ₁ ∘ κ₂`. -/
instance (C : CausalIndex R) : Group C.Aut where
  mul κ₁ κ₂ := κ₂.trans κ₁
  one := Iso.refl C
  inv κ := κ.symm
  mul_assoc _ _ _ := Iso.ext fun _ => rfl
  one_mul _ := Iso.ext fun _ => rfl
  mul_one _ := Iso.ext fun _ => rfl
  inv_mul_cancel κ := Iso.ext fun O => Iso.symm_apply_apply κ O

@[simp] theorem Aut.mul_apply {C : CausalIndex R} (κ₁ κ₂ : C.Aut) (O : R) :
    (κ₁ * κ₂) O = κ₁ (κ₂ O) := rfl

@[simp] theorem Aut.one_apply {C : CausalIndex R} (O : R) : (1 : C.Aut) O = O := rfl

end CausalIndex

/-- The causal index of the subsets of a set of sites, without time: the region index of the sites
(orthogonal means disjoint) with dependence meaning inclusion, so that the time slice reduces to
isotony. Lattice automata (QCALean's `latticeIndex`) and propagation bounds (LocalityLean's
`latticeIndex`) kept equal copies of it before LocalAlgebrasLean's milestone L4 (6 Oct 2026). -/
def subsetCausalIndex (V : Type*) : CausalIndex (Set V) where
  toRegionIndex := LocalAlgebrasLean.subsetIndex V
  Dependent := (· ⊆ ·)
  dependent_mono_left _ _ _ h h' := h.trans h'
  dependent_mono_right _ _ _ h h' := h.trans h'

@[simp] theorem subsetCausalIndex_orthogonal {V : Type*} (O₁ O₂ : Set V) :
    (subsetCausalIndex V).Orthogonal O₁ O₂ ↔ Disjoint O₁ O₂ := Iff.rfl

@[simp] theorem subsetCausalIndex_dependent {V : Type*} (O O' : Set V) :
    (subsetCausalIndex V).Dependent O O' ↔ O ⊆ O' := Iff.rfl

end LinearAQFT
