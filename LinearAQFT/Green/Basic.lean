/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Causal.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Green data

Stage F, item 1 and 2. Green data (interface I4) consist of points with a causal relation,
functions with supports, test functions, an operator `P` with its restriction to test functions,
a pairing, retarded and advanced Green operators, and cutoffs with their time slabs. From the
points and the slabs we derive a causal index on the regions `Set X`.

## Main definitions

* `LinearAQFT.Green.GreenData`.
* `LinearAQFT.Green.GreenData.shadow`: the causal shadow `J(O)`.
* `LinearAQFT.Green.GreenData.causalIndex`: the derived causal index.
-/

namespace LinearAQFT.Green

/-- F, Definition 1: Green data. `causalLE p q` means that `q` lies in the causal future of `p`;
`gret` is the retarded Green operator (supported in the future) and `gadv` the advanced one. -/
structure GreenData (X D F : Type*) [AddCommGroup D] [Module ℝ D] [AddCommGroup F]
    [Module ℝ F] where
  /-- (G1) The causal relation. -/
  causalLE : X → X → Prop
  /-- (G2) The support of a function. -/
  supp : F → Set X
  supp_zero : supp 0 = ∅
  supp_add : ∀ h h' : F, supp (h + h') ⊆ supp h ∪ supp h'
  supp_smul : ∀ (c : ℝ) (h : F), supp (c • h) ⊆ supp h
  /-- (G3) Test functions as functions. -/
  incl : D →ₗ[ℝ] F
  /-- (G4) The operator, and its restriction to test functions. -/
  P : F →ₗ[ℝ] F
  Ptest : D →ₗ[ℝ] D
  incl_Ptest : ∀ f, incl (Ptest f) = P (incl f)
  /-- (G5) The pairing of a test function with a function: local and nondegenerate. -/
  pairing : D →ₗ[ℝ] F →ₗ[ℝ] ℝ
  pairing_eq_zero : ∀ f h, Disjoint (supp (incl f)) (supp h) → pairing f h = 0
  pairing_nondegenerate : ∀ h, (∀ f, pairing f h = 0) → h = 0
  /-- (G6) The Green operators. -/
  gret : D →ₗ[ℝ] F
  gadv : D →ₗ[ℝ] F
  P_gret : ∀ f, P (gret f) = incl f
  P_gadv : ∀ f, P (gadv f) = incl f
  gret_Ptest : ∀ f, gret (Ptest f) = incl f
  gadv_Ptest : ∀ f, gadv (Ptest f) = incl f
  supp_gret : ∀ f, supp (gret f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE p q}
  supp_gadv : ∀ f, supp (gadv f) ⊆ {q | ∃ p ∈ supp (incl f), causalLE q p}
  adjoint : ∀ f g, pairing f (gret g) = pairing g (gadv f)
  /-- (G7) Cutoffs `χ` and their slabs. -/
  Cutoff : Type
  chi : Cutoff → F →ₗ[ℝ] F
  slab : Cutoff → Set X
  /-- (c1) `supp P(χ E f) ⊆ S ∩ J(supp f)`. -/
  supp_P_chi_E : ∀ c f, supp (P (chi c (gadv f - gret f))) ⊆
    slab c ∩ {q | ∃ p ∈ supp (incl f), causalLE p q ∨ causalLE q p}
  /-- (c2) `(1 - χ) G⁺ f + χ G⁻ f` is a test function. -/
  exists_test : ∀ c f, ∃ k : D, incl k = (gret f - chi c (gret f)) + chi c (gadv f)

namespace GreenData

variable {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F] [Module ℝ F]
variable (G : GreenData X D F)

/-- `p` and `q` are comparable: one lies in the causal future of the other. -/
def Comparable (p q : X) : Prop := G.causalLE p q ∨ G.causalLE q p

theorem comparable_comm {p q : X} : G.Comparable p q ↔ G.Comparable q p := Or.comm

/-- F, Definition 3: the causal shadow `J(O)`, the points comparable with a point of `O`. -/
def shadow (O : Set X) : Set X := {q | ∃ p ∈ O, G.Comparable p q}

theorem shadow_mono {O O' : Set X} (h : O ⊆ O') : G.shadow O ⊆ G.shadow O' :=
  fun _ ⟨p, hp, hpq⟩ => ⟨p, h hp, hpq⟩

/-- F, Definition 3 and Lemma 4: the derived causal index on the regions `Set X`. Dependence is
pointwise: every test function supported in `O` has a slab `S` with `S ∩ J(supp f) ⊆ O'`. -/
def causalIndex : CausalIndex (Set X) where
  Orthogonal O₁ O₂ := ∀ p ∈ O₁, ∀ q ∈ O₂, ¬ G.Comparable p q
  orthogonal_symm _ _ h p hp q hq hpq := h q hq p hp ((G.comparable_comm).1 hpq)
  orthogonal_mono_left _ _ _ h₀ h p hp q hq := h p (h₀ hp) q hq
  Dependent O O' := ∀ f : D, G.supp (G.incl f) ⊆ O →
    ∃ c, G.slab c ∩ G.shadow (G.supp (G.incl f)) ⊆ O'
  dependent_mono_left _ _ _ h₀ h f hf := h f (hf.trans h₀)
  dependent_mono_right _ _ _ h h₁ f hf := (h f hf).imp fun _ hc => hc.trans h₁

theorem causalIndex_orthogonal (O₁ O₂ : Set X) :
    G.causalIndex.Orthogonal O₁ O₂ ↔ ∀ p ∈ O₁, ∀ q ∈ O₂, ¬ G.Comparable p q := Iff.rfl

theorem causalIndex_dependent (O O' : Set X) :
    G.causalIndex.Dependent O O' ↔ ∀ f : D, G.supp (G.incl f) ⊆ O →
      ∃ c, G.slab c ∩ G.shadow (G.supp (G.incl f)) ⊆ O' := Iff.rfl

/-- One slab for the whole region gives dependence. -/
theorem causalIndex_dependent_of_slab {O O' : Set X} {c : G.Cutoff}
    (h : G.slab c ∩ G.shadow O ⊆ O') : G.causalIndex.Dependent O O' :=
  fun _ hf => ⟨c, fun _ ⟨hs, hq⟩ => h ⟨hs, G.shadow_mono hf hq⟩⟩

/-! ### Supports -/

theorem supp_neg (h : F) : G.supp (-h) ⊆ G.supp h := by
  simpa using G.supp_smul (-1) h

theorem supp_sub (h h' : F) : G.supp (h - h') ⊆ G.supp h ∪ G.supp h' := by
  rw [sub_eq_add_neg]
  exact (G.supp_add _ _).trans (Set.union_subset_union_right _ (G.supp_neg h'))

end GreenData

end LinearAQFT.Green
