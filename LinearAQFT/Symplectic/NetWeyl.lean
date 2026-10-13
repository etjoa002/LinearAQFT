/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Symplectic.Net
import BosonicLean.Weyl.State

/-!
# Weyl operators in the local algebras of the CCR net

For phase-space data `Φ`, the local algebra `ccrNet Φ O` of a region `O` is the norm closure of
the linear span of the Weyl operators `W(cls f)` of the test functions `f` localized in `O`, and a
Weyl operator `W(v)` lies in it exactly when `v` is the class of such a test function. These facts
hold for every `Φ`; QCALean's lattice phase space (milestone Q5b, Lemma 18) is an instance.
Moved here from QCALean under the placement rule (QCALean milestone Q6).

## Main statements

* `coe_ccrNet_eq_closure_span`: `ccrNet Φ O` is the closed span of its Weyl operators.
* `wCCR_mem_ccrNet_iff_exists`: `W(v) ∈ ccrNet Φ O` iff `v = cls f` for some `f ∈ loc O`.
* `eqOn_ccrNet`, `map_mem_ccrNet`: continuous linear maps are determined on a local algebra by
  its Weyl operators, and map it into another local algebra if its Weyl operators do.
-/

namespace LinearAQFT.Symplectic

open BosonicLean.Weyl

variable {R : Type*} [Preorder R] {C : CausalIndex R}
variable {D V : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup V] [Module ℝ V]

/-- The Weyl operators `W(cls f)` of the test functions localized in `O`. -/
def weylSet (Φ : PhaseSpace C D V) (O : R) : Set (CCR Φ.sigma) :=
  (fun f => wCCR Φ.sigma (Φ.cls f)) '' (Φ.loc O : Set D)

theorem mem_weylSet {Φ : PhaseSpace C D V} {O : R} {a : CCR Φ.sigma} :
    a ∈ weylSet Φ O ↔ ∃ f ∈ Φ.loc O, wCCR Φ.sigma (Φ.cls f) = a := by
  simp [weylSet]

/-- The generators of the CCR net are the Weyl operators of the localized test functions. -/
theorem generators_ccr_eq (Φ : PhaseSpace C D V) (O : R) :
    generators Φ (CCR.weylSystem Φ.sigma Φ.isAlt) O = weylSet Φ O := by
  rw [generators_apply, weylSet]
  rfl

/-- The span of the Weyl operators of `O` is closed under products. -/
theorem mul_mem_span_weylSet {Φ : PhaseSpace C D V} {O : R} {x y : CCR Φ.sigma}
    (hx : x ∈ Submodule.span ℂ (weylSet Φ O)) (hy : y ∈ Submodule.span ℂ (weylSet Φ O)) :
    x * y ∈ Submodule.span ℂ (weylSet Φ O) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := mem_weylSet.1 hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, hg, rfl⟩ := mem_weylSet.1 hy
      rw [wCCR_mul Φ.isAlt, ← map_add]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (mem_weylSet.2 ⟨f + g, add_mem hf hg, rfl⟩))
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- The span of the Weyl operators of `O` is closed under the adjoint. -/
theorem star_mem_span_weylSet {Φ : PhaseSpace C D V} {O : R} {x : CCR Φ.sigma}
    (hx : x ∈ Submodule.span ℂ (weylSet Φ O)) : star x ∈ Submodule.span ℂ (weylSet Φ O) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := mem_weylSet.1 hx
    have hs : star (wCCR Φ.sigma (Φ.cls f)) = wCCR Φ.sigma (Φ.cls (-f)) := by
      rw [map_neg]
      exact (CCR.weylSystem _ Φ.isAlt).star_eq Φ.isAlt _
    rw [hs]
    exact Submodule.subset_span (mem_weylSet.2 ⟨-f, neg_mem hf, rfl⟩)
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

/-- QCALean milestone Q5b, Lemma 18(a), for every `Φ`: the local algebra of `O` is the closed
span of the Weyl operators of the test functions localized in `O`. -/
theorem coe_ccrNet_eq_closure_span (Φ : PhaseSpace C D V) (O : R) :
    ((ccrNet Φ O : StarSubalgebra ℂ _) : Set (CCR Φ.sigma)) =
      closure (Submodule.span ℂ (weylSet Φ O)) := by
  have hone : (1 : CCR Φ.sigma) ∈ Submodule.span ℂ (weylSet Φ O) := by
    rw [← wCCR_zero, ← map_zero Φ.cls]
    exact Submodule.subset_span (mem_weylSet.2 ⟨0, zero_mem _, rfl⟩)
  let S : StarSubalgebra ℂ (CCR Φ.sigma) :=
    { (Submodule.span ℂ _).toSubalgebra hone (fun _ _ hx hy => mul_mem_span_weylSet hx hy) with
      star_mem' := fun hx => star_mem_span_weylSet hx }
  have h1 := Net.generated_apply (generators Φ (CCR.weylSystem Φ.sigma Φ.isAlt)) O
  rw [generators_ccr_eq] at h1
  change ((ccrNet Φ O : StarSubalgebra ℂ _) : Set (CCR Φ.sigma)) = _
  rw [show ccrNet Φ O = _ from h1, StarSubalgebra.topologicalClosure_coe]
  refine subset_antisymm (closure_mono ?_) (closure_mono ?_)
  · exact StarAlgebra.adjoin_le (S := S) (fun _ hx => Submodule.subset_span hx)
  · intro x hx
    exact (Submodule.span_le (p := (StarAlgebra.adjoin ℂ _).toSubalgebra.toSubmodule)).2
      (StarAlgebra.subset_adjoin ℂ _) hx

/-- QCALean milestone Q5b, Lemma 18(b), for every `Φ`: a Weyl operator `W(v)` lies in the local
algebra of `O` iff `v` is the class of a test function localized in `O`. -/
theorem wCCR_mem_ccrNet_iff_exists (Φ : PhaseSpace C D V) (O : R) (v : V) :
    wCCR Φ.sigma v ∈ ccrNet Φ O ↔ ∃ f ∈ Φ.loc O, Φ.cls f = v := by
  classical
  constructor
  · intro hv
    by_contra hsub
    have hv' : wCCR Φ.sigma v ∈ closure (Submodule.span ℂ (weylSet Φ O) : Set (CCR Φ.sigma)) := by
      rw [← coe_ccrNet_eq_closure_span]; exact hv
    let ψ := (testFun Φ.sigma v).comp (CCR Φ.sigma).toSubalgebra.toSubmodule.subtypeL
    have hle : Submodule.span ℂ (weylSet Φ O) ≤
        LinearMap.ker (ψ : CCR Φ.sigma →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      intro a ha
      obtain ⟨f, hf, rfl⟩ := mem_weylSet.1 ha
      have hfv : Φ.cls f ≠ v := fun h => hsub ⟨f, hf, h⟩
      change testFun Φ.sigma v (weyl Φ.sigma (Φ.cls f)) = 0
      rw [testFun_weyl Φ.isAlt]
      simp [hfv]
    have h0 : ψ (wCCR Φ.sigma v) = 0 := (closure_minimal hle ψ.isClosed_ker) hv'
    change testFun Φ.sigma v (weyl Φ.sigma v) = 0 at h0
    rw [testFun_weyl Φ.isAlt] at h0
    simp at h0
  · rintro ⟨f, hf, rfl⟩
    have : wCCR Φ.sigma (Φ.cls f) ∈ ((ccrNet Φ O : StarSubalgebra ℂ _) : Set (CCR Φ.sigma)) := by
      rw [coe_ccrNet_eq_closure_span]
      exact subset_closure (Submodule.subset_span (mem_weylSet.2 ⟨f, hf, rfl⟩))
    exact this

/-- Continuous linear maps agreeing on the Weyl operators of `O` agree on the local algebra of
`O`. -/
theorem eqOn_ccrNet {Φ : PhaseSpace C D V} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : CCR Φ.sigma →L[ℂ] E} {O : R}
    (h : ∀ t ∈ Φ.loc O, f (wCCR Φ.sigma (Φ.cls t)) = g (wCCR Φ.sigma (Φ.cls t)))
    {x : CCR Φ.sigma} (hx : x ∈ ccrNet Φ O) : f x = g x := by
  have hx' : x ∈ closure (Submodule.span ℂ (weylSet Φ O) : Set (CCR Φ.sigma)) := by
    rw [← coe_ccrNet_eq_closure_span]; exact hx
  have hW : Set.EqOn f g (weylSet Φ O) := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := mem_weylSet.1 ha
    exact h t ht
  exact ((LinearMap.eqOn_span' (f := f.toLinearMap) (g := g.toLinearMap) hW).closure
    f.continuous g.continuous) hx'

/-- A continuous linear map sending the Weyl operators of `O` into the local algebra of `O'` maps
the local algebra of `O` into that of `O'`. -/
theorem map_mem_ccrNet {Φ : PhaseSpace C D V} {f : CCR Φ.sigma →L[ℂ] CCR Φ.sigma} {O O' : R}
    (h : ∀ t ∈ Φ.loc O, f (wCCR Φ.sigma (Φ.cls t)) ∈ ccrNet Φ O')
    {x : CCR Φ.sigma} (hx : x ∈ ccrNet Φ O) : f x ∈ ccrNet Φ O' := by
  have hx' : x ∈ closure (Submodule.span ℂ (weylSet Φ O) : Set (CCR Φ.sigma)) := by
    rw [← coe_ccrNet_eq_closure_span]; exact hx
  have hspan : Submodule.span ℂ (weylSet Φ O) ≤
      (ccrNet Φ O').toSubalgebra.toSubmodule.comap f.toLinearMap := by
    rw [Submodule.span_le]
    intro a ha
    obtain ⟨t, ht, rfl⟩ := mem_weylSet.1 ha
    exact h t ht
  have hcl : f x ∈ closure ((ccrNet Φ O' : StarSubalgebra ℂ _) : Set (CCR Φ.sigma)) :=
    map_mem_closure f.continuous hx' fun y hy => hspan hy
  rwa [((ccrNet Φ).isClosed O').closure_eq] at hcl

end LinearAQFT.Symplectic
