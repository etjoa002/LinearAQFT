/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Green.PhaseSpace

/-!
# Symmetries of Green data

Stage F, item 4. A symmetry of Green data is a bijection of points preserving the causal
relation, with linear bijections of test functions and functions that transport supports,
commute with the Green operators and preserve the pairing, and a bijection of the cutoffs that
transports the slabs. It gives an automorphism of the derived phase-space data, with the
composition law.

## Main results

* `GreenData.Symmetry`, `Symmetry.refl`, `Symmetry.trans`.
* `Symmetry.iso`: the automorphism of `G.phaseSpace`; `iso_T_mk`, `refl_iso_T`, `trans_iso_T`.
-/

namespace LinearAQFT.Green

namespace GreenData

open Symplectic

variable {X D F : Type*} [AddCommGroup D] [Module ℝ D] [AddCommGroup F] [Module ℝ F]
variable (G : GreenData X D F)

/-- F, Definition 10: a symmetry of Green data. Commuting with `G±` is part of the definition. -/
structure Symmetry where
  pointEquiv : X ≃ X
  causalLE_iff : ∀ p q, G.causalLE (pointEquiv p) (pointEquiv q) ↔ G.causalLE p q
  pushD : D ≃ₗ[ℝ] D
  pushF : F ≃ₗ[ℝ] F
  incl_pushD : ∀ f, G.incl (pushD f) = pushF (G.incl f)
  supp_pushF : ∀ h, G.supp (pushF h) = pointEquiv '' G.supp h
  gret_pushD : ∀ f, G.gret (pushD f) = pushF (G.gret f)
  gadv_pushD : ∀ f, G.gadv (pushD f) = pushF (G.gadv f)
  pairing_push : ∀ f h, G.pairing (pushD f) (pushF h) = G.pairing f h
  cutoffEquiv : G.Cutoff ≃ G.Cutoff
  slab_cutoffEquiv : ∀ c, G.slab (cutoffEquiv c) = pointEquiv '' G.slab c

/-- The order isomorphism of regions `O ↦ e '' O`, written as `e.symm ⁻¹' O`. -/
def imageOrderIso (e : X ≃ X) : Set X ≃o Set X where
  toFun O := e.symm ⁻¹' O
  invFun O := e ⁻¹' O
  left_inv O := by ext p; simp
  right_inv O := by ext p; simp
  map_rel_iff' {O O'} := by
    constructor
    · intro h p hp
      have := @h (e p) (by simpa using hp)
      simpa using this
    · intro h p hp
      exact h hp

theorem imageOrderIso_apply (e : X ≃ X) (O : Set X) : imageOrderIso e O = e '' O :=
  (e.image_eq_preimage_symm O).symm

namespace Symmetry

variable {G}
variable (s : G.Symmetry)

theorem comparable_iff (p q : X) :
    G.Comparable (s.pointEquiv p) (s.pointEquiv q) ↔ G.Comparable p q := by
  unfold Comparable
  rw [s.causalLE_iff, s.causalLE_iff]

theorem shadow_image (O : Set X) :
    G.shadow (s.pointEquiv '' O) = s.pointEquiv '' G.shadow O := by
  ext q
  constructor
  · rintro ⟨_, ⟨p, hp, rfl⟩, hpq⟩
    refine ⟨s.pointEquiv.symm q, ⟨p, hp, ?_⟩, by simp⟩
    rw [← s.comparable_iff]
    simpa using hpq
  · rintro ⟨q', ⟨p, hp, hpq⟩, rfl⟩
    exact ⟨s.pointEquiv p, ⟨p, hp, rfl⟩, (s.comparable_iff p q').2 hpq⟩

theorem supp_incl_pushD (f : D) :
    G.supp (G.incl (s.pushD f)) = s.pointEquiv '' G.supp (G.incl f) := by
  rw [s.incl_pushD, s.supp_pushF]

theorem slab_shadow_image_subset_iff (c : G.Cutoff) (S O' : Set X) :
    G.slab (s.cutoffEquiv c) ∩ G.shadow (s.pointEquiv '' S) ⊆ s.pointEquiv '' O' ↔
      G.slab c ∩ G.shadow S ⊆ O' := by
  rw [s.slab_cutoffEquiv, s.shadow_image, ← Set.image_inter s.pointEquiv.injective,
    Set.image_subset_image_iff s.pointEquiv.injective]

/-- The automorphism of the derived causal index induced by a symmetry. -/
def kappa : G.causalIndex.Aut where
  toOrderIso := imageOrderIso s.pointEquiv
  orthogonal_iff' O₁ O₂ := by
    simp only [imageOrderIso_apply, causalIndex_orthogonal]
    constructor
    · intro h p hp q hq
      rw [← s.comparable_iff]
      exact h _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    · rintro h _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      rw [s.comparable_iff]
      exact h p hp q hq
  dependent_iff' O O' := by
    simp only [imageOrderIso_apply, causalIndex_dependent]
    constructor
    · intro h f hf
      have hsupp := s.supp_incl_pushD f
      obtain ⟨c', hc'⟩ := h (s.pushD f) (by
        rw [hsupp]
        exact Set.image_mono hf)
      refine ⟨s.cutoffEquiv.symm c', (s.slab_shadow_image_subset_iff _ _ _).1 ?_⟩
      rwa [Equiv.apply_symm_apply, ← hsupp]
    · intro h f hf
      have hsupp := s.supp_incl_pushD (s.pushD.symm f)
      rw [LinearEquiv.apply_symm_apply] at hsupp
      obtain ⟨c, hc⟩ := h (s.pushD.symm f) (by
        rw [← Set.image_subset_image_iff s.pointEquiv.injective, ← hsupp]
        exact hf)
      refine ⟨s.cutoffEquiv c, ?_⟩
      rw [hsupp]
      exact (s.slab_shadow_image_subset_iff _ _ _).2 hc

theorem kappa_apply (O : Set X) : s.kappa O = s.pointEquiv '' O :=
  imageOrderIso_apply _ O

theorem E_pushD (f : D) : G.E (s.pushD f) = s.pushF (G.E f) := by
  rw [E_apply, E_apply, s.gadv_pushD, s.gret_pushD, map_sub]

theorem map_ker_E :
    (LinearMap.ker G.E).map (s.pushD : D →ₗ[ℝ] D) = LinearMap.ker G.E := by
  ext g
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.mem_ker, LinearEquiv.coe_coe]
  have := s.E_pushD (s.pushD.symm g)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this, LinearEquiv.map_eq_zero_iff]

/-- F, Proposition 11: a symmetry gives an automorphism of the derived phase-space data. -/
def iso : G.phaseSpace.Iso G.phaseSpace where
  kappa := s.kappa
  push := s.pushD
  map_loc O := by
    ext g
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, s.kappa_apply]
    change G.supp (G.incl (s.pushD.symm g)) ⊆ O ↔ G.supp (G.incl g) ⊆ s.pointEquiv '' O
    have hg := s.supp_incl_pushD (s.pushD.symm g)
    rw [LinearEquiv.apply_symm_apply] at hg
    rw [hg, Set.image_subset_image_iff s.pointEquiv.injective]
  T := Submodule.Quotient.equiv _ _ s.pushD s.map_ker_E
  cls_push _ := rfl
  symplectic u v := by
    induction u using Submodule.Quotient.induction_on with
    | H f =>
    induction v using Submodule.Quotient.induction_on with
    | H g =>
      change G.pairing (s.pushD f) (G.E (s.pushD g)) = G.pairing f (G.E g)
      rw [s.E_pushD, s.pairing_push]

/-- F, Proposition 11: `L_γ [f] = [γ_D f]`. -/
theorem iso_T_mk (f : D) :
    s.iso.T (Submodule.Quotient.mk f) = Submodule.Quotient.mk (s.pushD f) := rfl

end Symmetry

/-- F, Proposition 11: the identity symmetry. -/
def Symmetry.refl : G.Symmetry where
  pointEquiv := Equiv.refl X
  causalLE_iff _ _ := Iff.rfl
  pushD := LinearEquiv.refl ℝ D
  pushF := LinearEquiv.refl ℝ F
  incl_pushD _ := rfl
  supp_pushF _ := (Set.image_id _).symm
  gret_pushD _ := rfl
  gadv_pushD _ := rfl
  pairing_push _ _ := rfl
  cutoffEquiv := Equiv.refl _
  slab_cutoffEquiv _ := (Set.image_id _).symm

/-- F, Proposition 11: the composite of two symmetries, `s₁` first. -/
def Symmetry.trans (s₁ s₂ : G.Symmetry) : G.Symmetry where
  pointEquiv := s₁.pointEquiv.trans s₂.pointEquiv
  causalLE_iff p q := by
    simp only [Equiv.trans_apply]
    rw [s₂.causalLE_iff, s₁.causalLE_iff]
  pushD := s₁.pushD.trans s₂.pushD
  pushF := s₁.pushF.trans s₂.pushF
  incl_pushD f := by
    simp only [LinearEquiv.trans_apply]
    rw [s₂.incl_pushD, s₁.incl_pushD]
  supp_pushF h := by
    simp only [LinearEquiv.trans_apply, Equiv.coe_trans]
    rw [s₂.supp_pushF, s₁.supp_pushF, Set.image_image]
    rfl
  gret_pushD f := by
    simp only [LinearEquiv.trans_apply]
    rw [s₂.gret_pushD, s₁.gret_pushD]
  gadv_pushD f := by
    simp only [LinearEquiv.trans_apply]
    rw [s₂.gadv_pushD, s₁.gadv_pushD]
  pairing_push f h := by
    simp only [LinearEquiv.trans_apply]
    rw [s₂.pairing_push, s₁.pairing_push]
  cutoffEquiv := s₁.cutoffEquiv.trans s₂.cutoffEquiv
  slab_cutoffEquiv c := by
    simp only [Equiv.trans_apply, Equiv.coe_trans]
    rw [s₂.slab_cutoffEquiv, s₁.slab_cutoffEquiv, Set.image_image]
    rfl

/-- The inverse of a symmetry. With `Symmetry.refl` and `Symmetry.trans`, the symmetries form a
group. -/
def Symmetry.symm (s : G.Symmetry) : G.Symmetry where
  pointEquiv := s.pointEquiv.symm
  causalLE_iff p q := by
    rw [← s.causalLE_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  pushD := s.pushD.symm
  pushF := s.pushF.symm
  incl_pushD f := by
    apply s.pushF.injective
    rw [LinearEquiv.apply_symm_apply, ← s.incl_pushD, LinearEquiv.apply_symm_apply]
  supp_pushF h := by
    have := s.supp_pushF (s.pushF.symm h)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [this, Equiv.symm_image_image]
  gret_pushD f := by
    apply s.pushF.injective
    rw [LinearEquiv.apply_symm_apply, ← s.gret_pushD, LinearEquiv.apply_symm_apply]
  gadv_pushD f := by
    apply s.pushF.injective
    rw [LinearEquiv.apply_symm_apply, ← s.gadv_pushD, LinearEquiv.apply_symm_apply]
  pairing_push f h := by
    rw [← s.pairing_push, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  cutoffEquiv := s.cutoffEquiv.symm
  slab_cutoffEquiv c := by
    have := s.slab_cutoffEquiv (s.cutoffEquiv.symm c)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_image_image]

/-- The inverse symmetry acts on the phase space by the inverse map. -/
theorem Symmetry.symm_iso_T (s : G.Symmetry) :
    (Symmetry.symm G s).iso.T = s.iso.T.symm := by
  ext u
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    rw [LinearEquiv.eq_symm_apply]
    change Submodule.Quotient.mk (s.pushD (s.pushD.symm f)) = _
    rw [LinearEquiv.apply_symm_apply]

section Group

open BosonicLean.Weyl Net

variable {Γ : Type*} [Group Γ]

/-- A family of symmetries whose test-function maps compose as a group action acts on the CCR
algebra: `γ ↦ α_{L_γ}`. -/
noncomputable def symmetryAlphaHom (s : Γ → G.Symmetry) (h1 : ∀ f, (s 1).pushD f = f)
    (hmul : ∀ γ γ' f, (s (γ * γ')).pushD f = (s γ).pushD ((s γ').pushD f)) :
    Γ →* (CCR G.phaseSpace.sigma ≃⋆ₐ[ℂ] CCR G.phaseSpace.sigma) :=
  ccrAlphaHom (fun γ => (s γ).iso)
    (LinearEquiv.ext fun u => by
      induction u using Submodule.Quotient.induction_on with
      | H f => exact congrArg Submodule.Quotient.mk (h1 f))
    (fun γ γ' => LinearEquiv.ext fun u => by
      induction u using Submodule.Quotient.induction_on with
      | H f => exact congrArg Submodule.Quotient.mk (hmul γ γ' f))

theorem symmetryAlphaHom_apply (s : Γ → G.Symmetry) (h1 : ∀ f, (s 1).pushD f = f)
    (hmul : ∀ γ γ' f, (s (γ * γ')).pushD f = (s γ).pushD ((s γ').pushD f)) (γ : Γ) :
    G.symmetryAlphaHom s h1 hmul γ = ccrAlpha (s γ).iso := rfl

/-- A group acting on Green data by symmetries, with a homomorphic action `κ` on the regions and
test-function maps composing as a group action, acts on the CCR algebra, and the CCR net is
covariant. -/
theorem ccrNet_isCovariantUnder_symmetry (s : Γ → G.Symmetry) (h1 : ∀ f, (s 1).pushD f = f)
    (hmul : ∀ γ γ' f, (s (γ * γ')).pushD f = (s γ).pushD ((s γ').pushD f))
    (κ : Γ →* G.causalIndex.Aut) (hκ : ∀ γ, (s γ).kappa = κ γ) :
    IsCovariantUnder (ccrNet G.phaseSpace) κ (G.symmetryAlphaHom s h1 hmul) :=
  Symplectic.ccrNet_isCovariantUnder (fun γ => (s γ).iso) _ _ κ hκ

end Group

/-- F, Proposition 11: the identity symmetry acts trivially on the phase space. -/
theorem Symmetry.refl_iso_T : (Symmetry.refl G).iso.T = LinearEquiv.refl ℝ G.Phase := by
  ext u
  induction u using Submodule.Quotient.induction_on with
  | H f => rfl

/-- F, Proposition 11: composition law, `L_{γ₂ γ₁} = L_{γ₂} L_{γ₁}`. -/
theorem Symmetry.trans_iso_T (s₁ s₂ : G.Symmetry) :
    (Symmetry.trans G s₁ s₂).iso.T = s₁.iso.T.trans s₂.iso.T := by
  ext u
  induction u using Submodule.Quotient.induction_on with
  | H f => rfl

end GreenData

end LinearAQFT.Green
