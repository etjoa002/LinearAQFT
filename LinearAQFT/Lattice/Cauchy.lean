/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.Net
import LinearAQFT.Symplectic.Pullback

/-!
# Cauchy data and the Cauchy-data net

Notation as in the notes (Chapter 5). Cauchy data on the slice pair `(t₁, t₁ + 1)` are pairs
`d = (d₀, d₁)` of finitely supported functions on `ℤ`, with the Wronskian
`σ_S(d, d') = ∑ₓ (d₀ d₁' - d₁ d₀')`. The Cauchy map
`Λ_{t₁} [f] = ((E f)(t₁, ·), (E f)(t₁ + 1, ·))` is a symplectic bijection from the phase space
`V = TestFun ⧸ ker E` onto Cauchy data, with the explicit preimage `f' = (-d₁, d₀)` on the two
slices. Hence the net defined through Cauchy data, `O ↦ C*{W_S (Λ_{t₁} [f]) : supp f ⊆ O}`, is
the net of the pulled-back Weyl system `W_S ∘ Λ_{t₁}`, and satisfies the axioms of milestone C.
The change of slice is the leapfrog step `F`, which is symplectic.

## Main definitions

* `CauchyData`, `wronskian`, `sliceData`, `cauchyMap` (E2, Definition 10); `cauchyInv`,
  `cauchyEquiv` (Theorem 13); `cauchyNet` (Definition 14); `leapfrog` (Proposition 16).

## Main statements

* `eq_zero_of_kgOp_eq_zero_of_slices` (Lemma 12).
* `cauchyMap_cauchyInv`, `cauchyMap_injective`, `cauchyMap_surjective`,
  `wronskian_cauchyMap` (Theorem 13).
* `cauchyNet_eq`, `cauchyNet_axioms`, `cauchyNet_ccr_isomorphic`,
  `cauchyNet_ccr_isCovariantUnder` (Theorem 15).
* `cauchyMap_succ`, `wronskian_leapfrog` (Proposition 16).
-/

noncomputable section

namespace LinearAQFT

namespace Lattice

open Symplectic BosonicLean.Weyl Net

variable (m2 : ℝ)

/-! ### The Wronskian -/

/-- Cauchy data on a pair of consecutive slices. -/
abbrev CauchyData := (ℤ →₀ ℝ) × (ℤ →₀ ℝ)

/-- The sum `∑ₓ a(x) b(x)`. -/
def sliceDot (a b : ℤ →₀ ℝ) : ℝ := a.sum fun x c => c * b x

theorem sliceDot_add_left (a a' b : ℤ →₀ ℝ) : sliceDot (a + a') b = sliceDot a b + sliceDot a' b :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem sliceDot_smul_left (c : ℝ) (a b : ℤ →₀ ℝ) : sliceDot (c • a) b = c * sliceDot a b := by
  rw [sliceDot, sliceDot, Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => mul_assoc _ _ _

theorem sliceDot_add_right (a b b' : ℤ →₀ ℝ) :
    sliceDot a (b + b') = sliceDot a b + sliceDot a b' := by
  simp only [sliceDot, Finsupp.coe_add, Pi.add_apply, mul_add]
  exact Finsupp.sum_add

theorem sliceDot_smul_right (c : ℝ) (a b : ℤ →₀ ℝ) : sliceDot a (c • b) = c * sliceDot a b := by
  simp only [sliceDot, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

theorem sliceDot_eq_sum_union (a b : ℤ →₀ ℝ) :
    sliceDot a b = ∑ x ∈ a.support ∪ b.support, a x * b x :=
  Finsupp.sum_of_support_subset a Finset.subset_union_left _ fun _ _ => zero_mul _

theorem sliceDot_comm (a b : ℤ →₀ ℝ) : sliceDot a b = sliceDot b a := by
  rw [sliceDot_eq_sum_union, sliceDot_eq_sum_union, Finset.union_comm]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The bilinear form `(a, b) ↦ ∑ₓ a(x) b(x)`. -/
def sliceDotForm : (ℤ →₀ ℝ) →ₗ[ℝ] (ℤ →₀ ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ sliceDot sliceDot_add_left sliceDot_smul_left sliceDot_add_right
    sliceDot_smul_right

/-- The Wronskian `σ_S(d, d') = ∑ₓ (d₀ d₁' - d₁ d₀')`. -/
def wronskian : LinearMap.BilinForm ℝ CauchyData :=
  (sliceDotForm.compl₂ (LinearMap.snd ℝ _ _)).comp (LinearMap.fst ℝ _ _) -
    (sliceDotForm.compl₂ (LinearMap.fst ℝ _ _)).comp (LinearMap.snd ℝ _ _)

theorem wronskian_apply (d d' : CauchyData) :
    wronskian d d' = sliceDot d.1 d'.2 - sliceDot d.2 d'.1 := rfl

theorem wronskian_isAlt : wronskian.IsAlt := fun d => by
  rw [wronskian_apply, sliceDot_comm, sub_self]

/-! ### Slices of solutions -/

/-- A finite set of positions containing the support of the slice `(E f)(t, ·)`. -/
def sliceFinset (f : TestFun) (t : ℤ) : Finset ℤ :=
  f.support.biUnion fun q => Finset.Icc (q.2 - |t - q.1|) (q.2 + |t - q.1|)

theorem mem_sliceFinset {f : TestFun} {t x : ℤ} (h : causalProp m2 f (t, x) ≠ 0) :
    x ∈ sliceFinset f t := by
  obtain ⟨q, hq, hx⟩ := causalProp_support m2 h
  refine Finset.mem_biUnion.2 ⟨q, hq, Finset.mem_Icc.2 ?_⟩
  have := abs_le.1 (hx.trans (sub_le_self _ zero_le_one))
  constructor <;> linarith [this.1, this.2]

/-- E2, Lemma 11: the slice `x ↦ (E f)(t, x)`, finitely supported by the cone bound. -/
def sliceData (t : ℤ) (f : TestFun) : ℤ →₀ ℝ :=
  Finsupp.onFinset (sliceFinset f t) (fun x => causalProp m2 f (t, x))
    fun _ h => mem_sliceFinset m2 h

@[simp] theorem sliceData_apply (t : ℤ) (f : TestFun) (x : ℤ) :
    sliceData m2 t f x = causalProp m2 f (t, x) := rfl

/-- The slice at time `t` as a linear map. -/
def sliceLinear (t : ℤ) : TestFun →ₗ[ℝ] (ℤ →₀ ℝ) where
  toFun := sliceData m2 t
  map_add' f g := by ext x; simp [causalProp_add]
  map_smul' c f := by ext x; simp [causalProp_smul]

@[simp] theorem sliceLinear_apply (t : ℤ) (f : TestFun) :
    sliceLinear m2 t f = sliceData m2 t f := rfl

/-- E2, Definition 10: the Cauchy map `Λ_{t₁} [f] = ((E f)(t₁, ·), (E f)(t₁ + 1, ·))`. -/
def cauchyMap (t₁ : ℤ) : PhaseVec m2 →ₗ[ℝ] CauchyData :=
  (LinearMap.ker (causalPropLinearMap m2)).liftQ
    ((sliceLinear m2 t₁).prod (sliceLinear m2 (t₁ + 1))) fun f hf => by
      have h : causalProp m2 f = 0 := (mem_ker_causalPropLinearMap m2).1 hf
      rw [LinearMap.mem_ker]
      ext x <;> simp [h]

theorem cauchyMap_mk (t₁ : ℤ) (f : TestFun) :
    cauchyMap m2 t₁ (Submodule.Quotient.mk f) = (sliceData m2 t₁ f, sliceData m2 (t₁ + 1) f) :=
  rfl

/-! ### The explicit preimage -/

/-- E2, Theorem 13: the preimage `f'` with `f'(t₁, ·) = -d₁` and `f'(t₁ + 1, ·) = d₀`. -/
def cauchyInv (t₁ : ℤ) (d : CauchyData) : TestFun :=
  Finsupp.mapDomain (fun x => (t₁ + 1, x)) d.1 - Finsupp.mapDomain (fun x => (t₁, x)) d.2

theorem causalProp_mapDomain (φ : ℤ → Point) (a : ℤ →₀ ℝ) (p : Point) :
    causalProp m2 (Finsupp.mapDomain φ a) p =
      a.sum fun y c => c * commutatorKernel m2 (p - φ y) := by
  rw [causalProp_apply, Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)]

theorem pairing_mapDomain (φ : ℤ → Point) (a : ℤ →₀ ℝ) (u : Point → ℝ) :
    pairing (Finsupp.mapDomain φ a) u = a.sum fun y c => c * u (φ y) := by
  rw [pairing, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

/-- `Δ(1, y) = -[y = 0]`. -/
theorem commutatorKernel_one (y : ℤ) :
    commutatorKernel m2 (1, y) = -(if y = 0 then 1 else 0) := by
  rw [show ((1, y) : Point) = -(-1, -y) by simp, commutatorKernel_neg,
    commutatorKernel_canonical]
  simp

private theorem sum_mul_indicator (a : ℤ →₀ ℝ) (x : ℤ) :
    (a.sum fun y c => c * if x - y = 0 then (1 : ℝ) else 0) = a x := by
  rw [← Finsupp.sum_ite_self_eq' a x]
  refine Finsupp.sum_congr fun y _ => ?_
  by_cases h : y = x
  · simp [h]
  · have : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm h)
    simp [h, this]

private theorem sum_mul_zero (a : ℤ →₀ ℝ) : (a.sum fun _ c => c * (0 : ℝ)) = 0 := by
  simp [Finsupp.sum]

theorem causalProp_cauchyInv_fst (t₁ : ℤ) (d : CauchyData) (x : ℤ) :
    causalProp m2 (cauchyInv t₁ d) (t₁, x) = d.1 x := by
  rw [cauchyInv, causalProp_sub, Pi.sub_apply, causalProp_mapDomain, causalProp_mapDomain]
  have h₁ : ∀ y : ℤ, ((t₁, x) : Point) - (t₁ + 1, y) = (-1, x - y) := fun y =>
    Prod.ext (by change t₁ - (t₁ + 1) = -1; ring) rfl
  have h₀ : ∀ y : ℤ, ((t₁, x) : Point) - (t₁, y) = (0, x - y) := fun y =>
    Prod.ext (sub_self t₁) rfl
  simp only [h₁, h₀, commutatorKernel_canonical, commutatorKernel_equal_time]
  rw [sum_mul_indicator, sum_mul_zero, sub_zero]

theorem causalProp_cauchyInv_snd (t₁ : ℤ) (d : CauchyData) (x : ℤ) :
    causalProp m2 (cauchyInv t₁ d) (t₁ + 1, x) = d.2 x := by
  rw [cauchyInv, causalProp_sub, Pi.sub_apply, causalProp_mapDomain, causalProp_mapDomain]
  have h₀ : ∀ y : ℤ, ((t₁ + 1, x) : Point) - (t₁ + 1, y) = (0, x - y) := fun y =>
    Prod.ext (sub_self _) rfl
  have h₁ : ∀ y : ℤ, ((t₁ + 1, x) : Point) - (t₁, y) = (1, x - y) := fun y =>
    Prod.ext (by change t₁ + 1 - t₁ = 1; ring) rfl
  simp only [h₀, h₁, commutatorKernel_one, commutatorKernel_equal_time, mul_neg]
  rw [sum_mul_zero, Finsupp.sum_neg, sum_mul_indicator]
  ring

/-- E2, Theorem 13(a): `Λ_{t₁} [f'] = d`. -/
theorem cauchyMap_cauchyInv (t₁ : ℤ) (d : CauchyData) :
    cauchyMap m2 t₁ (Submodule.Quotient.mk (cauchyInv t₁ d)) = d := by
  rw [cauchyMap_mk]
  ext x
  · exact causalProp_cauchyInv_fst m2 t₁ d x
  · exact causalProp_cauchyInv_snd m2 t₁ d x

theorem cauchyMap_surjective (t₁ : ℤ) : Function.Surjective (cauchyMap m2 t₁) :=
  fun d => ⟨_, cauchyMap_cauchyInv m2 t₁ d⟩

/-! ### Two slices determine a solution -/

theorem eq_zero_of_kgOp_eq_zero_of_slices_future {u : Point → ℝ} (hu : ∀ p, kgOp m2 u p = 0)
    (t₁ : ℤ) (h₀ : ∀ x, u (t₁, x) = 0) (h₁ : ∀ x, u (t₁ + 1, x) = 0) (n : ℕ) (x : ℤ) :
    u (t₁ + n, x) = 0 := by
  have step : ∀ n : ℕ, (∀ x, u (t₁ + n, x) = 0) ∧ (∀ x, u (t₁ + n + 1, x) = 0) := by
    intro n
    induction n with
    | zero => exact ⟨fun x => by simpa using h₀ x, fun x => by simpa using h₁ x⟩
    | succ n ih =>
      refine ⟨fun x => ?_, fun x => ?_⟩
      · rw [show t₁ + ((n + 1 : ℕ) : ℤ) = t₁ + n + 1 by push_cast; ring]
        exact ih.2 x
      have h := hu (t₁ + n + 1, x)
      simp only [kgOp] at h
      rw [show t₁ + (n : ℤ) + 1 - 1 = t₁ + n by ring, ih.1 x, ih.2 (x + 1), ih.2 (x - 1),
        ih.2 x] at h
      rw [show t₁ + ((n + 1 : ℕ) : ℤ) + 1 = t₁ + n + 1 + 1 by push_cast; ring]
      linarith
  exact (step n).1 x

/-- E2, Lemma 12: a solution vanishing on two consecutive slices vanishes. -/
theorem eq_zero_of_kgOp_eq_zero_of_slices {u : Point → ℝ} (hu : ∀ p, kgOp m2 u p = 0) (t₁ : ℤ)
    (h₀ : ∀ x, u (t₁, x) = 0) (h₁ : ∀ x, u (t₁ + 1, x) = 0) : u = 0 := by
  funext p
  obtain ⟨t, x⟩ := p
  by_cases ht : t₁ ≤ t
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = t₁ + n := ⟨(t - t₁).toNat, by omega⟩
    rw [hn]
    exact eq_zero_of_kgOp_eq_zero_of_slices_future m2 hu t₁ h₀ h₁ n x
  · have hr : ∀ p, kgOp m2 (u ∘ timeReflect) p = 0 := fun p => by rw [kgOp_comp_timeReflect, hu]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, -t = -(t₁ + 1) + n := ⟨(t₁ + 1 - t).toNat, by omega⟩
    have := eq_zero_of_kgOp_eq_zero_of_slices_future m2 hr (-(t₁ + 1))
      (fun x => by simpa [timeReflect] using h₁ x)
      (fun x => by simpa [timeReflect, show -(t₁ + 1) + 1 = -t₁ by ring] using h₀ x) n x
    rw [← hn] at this
    simpa [timeReflect] using this

/-- E2, Theorem 13(b): `Λ_{t₁}` is injective. -/
theorem cauchyMap_injective (t₁ : ℤ) : Function.Injective (cauchyMap m2 t₁) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    rw [cauchyMap_mk, Prod.mk_eq_zero] at hu
    refine (cls_eq_zero_iff m2 f).2 (eq_zero_of_kgOp_eq_zero_of_slices m2
      (kgOp_causalProp m2 f) t₁ (fun x => ?_) (fun x => ?_))
    · simpa using DFunLike.congr_fun hu.1 x
    · simpa using DFunLike.congr_fun hu.2 x

theorem mk_cauchyInv_cauchyMap (t₁ : ℤ) (u : PhaseVec m2) :
    Submodule.Quotient.mk (cauchyInv t₁ (cauchyMap m2 t₁ u)) = u :=
  cauchyMap_injective m2 t₁ (cauchyMap_cauchyInv m2 t₁ _)

theorem pairing_cauchyInv (t₁ : ℤ) (d : CauchyData) (u : Point → ℝ) :
    pairing (cauchyInv t₁ d) u =
      (d.1.sum fun y c => c * u (t₁ + 1, y)) - (d.2.sum fun y c => c * u (t₁, y)) := by
  rw [cauchyInv, pairing_sub_left, pairing_mapDomain, pairing_mapDomain]

/-- E2, Theorem 13(c): `σ_S(Λ_{t₁} u, Λ_{t₁} w) = σ(u, w)`. -/
theorem wronskian_cauchyMap (t₁ : ℤ) (u w : PhaseVec m2) :
    wronskian (cauchyMap m2 t₁ u) (cauchyMap m2 t₁ w) = (phaseSpace m2).sigma u w := by
  conv_rhs => rw [← mk_cauchyInv_cauchyMap m2 t₁ u]
  induction w using Submodule.Quotient.induction_on with
  | H g =>
    change _ = pairing _ (causalProp m2 g)
    rw [pairing_cauchyInv, wronskian_apply, cauchyMap_mk]
    rfl

/-- E2, Theorem 13: `Λ_{t₁}` as a linear bijection. -/
def cauchyEquiv (t₁ : ℤ) : PhaseVec m2 ≃ₗ[ℝ] CauchyData :=
  LinearEquiv.ofBijective (cauchyMap m2 t₁) ⟨cauchyMap_injective m2 t₁, cauchyMap_surjective m2 t₁⟩

@[simp] theorem cauchyEquiv_apply (t₁ : ℤ) (u : PhaseVec m2) :
    cauchyEquiv m2 t₁ u = cauchyMap m2 t₁ u := rfl

/-! ### The Cauchy-data net -/

/-- E2, Definition 14: the Cauchy-data net `O ↦ C*{W_S (Λ_{t₁} [f]) : supp f ⊆ O}`. -/
def cauchyNet (t₁ : ℤ) {A : Type*} [CStarAlgebra A] (S : WeylSystem wronskian A) :
    Net (Set Point) A :=
  Net.generated
    { toFun := fun O => (fun f => S.W (cauchyMap m2 t₁ ((phaseSpace m2).cls f))) ''
        ((phaseSpace m2).loc O : Set TestFun)
      monotone' := fun _ _ h => Set.image_mono ((phaseSpace m2).loc.monotone h) }

/-- E2, Theorem 15(a): the Cauchy-data net is the net of the pulled-back Weyl system. -/
theorem cauchyNet_eq (t₁ : ℤ) {A : Type*} [CStarAlgebra A] (S : WeylSystem wronskian A) :
    cauchyNet m2 t₁ S = weylNet (phaseSpace m2)
      (S.pullback (cauchyMap m2 t₁) (wronskian_cauchyMap m2 t₁) (cauchyMap_surjective m2 t₁)) :=
  rfl

/-- E2, Theorem 15(a): Axioms 1, 3, 4 for the Cauchy-data net of every Weyl system over
Cauchy data. -/
theorem cauchyNet_axioms (t₁ : ℤ) {A : Type*} [CStarAlgebra A] (S : WeylSystem wronskian A) :
    (cauchyNet m2 t₁ S).IsGenerating ∧ IsCausal causalIndex (cauchyNet m2 t₁ S) ∧
      HasTimeSlice causalIndex (cauchyNet m2 t₁ S) := by
  rw [cauchyNet_eq]
  exact ⟨weylNet_isGenerating _ _, weylNet_isCausal _ _, weylNet_hasTimeSlice _ _⟩

/-- The relabelling isomorphism `α_Λ : CCR(V, σ) ≃ CCR(V_S, σ_S)` of `Λ = Λ_{t₁}`. -/
def cauchyRelabel (t₁ : ℤ) : CCR (phaseSpace m2).sigma ≃⋆ₐ[ℂ] CCR wronskian :=
  CCR.relabel (T := cauchyEquiv m2 t₁) (wronskian_cauchyMap m2 t₁)

theorem cauchyNet_ccr_isCovariancePair (t₁ : ℤ) :
    IsCovariancePair (ccrNet (phaseSpace m2))
      (cauchyNet m2 t₁ (CCR.weylSystem wronskian wronskian_isAlt))
      (CausalIndex.Iso.refl causalIndex) (cauchyRelabel m2 t₁) := by
  rw [cauchyNet_eq]
  exact weylNet_isCovariancePair (PhaseSpace.Iso.refl _) _ _ _ fun u =>
    Subtype.ext (conj_relabel_weyl (wronskian_cauchyMap m2 t₁) u)

/-- E2, Theorem 15(b): for the CCR algebra over Cauchy data, the Cauchy-data net is
isomorphic to the CCR net of the lattice field. -/
theorem cauchyNet_ccr_isomorphic (t₁ : ℤ) :
    Isomorphic causalIndex (ccrNet (phaseSpace m2))
      (cauchyNet m2 t₁ (CCR.weylSystem wronskian wronskian_isAlt)) :=
  ⟨_, cauchyNet_ccr_isCovariancePair m2 t₁⟩

/-- The translation automorphisms of `CCR(V_S, σ_S)`: `a ↦ α_Λ α_a α_Λ⁻¹`. -/
def cauchyTranslate (t₁ : ℤ) : Multiplicative Point →* (CCR wronskian ≃⋆ₐ[ℂ] CCR wronskian) where
  toFun a := (cauchyRelabel m2 t₁).symm.trans ((ccrTranslate m2 a).trans (cauchyRelabel m2 t₁))
  map_one' := by
    simp only [map_one]
    ext x
    simp
  map_mul' a b := by
    simp only [map_mul]
    ext x
    simp

/-- E2, Theorem 15(b): the Cauchy-data CCR net is covariant under the lattice translations. -/
theorem cauchyNet_ccr_isCovariantUnder (t₁ : ℤ) :
    IsCovariantUnder (cauchyNet m2 t₁ (CCR.weylSystem wronskian wronskian_isAlt))
      translateHom (cauchyTranslate m2 t₁) := fun a => by
  have h := ((cauchyNet_ccr_isCovariancePair m2 t₁).symm.trans
    ((ccrNet_phaseSpace m2).2.2.2 a)).trans (cauchyNet_ccr_isCovariancePair m2 t₁)
  convert h using 1
  · exact CausalIndex.Iso.ext fun _ => rfl
  · exact StarAlgEquiv.ext fun _ => rfl

/-! ### Change of slice -/

/-- The shift `b ↦ b(· + k)` of a function on `ℤ`. -/
def shiftZ (k : ℤ) : (ℤ →₀ ℝ) →ₗ[ℝ] (ℤ →₀ ℝ) :=
  (Finsupp.domLCongr (Equiv.addRight (-k)) : (ℤ →₀ ℝ) ≃ₗ[ℝ] (ℤ →₀ ℝ))

theorem shiftZ_apply (k : ℤ) (b : ℤ →₀ ℝ) (x : ℤ) : shiftZ k b x = b (x + k) := by
  simp [shiftZ, Finsupp.domLCongr_apply]

/-- E2, Proposition 16: the leapfrog step
`F(d₀, d₁) = (d₁, -d₀ + d₁(· + 1) + d₁(· - 1) - m² d₁)`. -/
def leapfrog : CauchyData →ₗ[ℝ] CauchyData :=
  (LinearMap.snd ℝ _ _).prod
    (-LinearMap.fst ℝ _ _ + (shiftZ 1 + shiftZ (-1) - m2 • LinearMap.id) ∘ₗ LinearMap.snd ℝ _ _)

theorem leapfrog_apply (d : CauchyData) (x : ℤ) :
    (leapfrog m2 d).1 x = d.2 x ∧
      (leapfrog m2 d).2 x = -d.1 x + d.2 (x + 1) + d.2 (x - 1) - m2 * d.2 x := by
  refine ⟨rfl, ?_⟩
  simp [leapfrog, shiftZ_apply, sub_eq_add_neg]
  ring

/-- E2, Proposition 16: `Λ_{t₁ + 1} = F ∘ Λ_{t₁}`. -/
theorem cauchyMap_succ (t₁ : ℤ) :
    cauchyMap m2 (t₁ + 1) = (leapfrog m2).comp (cauchyMap m2 t₁) := by
  refine LinearMap.ext fun u => ?_
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    rw [LinearMap.comp_apply, cauchyMap_mk, cauchyMap_mk]
    ext x
    · rfl
    · rw [(leapfrog_apply m2 _ x).2]
      have h := kgOp_causalProp m2 f (t₁ + 1, x)
      simp only [kgOp] at h
      simp only [sliceData_apply]
      rw [show t₁ + 1 - 1 = t₁ by ring] at h
      linarith

/-- E2, Proposition 16: `F` preserves the Wronskian. -/
theorem wronskian_leapfrog (d d' : CauchyData) :
    wronskian (leapfrog m2 d) (leapfrog m2 d') = wronskian d d' := by
  obtain ⟨u, rfl⟩ := cauchyMap_surjective m2 0 d
  obtain ⟨w, rfl⟩ := cauchyMap_surjective m2 0 d'
  have e : ∀ v, leapfrog m2 (cauchyMap m2 0 v) = cauchyMap m2 (0 + 1) v := fun v => by
    rw [cauchyMap_succ]; rfl
  rw [e, e, wronskian_cauchyMap, wronskian_cauchyMap]

end Lattice

end LinearAQFT

end
