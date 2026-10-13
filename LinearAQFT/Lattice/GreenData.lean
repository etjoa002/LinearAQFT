/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Green.PhaseSpace
import LinearAQFT.Lattice.Linear

/-!
# The lattice field as Green data

Stage F, item 5 (moved from `Lattice/Green.lean` on 30 Sep 2026, so that the phase-space data of
E2 can be derived from it). The lattice Klein–Gordon field of E1 is Green data: points `ℤ²` with
`causalLE`, functions `ℤ² → ℝ`, finitely supported test functions, the operator `kgOp`, the
pairing, the retarded and advanced operators, and the cutoffs `χ_{t₁}` (the step at `t₁`) with the
pairs of slices as slabs. The derived causal index is E1's, `E` is the causal propagator, and the
localized test functions are those of E2.

## Main results

* `Lattice.greenData` (F, Proposition 12).
* `Lattice.greenData_causalIndex`, `Lattice.greenData_E`, `Lattice.greenData_loc` (Theorem 13).
-/

noncomputable section

namespace LinearAQFT.Lattice

open Green Symplectic

variable (m2 : ℝ)

/-! ### Linear maps -/

theorem retarded_add (f g : TestFun) :
    retarded m2 (f + g) = retarded m2 f + retarded m2 g := by
  funext p
  simp only [retarded, Pi.add_apply]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem retarded_smul (c : ℝ) (f : TestFun) : retarded m2 (c • f) = c • retarded m2 f := by
  funext p
  simp only [retarded, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => mul_assoc _ _ _

theorem advanced_add (f g : TestFun) :
    advanced m2 (f + g) = advanced m2 f + advanced m2 g := by
  funext p
  simp only [advanced, Pi.add_apply]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem advanced_smul (c : ℝ) (f : TestFun) : advanced m2 (c • f) = c • advanced m2 f := by
  funext p
  simp only [advanced, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => mul_assoc _ _ _

/-- The retarded operator `G⁺` as a linear map. -/
def retardedLinearMap : TestFun →ₗ[ℝ] (Point → ℝ) where
  toFun := retarded m2
  map_add' := retarded_add m2
  map_smul' := retarded_smul m2

/-- The advanced operator `G⁻` as a linear map. -/
def advancedLinearMap : TestFun →ₗ[ℝ] (Point → ℝ) where
  toFun := advanced m2
  map_add' := advanced_add m2
  map_smul' := advanced_smul m2

/-- The Klein–Gordon operator `P` as a linear map on functions. -/
def kgOpLinearMap : (Point → ℝ) →ₗ[ℝ] (Point → ℝ) where
  toFun := kgOp m2
  map_add' := kgOp_add m2
  map_smul' c u := by
    funext p
    simp only [kgOp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The Klein–Gordon operator on test functions as a linear map. -/
def kgOpFinLinearMap : TestFun →ₗ[ℝ] TestFun where
  toFun := kgOpFin m2
  map_add' f g := by
    ext p
    simp only [kgOpFin_apply, Finsupp.coe_add, Finsupp.add_apply]
    rw [kgOp_add]
    rfl
  map_smul' c f := by
    ext p
    simp only [kgOpFin_apply, Finsupp.coe_smul, Finsupp.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp only [kgOp, Pi.smul_apply, smul_eq_mul]
    ring

/-- The pairing `⟨f, u⟩ = Σ_p f(p) u(p)` as a bilinear map. -/
def pairingBilin : TestFun →ₗ[ℝ] (Point → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ pairing pairing_add_left pairing_smul_left pairing_add_right
    (fun c f u => by rw [pairing_smul_right, smul_eq_mul])

/-- The cutoff `χ_{t₁}`: a function at times `≥ t₁ + 1`, zero before. -/
def chiLinearMap (t₁ : ℤ) : (Point → ℝ) →ₗ[ℝ] (Point → ℝ) where
  toFun u p := if t₁ + 1 ≤ p.1 then u p else 0
  map_add' u w := by
    funext p
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-! ### Formal adjointness -/

/-- F, Proposition 12: `⟨f, G⁺ g⟩ = ⟨g, G⁻ f⟩`, from the evenness of the kernel in `x`. -/
theorem pairing_retarded (f g : TestFun) :
    pairing f (retarded m2 g) = pairing g (advanced m2 f) := by
  simp only [pairing, retarded, advanced, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  have : kernel m2 (timeReflect (q - p)) = kernel m2 (p - q) := by
    have h := kernel_neg m2 (p - q).1 (p - q).2
    rw [← h]
    congr 1
    ext <;> simp [timeReflect]
  rw [this]
  ring

/-! ### The cutoff test function -/

/-- `(1 - χ_{t₁}) G⁺ f + χ_{t₁} G⁻ f`. -/
def cutoffFun (t₁ : ℤ) (f : TestFun) (p : Point) : ℝ :=
  if t₁ + 1 ≤ p.1 then advanced m2 f p else retarded m2 f p

/-- A finite set containing the support of `cutoffFun`. -/
def cutoffFinset (t₁ : ℤ) (f : TestFun) : Finset Point :=
  f.support.biUnion fun q =>
    (Finset.Icc (q.1 + 1) t₁ ×ˢ Finset.Icc (q.2 - (t₁ - q.1)) (q.2 + (t₁ - q.1))) ∪
      (Finset.Icc (t₁ + 1) (q.1 - 1) ×ˢ Finset.Icc (q.2 - (q.1 - t₁)) (q.2 + (q.1 - t₁)))

theorem mem_cutoffFinset {t₁ : ℤ} {f : TestFun} {p : Point} (h : cutoffFun m2 t₁ f p ≠ 0) :
    p ∈ cutoffFinset t₁ f := by
  simp only [cutoffFinset, Finset.mem_biUnion, Finset.mem_union, Finset.mem_product,
    Finset.mem_Icc]
  unfold cutoffFun at h
  split_ifs at h with ht
  · obtain ⟨q, hq, hpq⟩ := advanced_support m2 h
    refine ⟨q, hq, Or.inr ⟨⟨ht, by linarith [abs_nonneg (p.2 - q.2)]⟩, ?_⟩⟩
    rw [abs_le] at hpq
    constructor <;> linarith
  · obtain ⟨q, hq, hpq⟩ := retarded_support m2 h
    refine ⟨q, hq, Or.inl ⟨⟨by linarith [abs_nonneg (p.2 - q.2)], by omega⟩, ?_⟩⟩
    rw [abs_le] at hpq
    constructor <;> omega

/-- F, Proposition 12 (c2): the cutoff test function. -/
def cutoffTest (t₁ : ℤ) (f : TestFun) : TestFun :=
  Finsupp.onFinset (cutoffFinset t₁ f) (cutoffFun m2 t₁ f) fun _ h => mem_cutoffFinset m2 h

/-! ### The lattice Green data -/

theorem support_chi_causalProp (t₁ : ℤ) (f : TestFun) :
    Function.support (kgOp m2 (chiLinearMap t₁ (causalProp m2 f))) ⊆
      slices t₁ ∩ {q | ∃ p ∈ Function.support f, causalLE p q ∨ causalLE q p} := by
  intro q hq
  have hchi : kgOp m2 (chiLinearMap t₁ (causalProp m2 f)) q = -timeSliceFun m2 f t₁ q := by
    have hsplit : chiLinearMap t₁ (causalProp m2 f) =
        causalProp m2 f - pastPart t₁ (causalProp m2 f) := by
      funext p
      simp only [chiLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, pastPart]
      split_ifs <;> first | (exfalso; omega) | simp
    rw [hsplit, kgOp_sub, Pi.sub_apply, kgOp_causalProp, timeSliceFun, zero_sub]
  rw [Function.mem_support, hchi, neg_ne_zero] at hq
  obtain ⟨hs, p, hp, hpq⟩ := timeSliceFun_ne_zero m2 hq
  refine ⟨hs, p, ?_, hpq.symm⟩
  rwa [Finsupp.fun_support_eq]

/-- F, Proposition 12: the lattice field as Green data. -/
def greenData : GreenData Point TestFun (Point → ℝ) where
  causalLE := causalLE
  supp := Function.support
  supp_zero := Function.support_zero
  supp_add := Function.support_add
  supp_smul c u p hp := by
    rw [Function.mem_support] at hp ⊢
    intro h
    exact hp (by simp [h])
  incl := Finsupp.lcoeFun
  P := kgOpLinearMap m2
  Ptest := kgOpFinLinearMap m2
  incl_Ptest f := funext fun p => kgOpFin_apply m2 f p
  pairing := pairingBilin
  pairing_eq_zero f u h := by
    change pairing f u = 0
    refine Finset.sum_eq_zero fun p hp => ?_
    have hu : u p = 0 := by
      by_contra hne
      exact Set.disjoint_left.1 h (by simpa using hp) (Function.mem_support.2 hne)
    simp [hu]
  pairing_nondegenerate u h := by
    funext p
    have := h (Finsupp.single p 1)
    change pairing (Finsupp.single p 1) u = 0 at this
    rw [pairing_single, one_mul] at this
    exact this
  gret := retardedLinearMap m2
  gadv := advancedLinearMap m2
  P_gret f := funext fun p => kgOp_retarded m2 f p
  P_gadv f := funext fun p => kgOp_advanced m2 f p
  gret_Ptest f := retarded_kgOpFin m2 f
  gadv_Ptest f := advanced_kgOpFin m2 f
  supp_gret f q hq := by
    obtain ⟨p, hp, hpq⟩ := retarded_support m2 (Function.mem_support.1 hq)
    refine ⟨p, by simpa using hp, ?_⟩
    unfold causalLE
    linarith
  supp_gadv f q hq := by
    obtain ⟨p, hp, hpq⟩ := advanced_support m2 (Function.mem_support.1 hq)
    refine ⟨p, by simpa using hp, ?_⟩
    unfold causalLE
    rw [abs_sub_comm]
    linarith
  adjoint f g := pairing_retarded m2 f g
  Cutoff := ℤ
  chi := chiLinearMap
  slab := slices
  supp_P_chi_E t₁ f := support_chi_causalProp m2 t₁ f
  exists_test t₁ f := by
    refine ⟨cutoffTest m2 t₁ f, ?_⟩
    funext p
    change cutoffFun m2 t₁ f p = _
    simp only [cutoffFun, chiLinearMap, retardedLinearMap, advancedLinearMap, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.add_apply, Pi.sub_apply]
    split_ifs <;> simp

/-! ### Comparison with E1 and E2 -/

theorem causalIndex_ext {C C' : CausalIndex (Set Point)} (hO : C.Orthogonal = C'.Orthogonal)
    (hD : C.Dependent = C'.Dependent) : C = C' := by
  obtain ⟨⟨o, _, _⟩, d, _, _⟩ := C
  obtain ⟨⟨o', _, _⟩, d', _, _⟩ := C'
  change o = o' at hO
  change d = d' at hD
  subst hO
  subst hD
  rfl

theorem greenData_shadow (O : Set Point) : (greenData m2).shadow O = causalShadow O := by
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    exact ⟨p, hp, comparable_comm.1 hpq⟩
  · rintro ⟨p, hp, hpq⟩
    exact ⟨p, hp, comparable_comm.1 hpq⟩

/-- F, Theorem 13: the derived causal index is the lattice causal index of E1. -/
theorem greenData_causalIndex : (greenData m2).causalIndex = causalIndex := by
  refine causalIndex_ext rfl ?_
  funext O O'
  apply propext
  change (∀ f : TestFun, Function.support f ⊆ O →
      ∃ t₁, slices t₁ ∩ (greenData m2).shadow (Function.support f) ⊆ O') ↔
    (∀ Y : Set Point, Y.Finite → Y ⊆ O → ∃ t₁, causalShadow Y ∩ slices t₁ ⊆ O')
  simp only [greenData_shadow, Set.inter_comm (slices _)]
  constructor
  · intro h Y hY hYO
    let f : TestFun := Finsupp.onFinset hY.toFinset (Y.indicator 1) fun p hp => by
      rw [Set.Finite.mem_toFinset]
      by_contra hpY
      exact hp (Set.indicator_of_notMem hpY _)
    have hf : Function.support f = Y := by
      ext p
      simp only [f, Function.mem_support, Finsupp.onFinset_apply]
      by_cases hp : p ∈ Y <;> simp [hp]
    obtain ⟨t₁, ht⟩ := h f (hf ▸ hYO)
    exact ⟨t₁, hf ▸ ht⟩
  · intro h f hf
    exact h _ (by rw [Finsupp.fun_support_eq]; exact f.support.finite_toSet) hf

/-- F, Theorem 13: `E` is the commutator of E1. -/
theorem greenData_E : (greenData m2).E = causalPropLinearMap m2 := rfl

theorem greenData_loc (O : Set Point) : (greenData m2).loc O = loc O := by
  ext f
  rw [GreenData.mem_loc, mem_loc]
  change Function.support f ⊆ O ↔ _
  rw [Finsupp.fun_support_eq]

end LinearAQFT.Lattice
