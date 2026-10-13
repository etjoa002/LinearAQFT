/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.Kernel
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Green operators and the causal propagator on the lattice

Test functions are finitely supported functions `ℤ² →₀ ℝ`; solutions are arbitrary functions.
The retarded and advanced Green operators are convolutions with the kernel `K` and its time
reflection, and the causal propagator is `E = G⁻ - G⁺` (advanced minus retarded, programme
Conventions), so that `[φ(f), φ(g)] = i ⟨f, E g⟩`.

## Main definitions

* `pairing`, `kgOpFin` (E1, Section 2); `retarded`, `advanced`, `causalProp`,
  `commutatorKernel` (E1, Definition 6).

## Main statements

* `pairing_kgOpFin` (Lemma 3), `kgOp_retarded`, `kgOp_advanced`, `retarded_support`,
  `advanced_support`, `retarded_kgOpFin`, `advanced_kgOpFin` (Proposition 8),
  `kgOp_causalProp`, `causalProp_kgOpFin`, `commutatorKernel_neg`,
  `pairing_causalProp_antisymm`, `pairing_causalProp_eq_zero_of_orthogonal`,
  `commutatorKernel_eq_zero_of_even` (Proposition 9), `commutatorKernel_canonical`,
  `commutatorKernel_equal_time`, `commutatorKernel_witness`.
-/

noncomputable section

namespace LinearAQFT

namespace Lattice

open Finset

variable (m2 : ℝ)

/-- Test functions: finitely supported real functions on the lattice. -/
abbrev TestFun := Point →₀ ℝ

/-- The pairing `⟨f, u⟩ = ∑ₚ f(p) u(p)`. -/
def pairing (f : TestFun) (u : Point → ℝ) : ℝ := f.sum fun p c => c * u p

theorem pairing_add_left (f g : TestFun) (u : Point → ℝ) :
    pairing (f + g) u = pairing f u + pairing g u :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem pairing_smul_left (c : ℝ) (f : TestFun) (u : Point → ℝ) :
    pairing (c • f) u = c * pairing f u := by
  unfold pairing
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

theorem pairing_neg_left (f : TestFun) (u : Point → ℝ) : pairing (-f) u = -pairing f u := by
  have := pairing_smul_left (-1) f u; simpa using this

theorem pairing_sub_left (f g : TestFun) (u : Point → ℝ) :
    pairing (f - g) u = pairing f u - pairing g u := by
  rw [sub_eq_add_neg, pairing_add_left, pairing_neg_left, ← sub_eq_add_neg]

/-- The shift `(shiftFin e f)(p) = f(p + e)`. -/
def shiftFin (e : Point) (f : TestFun) : TestFun := Finsupp.equivMapDomain (Equiv.subRight e) f

@[simp] theorem shiftFin_apply (e : Point) (f : TestFun) (p : Point) :
    shiftFin e f p = f (p + e) := by
  simp [shiftFin, Finsupp.equivMapDomain_apply]

theorem pairing_shiftFin (e : Point) (f : TestFun) (u : Point → ℝ) :
    pairing (shiftFin e f) u = pairing f (fun q => u (q - e)) := by
  unfold pairing shiftFin
  rw [Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  rfl

/-- `P` on test functions, as a combination of shifts. -/
def kgOpFin (f : TestFun) : TestFun :=
  shiftFin (1, 0) f + shiftFin (-1, 0) f - shiftFin (0, 1) f - shiftFin (0, -1) f + m2 • f

theorem kgOpFin_apply (f : TestFun) (p : Point) : kgOpFin m2 f p = kgOp m2 f p := by
  simp only [kgOpFin, kgOp, Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_smul, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, shiftFin_apply, smul_eq_mul]
  have h1 : p + ((1 : ℤ), (0 : ℤ)) = (p.1 + 1, p.2) := Prod.ext (by simp) (by simp)
  have h2 : p + ((-1 : ℤ), (0 : ℤ)) = (p.1 - 1, p.2) := Prod.ext (by simp; ring) (by simp)
  have h3 : p + ((0 : ℤ), (1 : ℤ)) = (p.1, p.2 + 1) := Prod.ext (by simp) (by simp)
  have h4 : p + ((0 : ℤ), (-1 : ℤ)) = (p.1, p.2 - 1) := Prod.ext (by simp) (by simp; ring)
  rw [h1, h2, h3, h4]

/-- E1, Lemma 3: `⟨P f, u⟩ = ⟨f, P u⟩`. -/
theorem pairing_kgOpFin (f : TestFun) (u : Point → ℝ) :
    pairing (kgOpFin m2 f) u = pairing f (kgOp m2 u) := by
  simp only [kgOpFin, pairing_add_left, pairing_sub_left, pairing_smul_left, pairing_shiftFin]
  unfold pairing
  simp only [← Finsupp.sum_add, ← Finsupp.sum_sub, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  dsimp only
  have h1 : q - ((1 : ℤ), (0 : ℤ)) = (q.1 - 1, q.2) := Prod.ext (by simp) (by simp)
  have h2 : q - ((-1 : ℤ), (0 : ℤ)) = (q.1 + 1, q.2) := Prod.ext (by simp) (by simp)
  have h3 : q - ((0 : ℤ), (1 : ℤ)) = (q.1, q.2 - 1) := Prod.ext (by simp) (by simp)
  have h4 : q - ((0 : ℤ), (-1 : ℤ)) = (q.1, q.2 + 1) := Prod.ext (by simp) (by simp)
  rw [h1, h2, h3, h4]
  simp only [kgOp]
  ring

theorem kgOp_sub (u w : Point → ℝ) : kgOp m2 (u - w) = kgOp m2 u - kgOp m2 w := by
  funext p; simp only [kgOp, Pi.sub_apply]; ring

theorem kgOp_add (u w : Point → ℝ) : kgOp m2 (u + w) = kgOp m2 u + kgOp m2 w := by
  funext p; simp only [kgOp, Pi.add_apply]; ring

theorem kgOp_finsetSum (s : Finset Point) (c : Point → ℝ) (k : Point → Point → ℝ) (p : Point) :
    kgOp m2 (fun r => ∑ q ∈ s, c q * k q r) p = ∑ q ∈ s, c q * kgOp m2 (k q) p := by
  simp only [kgOp, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by ring

theorem kgOp_comp_sub (u : Point → ℝ) (q p : Point) :
    kgOp m2 (fun r => u (r - q)) p = kgOp m2 u (p - q) := by
  simp only [kgOp]
  have h1 : ((p.1 + 1, p.2) : Point) - q = ((p - q).1 + 1, (p - q).2) :=
    Prod.ext (by simp; ring) (by simp)
  have h2 : ((p.1 - 1, p.2) : Point) - q = ((p - q).1 - 1, (p - q).2) :=
    Prod.ext (by simp; ring) (by simp)
  have h3 : ((p.1, p.2 + 1) : Point) - q = ((p - q).1, (p - q).2 + 1) :=
    Prod.ext (by simp) (by simp; ring)
  have h4 : ((p.1, p.2 - 1) : Point) - q = ((p - q).1, (p - q).2 - 1) :=
    Prod.ext (by simp) (by simp; ring)
  rw [h1, h2, h3, h4]

/-- E1, Definition 6: the retarded Green operator `G⁺ f (p) = ∑_q f(q) K(p - q)`. -/
def retarded (f : TestFun) (p : Point) : ℝ := f.sum fun q c => c * kernel m2 (p - q)

/-- E1, Definition 6: the advanced Green operator `G⁻ f (p) = ∑_q f(q) K(R(p - q))`. -/
def advanced (f : TestFun) (p : Point) : ℝ := f.sum fun q c => c * kernel m2 (timeReflect (p - q))

/-- E1, Definition 6: the causal propagator `E f = G⁻ f - G⁺ f` (advanced minus retarded). -/
def causalProp (f : TestFun) : Point → ℝ := advanced m2 f - retarded m2 f

/-- The kernel of `E`: `E(s, y) = K(-s, y) - K(s, y)`. -/
def commutatorKernel (r : Point) : ℝ := kernel m2 (timeReflect r) - kernel m2 r

theorem causalProp_apply (f : TestFun) (p : Point) :
    causalProp m2 f p = f.sum fun q c => c * commutatorKernel m2 (p - q) := by
  simp only [causalProp, Pi.sub_apply, advanced, retarded, commutatorKernel, mul_sub]
  rw [Finsupp.sum_sub]

theorem kgOp_kernel_timeReflect (p : Point) :
    kgOp m2 (fun r => kernel m2 (timeReflect r)) p = if p = (0, 0) then 1 else 0 := by
  have := kgOp_comp_timeReflect m2 (kernel m2) p
  rw [show (kernel m2 ∘ timeReflect) = fun r => kernel m2 (timeReflect r) from rfl] at this
  rw [this, kgOp_kernel]
  congr 1
  apply propext
  constructor <;> intro h
  · have h' := congrArg timeReflect h
    simpa [timeReflect] using h'
  · subst h; rfl

/-- E1, Proposition 8(a): `P G⁺ f = f`. -/
theorem kgOp_retarded (f : TestFun) (p : Point) : kgOp m2 (retarded m2 f) p = f p := by
  have : retarded m2 f = fun r => ∑ q ∈ f.support, f q * kernel m2 (r - q) := rfl
  rw [this, kgOp_finsetSum]
  simp only [kgOp_comp_sub, kgOp_kernel, Prod.mk_zero_zero, sub_eq_zero, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

/-- E1, Proposition 8(a): `P G⁻ f = f`. -/
theorem kgOp_advanced (f : TestFun) (p : Point) : kgOp m2 (advanced m2 f) p = f p := by
  have : advanced m2 f = fun r => ∑ q ∈ f.support, f q * kernel m2 (timeReflect (r - q)) := rfl
  rw [this, kgOp_finsetSum]
  simp only [kgOp_comp_sub m2 (fun r => kernel m2 (timeReflect r)), kgOp_kernel_timeReflect,
    Prod.mk_zero_zero, sub_eq_zero, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

/-- E1, Proposition 8(b): `G⁺ f (p) ≠ 0` gives `q ∈ supp f` with `|x_p - x_q| ≤ t_p - t_q - 1`. -/
theorem retarded_support {f : TestFun} {p : Point} (h : retarded m2 f p ≠ 0) :
    ∃ q ∈ f.support, |p.2 - q.2| ≤ p.1 - q.1 - 1 := by
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨q, hq, ?_⟩
  have := kernel_support m2 (right_ne_zero_of_mul hne)
  simpa using this

/-- E1, Proposition 8(b): `G⁻ f (p) ≠ 0` gives `q ∈ supp f` with `|x_p - x_q| ≤ t_q - t_p - 1`. -/
theorem advanced_support {f : TestFun} {p : Point} (h : advanced m2 f p ≠ 0) :
    ∃ q ∈ f.support, |p.2 - q.2| ≤ q.1 - p.1 - 1 := by
  obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨q, hq, ?_⟩
  have := kernel_support m2 (right_ne_zero_of_mul hne)
  simp only [timeReflect, Prod.fst_sub, Prod.snd_sub] at this
  linarith

theorem kgOpFin_support {f : TestFun} {p : Point} (h : kgOpFin m2 f p ≠ 0) :
    ∃ q ∈ f.support, q.1 - 1 ≤ p.1 ∧ p.1 ≤ q.1 + 1 := by
  rw [kgOpFin_apply] at h
  simp only [kgOp] at h
  by_contra hc
  push Not at hc
  have z : ∀ r : Point, (r.1 = p.1 - 1 ∨ r.1 = p.1 ∨ r.1 = p.1 + 1) → f r = 0 := by
    intro r hr
    by_contra hne
    have := hc r (Finsupp.mem_support_iff.2 hne)
    omega
  apply h
  rw [z (p.1 + 1, p.2) (by simp), z (p.1 - 1, p.2) (by simp), z (p.1, p.2 + 1) (by simp),
    z (p.1, p.2 - 1) (by simp), z p (by simp)]
  ring

private theorem exists_lower_bound (f : TestFun) : ∃ T : ℤ, ∀ q ∈ f.support, T ≤ q.1 := by
  refine ⟨-(∑ q ∈ f.support, |q.1|), fun q hq => ?_⟩
  have h1 : |q.1| ≤ ∑ r ∈ f.support, |r.1| :=
    Finset.single_le_sum (f := fun r : Point => |r.1|) (fun r _ => abs_nonneg _) hq
  have h2 := neg_abs_le q.1
  linarith

theorem exists_upper_bound (f : TestFun) : ∃ T : ℤ, ∀ q ∈ f.support, q.1 ≤ T := by
  refine ⟨∑ q ∈ f.support, |q.1|, fun q hq => ?_⟩
  have h1 : |q.1| ≤ ∑ r ∈ f.support, |r.1| :=
    Finset.single_le_sum (f := fun r : Point => |r.1|) (fun r _ => abs_nonneg _) hq
  have h2 := le_abs_self q.1
  linarith

/-- E1, Proposition 8(c): `G⁺ P f = f`. -/
theorem retarded_kgOpFin (f : TestFun) : retarded m2 (kgOpFin m2 f) = f := by
  obtain ⟨T, hT⟩ := exists_lower_bound f
  have h := eq_zero_of_kgOp_eq_zero_of_past m2 (u := retarded m2 (kgOpFin m2 f) - f)
    (fun p => by
      rw [kgOp_sub, Pi.sub_apply, kgOp_retarded, kgOpFin_apply, sub_self])
    T (fun p hp => by
      simp only [Pi.sub_apply]
      have h1 : retarded m2 (kgOpFin m2 f) p = 0 := by
        by_contra hne
        obtain ⟨q, hq, hpq⟩ := retarded_support m2 hne
        obtain ⟨r, hr, hqr⟩ := kgOpFin_support m2 (Finsupp.mem_support_iff.1 hq)
        have := hT r hr
        have := abs_nonneg (p.2 - q.2)
        omega
      have h2 : f p = 0 := by
        by_contra hne
        have := hT p (Finsupp.mem_support_iff.2 hne)
        omega
      rw [h1, h2, sub_zero])
  exact sub_eq_zero.1 h

/-- E1, Proposition 8(c): `G⁻ P f = f`. -/
theorem advanced_kgOpFin (f : TestFun) : advanced m2 (kgOpFin m2 f) = f := by
  obtain ⟨T, hT⟩ := exists_upper_bound f
  have h := eq_zero_of_kgOp_eq_zero_of_future m2 (u := advanced m2 (kgOpFin m2 f) - f)
    (fun p => by
      rw [kgOp_sub, Pi.sub_apply, kgOp_advanced, kgOpFin_apply, sub_self])
    T (fun p hp => by
      simp only [Pi.sub_apply]
      have h1 : advanced m2 (kgOpFin m2 f) p = 0 := by
        by_contra hne
        obtain ⟨q, hq, hpq⟩ := advanced_support m2 hne
        obtain ⟨r, hr, hqr⟩ := kgOpFin_support m2 (Finsupp.mem_support_iff.1 hq)
        have := hT r hr
        have := abs_nonneg (p.2 - q.2)
        omega
      have h2 : f p = 0 := by
        by_contra hne
        have := hT p (Finsupp.mem_support_iff.2 hne)
        omega
      rw [h1, h2, sub_zero])
  exact sub_eq_zero.1 h

/-- E1, Proposition 9(a): `P E f = 0`. -/
theorem kgOp_causalProp (f : TestFun) (p : Point) : kgOp m2 (causalProp m2 f) p = 0 := by
  rw [causalProp, kgOp_sub, Pi.sub_apply, kgOp_advanced, kgOp_retarded, sub_self]

/-- E1, Proposition 9(a): `E P f = 0`. -/
theorem causalProp_kgOpFin (f : TestFun) : causalProp m2 (kgOpFin m2 f) = 0 := by
  rw [causalProp, advanced_kgOpFin, retarded_kgOpFin, sub_self]

/-- E1, Proposition 9(b): `E(-s, -y) = -E(s, y)`. -/
theorem commutatorKernel_neg (r : Point) : commutatorKernel m2 (-r) = -commutatorKernel m2 r := by
  obtain ⟨s, y⟩ := r
  simp only [commutatorKernel, timeReflect, Prod.neg_mk, neg_neg]
  rw [kernel_neg m2 s y, show ((-s, -y) : Point) = (-s, -y) from rfl, kernel_neg m2 (-s) y]
  ring

/-- E1, Proposition 9(c): `⟨f, E g⟩ = -⟨g, E f⟩`. -/
theorem pairing_causalProp_antisymm (f g : TestFun) :
    pairing f (causalProp m2 g) = -pairing g (causalProp m2 f) := by
  simp only [pairing, causalProp_apply, Finsupp.sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  rw [show p - q = -(q - p) from (neg_sub q p).symm, commutatorKernel_neg]
  ring

/-- E1, Proposition 9(d): if no point of `supp f` is comparable with a point of `supp g`,
then `⟨f, E g⟩ = 0`. -/
theorem pairing_causalProp_eq_zero_of_orthogonal {f g : TestFun}
    (h : ∀ p ∈ f.support, ∀ q ∈ g.support, ¬ Comparable p q) :
    pairing f (causalProp m2 g) = 0 := by
  simp only [pairing, causalProp_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hE : commutatorKernel m2 (p - q) = 0 := by
    have hc := h p hp q hq
    have k1 : kernel m2 (p - q) = 0 := by
      by_contra hne
      have := kernel_support m2 hne
      exact hc (Or.inr (by simp only [causalLE, Prod.fst_sub, Prod.snd_sub] at this ⊢; linarith))
    have k2 : kernel m2 (timeReflect (p - q)) = 0 := by
      by_contra hne
      have := kernel_support m2 hne
      simp only [timeReflect, Prod.fst_sub, Prod.snd_sub] at this
      refine hc (Or.inl ?_)
      simp only [causalLE]
      rw [abs_sub_comm]
      linarith
    rw [commutatorKernel, k1, k2, sub_zero]
  rw [hE]; ring

/-- E1, Proposition 9(e): for `m² = 0`, `E(r) = 0` when `r₁ + r₂` is even. -/
theorem commutatorKernel_eq_zero_of_even {r : Point} (h : Even (r.1 + r.2)) :
    commutatorKernel 0 r = 0 := by
  have k1 : kernel 0 r = 0 := by
    by_contra hne
    exact (Int.not_odd_iff_even.2 h) (kernel_parity hne)
  have k2 : kernel 0 (timeReflect r) = 0 := by
    by_contra hne
    have := kernel_parity hne
    simp only [timeReflect] at this
    apply Int.not_odd_iff_even.2 h
    have e : r.1 + r.2 = (-r.1 + r.2) + 2 * r.1 := by ring
    rw [e]
    exact this.add_even (even_two_mul _)
  rw [commutatorKernel, k1, k2, sub_zero]

/-- Canonical sign: `⟨δ_(0,x), E δ_(1,y)⟩ = E(-1, x - y) = [x = y]`. -/
theorem commutatorKernel_canonical (y : ℤ) :
    commutatorKernel m2 (-1, y) = if y = 0 then 1 else 0 := by
  simp only [commutatorKernel, timeReflect, neg_neg]
  rw [kernel_one, kernel_of_nonpos m2 (show ((-1 : ℤ), y).1 ≤ 0 by simp), sub_zero]

/-- Equal times: `E(0, y) = 0`. -/
theorem commutatorKernel_equal_time (y : ℤ) : commutatorKernel m2 (0, y) = 0 := by
  simp only [commutatorKernel, timeReflect, neg_zero, sub_self]

/-- The opposite-parity witness at `m² = 0`: `E(3, 0) = -1`. -/
theorem commutatorKernel_witness : commutatorKernel 0 (3, 0) = -1 := by
  simp only [commutatorKernel, timeReflect]
  rw [kernel_of_nonpos 0 (show ((-3 : ℤ), (0 : ℤ)).1 ≤ 0 by simp)]
  have : kernel 0 ((3 : ℤ), 0) = kernelNat 0 3 0 := kernel_natCast 0 3 0
  rw [this]
  norm_num [kernelNat_succ_succ, kernelNat_one, kernelNat_zero]

end Lattice

end LinearAQFT

end
