/-
Copyright (c) 2026 LinearAQFT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LinearAQFT contributors
-/
import LinearAQFT.Lattice.Causal
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The discrete Klein–Gordon operator and its retarded kernel

On functions `u : ℤ² → ℝ` the operator is
`(P u)(t, x) = u(t+1, x) + u(t-1, x) - u(t, x+1) - u(t, x-1) + m² u(t, x)`, the discrete form of
`-□ + m²` in mostly-plus signature. The retarded kernel `K` is defined by recursion in time.

## Main definitions

* `LinearAQFT.Lattice.kgOp m2` (E1, Section 2).
* `LinearAQFT.Lattice.kernel m2` (E1, Definition 4).

## Main statements

* `kgOp_kernel` (Lemma 5(a)), `kernel_support` (5(b)), `kernel_neg` (5(c)),
  `kernel_parity` (5(d)); `eq_zero_of_kgOp_eq_zero_of_past`, `..._of_future` (Lemma 7).
-/

namespace LinearAQFT

namespace Lattice

variable (m2 : ℝ)

/-- E1, Section 2: `(P u)(t, x) = u(t+1, x) + u(t-1, x) - u(t, x+1) - u(t, x-1) + m² u(t, x)`. -/
def kgOp (u : Point → ℝ) : Point → ℝ := fun p =>
  u (p.1 + 1, p.2) + u (p.1 - 1, p.2) - u (p.1, p.2 + 1) - u (p.1, p.2 - 1) + m2 * u p

/-- The pair `(K(n, ·), K(n+1, ·))` of consecutive time slices of the kernel. -/
def kernelAux : ℕ → (ℤ → ℝ) × (ℤ → ℝ)
  | 0 => (fun _ => 0, fun y => if y = 0 then 1 else 0)
  | n + 1 => ((kernelAux n).2, fun y =>
      -(kernelAux n).1 y + (kernelAux n).2 (y + 1) + (kernelAux n).2 (y - 1)
        - m2 * (kernelAux n).2 y)

/-- The kernel on the time slice `n ∈ ℕ`. -/
def kernelNat (n : ℕ) (y : ℤ) : ℝ := (kernelAux m2 n).1 y

theorem kernelNat_zero (y : ℤ) : kernelNat m2 0 y = 0 := rfl

theorem kernelNat_one (y : ℤ) : kernelNat m2 1 y = if y = 0 then 1 else 0 := rfl

theorem kernelNat_succ_succ (n : ℕ) (y : ℤ) :
    kernelNat m2 (n + 2) y = -kernelNat m2 n y + kernelNat m2 (n + 1) (y + 1)
      + kernelNat m2 (n + 1) (y - 1) - m2 * kernelNat m2 (n + 1) y := rfl

/-- E1, Definition 4: the retarded kernel, `K(s, y) = 0` for `s ≤ 0`, `K(1, y) = [y = 0]`, and
`K(s+1, y) = -K(s-1, y) + K(s, y+1) + K(s, y-1) - m² K(s, y)` for `s ≥ 1`. -/
def kernel (p : Point) : ℝ := if p.1 < 0 then 0 else kernelNat m2 p.1.toNat p.2

theorem kernel_natCast (n : ℕ) (y : ℤ) : kernel m2 ((n : ℤ), y) = kernelNat m2 n y := by
  simp [kernel]

theorem kernel_of_nonpos {p : Point} (hp : p.1 ≤ 0) : kernel m2 p = 0 := by
  unfold kernel
  split_ifs with h
  · rfl
  · have : p.1.toNat = 0 := by omega
    rw [this]; rfl

theorem kernel_one (y : ℤ) : kernel m2 (1, y) = if y = 0 then 1 else 0 := by
  have := kernel_natCast m2 1 y
  rw [Nat.cast_one] at this
  rw [this]; rfl

theorem kernel_recursion {s : ℤ} (hs : 1 ≤ s) (y : ℤ) :
    kernel m2 (s + 1, y) = -kernel m2 (s - 1, y) + kernel m2 (s, y + 1) + kernel m2 (s, y - 1)
      - m2 * kernel m2 (s, y) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = (n : ℤ) + 1 := ⟨(s - 1).toNat, by omega⟩
  have h1 : ((n : ℤ) + 1 + 1) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
  have h2 : ((n : ℤ) + 1 - 1) = ((n : ℕ) : ℤ) := by ring
  have h3 : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h1, h2, h3, kernel_natCast, kernel_natCast, kernel_natCast, kernel_natCast,
    kernel_natCast, kernelNat_succ_succ]

/-- E1, Lemma 5(a): `P K = δ`. -/
theorem kgOp_kernel (p : Point) : kgOp m2 (kernel m2) p = if p = (0, 0) then 1 else 0 := by
  obtain ⟨s, y⟩ := p
  simp only [kgOp]
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · rw [kernel_of_nonpos m2 (show (s + 1, y).1 ≤ 0 by simp; omega),
      kernel_of_nonpos m2 (show (s - 1, y).1 ≤ 0 by simp; omega),
      kernel_of_nonpos m2 (show (s, y + 1).1 ≤ 0 by simp; omega),
      kernel_of_nonpos m2 (show (s, y - 1).1 ≤ 0 by simp; omega),
      kernel_of_nonpos m2 (show (s, y).1 ≤ 0 by simp; omega)]
    have : (s, y) ≠ (0, 0) := by intro h; simp at h; omega
    simp [this]
  · rw [show ((0 : ℤ) + 1) = 1 by rfl, kernel_one,
      kernel_of_nonpos m2 (show ((0 : ℤ) - 1, y).1 ≤ 0 by simp),
      kernel_of_nonpos m2 (show ((0 : ℤ), y + 1).1 ≤ 0 by simp),
      kernel_of_nonpos m2 (show ((0 : ℤ), y - 1).1 ≤ 0 by simp),
      kernel_of_nonpos m2 (show ((0 : ℤ), y).1 ≤ 0 by simp)]
    by_cases hy : y = 0 <;> simp [hy]
  · rw [kernel_recursion m2 hs]
    have : (s, y) ≠ (0, 0) := by intro h; simp at h; omega
    simp only [this, ↓reduceIte]
    ring

/-- E1, Lemma 5(b), on natural time slices. -/
theorem kernelNat_support (n : ℕ) : ∀ y, kernelNat m2 n y ≠ 0 → |y| ≤ (n : ℤ) - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => intro y h; exact absurd rfl h
    | 1, _ =>
      intro y h
      rw [kernelNat_one] at h
      split_ifs at h with hy
      · simp [hy]
      · exact absurd rfl h
    | n + 2, ih =>
      intro y h
      rw [kernelNat_succ_succ] at h
      by_contra hc
      have hc := not_le.mp hc
      push_cast at hc
      rw [lt_abs] at hc
      have e1 : kernelNat m2 n y = 0 := by
        by_contra h'; have := ih n (by omega) y h'; rw [abs_le] at this; omega
      have e2 : kernelNat m2 (n + 1) (y + 1) = 0 := by
        by_contra h'; have := ih (n + 1) (by omega) _ h'
        push_cast at this; rw [abs_le] at this; omega
      have e3 : kernelNat m2 (n + 1) (y - 1) = 0 := by
        by_contra h'; have := ih (n + 1) (by omega) _ h'
        push_cast at this; rw [abs_le] at this; omega
      have e4 : kernelNat m2 (n + 1) y = 0 := by
        by_contra h'; have := ih (n + 1) (by omega) _ h'
        push_cast at this; rw [abs_le] at this; omega
      exact h (by rw [e1, e2, e3, e4]; ring)

/-- E1, Lemma 5(b): `K(s, y) ≠ 0` implies `|y| ≤ s - 1`. -/
theorem kernel_support {p : Point} (h : kernel m2 p ≠ 0) : |p.2| ≤ p.1 - 1 := by
  obtain ⟨s, y⟩ := p
  by_cases hs : s ≤ 0
  · exact absurd (kernel_of_nonpos m2 (show (s, y).1 ≤ 0 from hs)) h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by omega⟩
    rw [kernel_natCast] at h
    exact kernelNat_support m2 n y h

/-- E1, Lemma 5(c), on natural time slices. -/
theorem kernelNat_neg (n : ℕ) : ∀ y, kernelNat m2 n (-y) = kernelNat m2 n y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => intro y; rfl
    | 1, _ => intro y; simp [kernelNat_one]
    | n + 2, ih =>
      intro y
      rw [kernelNat_succ_succ, kernelNat_succ_succ, ih n (by omega), ih (n + 1) (by omega),
        show -y + 1 = -(y - 1) by ring, show -y - 1 = -(y + 1) by ring,
        ih (n + 1) (by omega) (y - 1), ih (n + 1) (by omega) (y + 1)]
      ring

/-- E1, Lemma 5(c): `K(s, -y) = K(s, y)`. -/
theorem kernel_neg (s y : ℤ) : kernel m2 (s, -y) = kernel m2 (s, y) := by
  by_cases hs : s ≤ 0
  · rw [kernel_of_nonpos m2 (show (s, -y).1 ≤ 0 from hs),
      kernel_of_nonpos m2 (show (s, y).1 ≤ 0 from hs)]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by omega⟩
    rw [kernel_natCast, kernel_natCast, kernelNat_neg]

/-- E1, Lemma 5(d), on natural time slices. -/
theorem kernelNat_parity (n : ℕ) : ∀ y, kernelNat 0 n y ≠ 0 → Odd ((n : ℤ) + y) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => intro y h; exact absurd rfl h
    | 1, _ =>
      intro y h
      rw [kernelNat_one] at h
      split_ifs at h with hy
      · subst hy; decide
      · exact absurd rfl h
    | n + 2, ih =>
      intro y h
      rw [kernelNat_succ_succ, zero_mul, sub_zero] at h
      by_contra hc
      have hc' : Even ((n : ℤ) + y) := by
        rw [← Int.not_odd_iff_even]; intro ho; apply hc
        have : ((n + 2 : ℕ) : ℤ) + y = ((n : ℤ) + y) + 2 := by push_cast; ring
        rw [this]; exact ho.add_even even_two
      have e1 : kernelNat 0 n y = 0 := by
        by_contra h'; exact (Int.not_odd_iff_even.2 hc') (ih n (by omega) y h')
      have e2 : kernelNat 0 (n + 1) (y + 1) = 0 := by
        by_contra h'; have := ih (n + 1) (by omega) _ h'
        apply Int.not_odd_iff_even.2 hc'
        have e : ((n + 1 : ℕ) : ℤ) + (y + 1) = ((n : ℤ) + y) + 2 := by push_cast; ring
        rw [e] at this; exact (Int.odd_add.1 this).2 even_two
      have e3 : kernelNat 0 (n + 1) (y - 1) = 0 := by
        by_contra h'; have := ih (n + 1) (by omega) _ h'
        apply Int.not_odd_iff_even.2 hc'
        have e : ((n + 1 : ℕ) : ℤ) + (y - 1) = (n : ℤ) + y := by push_cast; ring
        rwa [e] at this
      exact h (by rw [e1, e2, e3]; ring)

/-- E1, Lemma 5(d): for `m² = 0`, `K(s, y) ≠ 0` implies that `s + y` is odd. -/
theorem kernel_parity {p : Point} (h : kernel 0 p ≠ 0) : Odd (p.1 + p.2) := by
  obtain ⟨s, y⟩ := p
  by_cases hs : s ≤ 0
  · exact absurd (kernel_of_nonpos 0 (show (s, y).1 ≤ 0 from hs)) h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by omega⟩
    rw [kernel_natCast] at h
    exact kernelNat_parity n y h

/-- The time reflection `(t, x) ↦ (-t, x)`. -/
def timeReflect (p : Point) : Point := (-p.1, p.2)

theorem kgOp_comp_timeReflect (u : Point → ℝ) (p : Point) :
    kgOp m2 (u ∘ timeReflect) p = kgOp m2 u (timeReflect p) := by
  simp only [kgOp, Function.comp, timeReflect, neg_add, neg_sub]
  rw [show -p.1 + -1 = -p.1 - 1 by ring, show -p.1 + 1 = -p.1 + 1 by rfl]
  ring_nf

/-- E1, Lemma 7: a solution vanishing in the far past vanishes. -/
theorem eq_zero_of_kgOp_eq_zero_of_past {u : Point → ℝ} (hu : ∀ p, kgOp m2 u p = 0) (T : ℤ)
    (hT : ∀ p : Point, p.1 < T → u p = 0) : u = 0 := by
  have step : ∀ n : ℕ, (∀ x, u (T - 1 + n, x) = 0) ∧ (∀ x, u (T + n, x) = 0) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun x => hT _ (by simp), fun x => ?_⟩
      have h := hu (T - 1, x)
      simp only [kgOp] at h
      rw [hT (T - 1 - 1, x) (by simp; omega), hT (T - 1, x + 1) (by simp),
        hT (T - 1, x - 1) (by simp), hT (T - 1, x) (by simp)] at h
      simpa [show T - 1 + 1 = T by ring] using h
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · intro x
        have e : T - 1 + ((n + 1 : ℕ) : ℤ) = T + n := by push_cast; ring
        rw [e]; exact ih.2 x
      intro x
      have h := hu (T + n, x)
      simp only [kgOp] at h
      rw [show T + (n : ℤ) - 1 = T - 1 + n by ring, ih.1 x, ih.2 (x + 1), ih.2 (x - 1),
        ih.2 x] at h
      have e : T + ((n + 1 : ℕ) : ℤ) = T + n + 1 := by push_cast; ring
      rw [e]
      linarith
  funext p
  obtain ⟨t, x⟩ := p
  by_cases ht : t < T
  · exact hT _ ht
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = T + n := ⟨(t - T).toNat, by omega⟩
    rw [hn]; exact (step n).2 x

/-- E1, Lemma 7: a solution vanishing in the far future vanishes. -/
theorem eq_zero_of_kgOp_eq_zero_of_future {u : Point → ℝ} (hu : ∀ p, kgOp m2 u p = 0) (T : ℤ)
    (hT : ∀ p : Point, T < p.1 → u p = 0) : u = 0 := by
  have h := eq_zero_of_kgOp_eq_zero_of_past m2 (u := u ∘ timeReflect)
    (fun p => by rw [kgOp_comp_timeReflect, hu]) (-T)
    (fun p hp => hT _ (by simp [timeReflect]; omega))
  funext p
  have := congrFun h (timeReflect p)
  simpa [timeReflect] using this

end Lattice

end LinearAQFT
