# Conventions

## Mathematics

- **Signature: mostly plus.** The Klein–Gordon operator is `P = −□ + m²` with `□ = g^{ab}∇_a∇_b`;
  in flat space `P = ∂ₜ² − Δ + m²`. The lattice operator
  `(Pu)(t,x) = u(t+1,x) + u(t−1,x) − u(t,x+1) − u(t,x−1) + m²u(t,x)` is its discrete form. In the
  Lean files on Minkowski space, `□` (the operator `wave`) denotes `∂₀² − Σᵢ ∂ᵢ²`, so that
  "`□ + μ`" means `P + μ`.
- **Green operators.** `G⁺` is the retarded operator, `supp G⁺f ⊆ J⁺(supp f)`, and `G⁻` the
  advanced one (some references, e.g. Bär–Ginoux–Pfäffle, use the opposite names; the notes,
  Remark 7.3, give the table).
- **Commutator function: advanced minus retarded,** `E = G⁻ − G⁺`, so that
  `[φ(f), φ(g)] = i E(f, g)` with `E(f, g) = ⟨f, E g⟩`, and at equal times
  `[φ(t,x), π(t,y)] = i δ(x − y)`.
- **Weyl relation.** `W(u) = e^{iφ(u)}` formally, `σ([f], [g]) = E(f, g)`, and
  `W(u) W(w) = e^{−iσ(u,w)/2} W(u + w)`; `W(u)* = W(−u)`. On `ℓ²(V)`,
  `(W(u)ψ)(v) = e^{iσ(u,v)/2} ψ(v + u)`.
- **Inner products** are linear in the second argument (the physicists' convention, and
  Mathlib's).
- **Causal order.** On `ℤ²` and on 3+1 Minkowski space, `p ≤ q` iff `|q⃗ − p⃗| ≤ q⁰ − p⁰`;
  `J^±(K)` are the causal future and past of a set `K`. Supports are closed supports.
- **Regions and nets.** A causal index is a preorder of regions with a symmetric orthogonality
  relation, antitone in both arguments, and a dependence relation (the region `O'` determines `O`
  causally); a net assigns to each region a norm-closed star subalgebra of a unital C*-algebra,
  monotonically. Generation, causality, time slice and covariance are properties of a net, not
  part of its definition. Covariance is stated for isomorphisms (in particular for
  time-orientation-preserving symmetries); automorphisms compose as `α_{κ₁κ₂} = α_{κ₁} α_{κ₂}`.
- **Time slice.** The dependence is pointwise: every test function localized in `O` has its own
  cutoff region inside `O'` (two consecutive time slices on the lattice, an inertial slab in
  Minkowski space).
- **Assumptions** that are not proved, such as the existence of an irreducible representation
  (`HasIrreducibleRep`) or Green data on a general spacetime, are hypotheses of theorems or fields
  of structures, never axioms.

## Lean

- One definition per concept: the library builds on LocalAlgebrasLean (regions, nets) and
  BosonicLean (the CCR algebra, Weyl systems, simplicity) and re-creates nothing they define. A
  declaration lives in the most general library that can state it.
- Namespaces follow the directories under the root `LinearAQFT` (`Causal`, `Net`, `Symplectic`,
  `Lattice`, `Green`, `Minkowski`); general analysis lemmas with no physics content are in
  `LinearAQFT/Analysis/`, in the namespace `LinearAQFT`.
- Declaration names are ASCII and follow Mathlib's naming and style; lines are at most 100
  characters. Renamed declarations keep a deprecated alias (`LinearAQFT/Deprecated.lean`).
- No unfinished proofs, no added axioms, no unchecked computation, no blanket import of Mathlib.
  The theorems a reader would cite are stated in `verify/Challenge.lean` and judged by
  `lake comparator` (see the front page, "Verification").

## Notes

- The notes follow the library chapter by chapter, with the lattice as the running example; a
  statement marked "Lean ✓" has a checked counterpart, listed in the index at the end, and
  examples are marked "script ✓" or "paper" when they are checked by a script or on paper only.
