# Slices: extracting part of the library

A *slice* is the part of LinearAQFT that a chosen set of theorems needs. The three slices here
cover the results that correspond to J. Dimock, "Algebras of local observables on a manifold",
Commun. Math. Phys. 77 (1980) 219–228. They are what remains of the original purpose of the
library as it grows past it.

| Slice | Theorems (library form of the axioms of Dimock (1980)) | LinearAQFT modules | Declarations used / unused in those modules |
|---|---|---|---|
| `dimock-abstract` | Axioms 1–4 for any phase-space data with nondegenerate σ (primitivity given an irreducible representation); Axiom 5 for the CCR net | 6 | 367 / 82 |
| `dimock-lattice` | the unconditional instance on ℤ² with translation covariance | 17 | 714 / 147 |
| `dimock-minkowski` | Axioms 1–4 for any Green data; the free massless field on 3+1 Minkowski space with Poincaré covariance | 24 (no lattice module) | 1008 / 148 |

The declaration counts include the declarations each slice uses from LocalAlgebrasLean (4
modules: regions, nets, generated nets, the lattice of regions) and from BosonicLean (8 modules).
Regenerated on 13 Oct 2026 at LocalAlgebrasLean 444adac and BosonicLean da615b7; since that date
the closure follows LocalAlgebrasLean too, where nets have lived since 6 Oct 2026, so the counts
are not comparable with the earlier ones (30 Sep 2026: 340 / 52, 685 / 117, 981 / 118). The
lecture notes have a matching edition, `docs/lecture-notes/LinearAQFT-Dimock.pdf`. The main
theorems are named `ccrNet_axioms_primitive`, in `Symplectic/Axioms.lean` and
`Lattice/Axioms.lean`; `slices/<name>.closure.json` holds the current record. The massive field
(`Minkowski/Mass.lean`, notes chapter 9) is not in any slice.

These are the library's versions of the results of Dimock (1980), not his Theorem 4 verbatim. The
differences (Green data instead of a globally hyperbolic manifold, pointwise time slice,
primitivity given an irreducible representation, time-orientation-preserving covariance) are in
the lecture notes, Remark `rem:dimock-thm4`, and for Minkowski space Remark 8.13.

## Files

- `slices/<name>.toml`, the manifest:
  - `targets`: the theorems;
  - `allowed_modules`: the exact LinearAQFT module closure;
  - `notes_labels`: the lecture-notes labels of the targets;
  - the source, and where the differences from it are recorded.
- `slices/Dimock/*.lean`, the facades. Each imports only the modules that hold its targets,
  restates every target with its type written out (copied from the approved statement
  probes), and prints its axioms. They add no declarations.
- `slices/<name>.closure.json`: the declaration closure, a generated record.

## Commands

| Command | Needs Lean | What it does |
|---|---|---|
| `python tools/slice_closure.py --all` | no | Follows `import` lines from each facade. Fails if the LinearAQFT module closure differs from `allowed_modules`, or if a target has no correspondence entry under the listed notes labels. Run it at every milestone: it catches later stages leaking into a slice. |
| `lake build LinearAQFTDimock` | yes | Builds only the three facades and what they import. The facades print `#print axioms` for every target. |
| `lake build LinearAQFT SliceTools`, then `python tools/slice_closure.py --decls slices/<name>.toml` | yes | Writes `slices/<name>.closure.json`: every declaration the targets use, stopping at Mathlib, and the declarations of those modules they do not use. |
| `python tools/export_slice.py slices/<name>.toml --out <new dir>` | to build the result | Copies the closure modules and the facade verbatim into a standalone Lake package, with the same LocalAlgebrasLean, BosonicLean, Mathlib and Lean versions and a README. It refuses an existing directory and never deletes anything. Build it with `lake exe cache get && lake build`. The export stays local; nothing is published. |

## What extraction can and cannot guarantee

- **Proof terms (kernel level).** A theorem together with every constant it uses is a
  self-contained environment. This is exact: it is the traversal behind `#print axioms` and the
  `--decls` record.
- **Files (module level).** The import closure of the facade builds on its own; the export
  demonstrates it. How small the closure is depends on how cleanly the files are split. Before
  30 Sep 2026 the Minkowski slice also pulled in six lattice modules, because a general lemma
  (`Symplectic.ccrAlpha_congr`) lived in `Lattice/Net.lean` (stage-G finding 14); moving it fixed
  that.
- **Single declarations in source.** Dropping the unused declarations inside a file is possible,
  but the closure alone does not guarantee that the result compiles. A lemma used by a tactic
  may leave no trace in the proof term (for example a `rfl` lemma used by `dsimp`), so every
  pruning must be followed by a rebuild. The export does not prune.

## Verified on 30 Sep 2026

- The library builds with no warnings (3188 jobs; after merging `main`'s closing pass, 3199).
- `lake build LinearAQFTDimock` succeeds; every target depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- All statement probes compile (14 before the merge; 16 after it, with H3 and H4).
- The abstract and Minkowski exports build as standalone packages, with the same axioms. The
  Minkowski export has no `Lattice` directory.
