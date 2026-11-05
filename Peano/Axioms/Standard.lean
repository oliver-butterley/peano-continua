module

public import Peano.Defs

/-!
# Standard facts missing from Mathlib, assumed as axioms

The trust boundary of the formalisation, part 2 of 2 (part 1: `Peano.Axioms.Cited`). Each axiom
is a textbook fact that the paper uses without comment and that Mathlib (v4.35.0) does not
provide; its docstring gives a textbook reference and why it is assumed rather than proved. Facts
that are cheap to prove are proved instead (for example `IsWeakHomotopyEquivalence.comp`). Audit
table: `notes/axioms.md`; review: `notes/checks/axioms-review.md`.
-/

@[expose] public section

open Topology

namespace Peano

/-- **Planar sets with empty interior are at most one-dimensional** (Hurewicz–Wallman, *Dimension
Theory*, Theorem IV.3: a subset of `ℝⁿ` has dimension `n` iff it contains a non-empty open subset
of `ℝⁿ`; and Theorem V.8: for separable metric spaces the covering dimension equals the inductive
dimension). Assumed because Mathlib has no covering dimension theory. Used to see that the model
continua `A_K` of Theorem 1.2 are one-dimensional. Stated only for compact sets, the case used. -/
axiom coveringDimLE_one_of_interior_eq_empty (A : Set (ℝ × ℝ)) (hA : IsCompact A)
    (hint : interior A = ∅) : CoveringDimLE 1 A

end Peano
