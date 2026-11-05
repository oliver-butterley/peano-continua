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

/-- A homotopy equivalence is a weak homotopy equivalence (Hatcher, *Algebraic Topology*,
Proposition 1.18 for `π₁` and §4.1, p. 342, for `πₙ`; the proof transports along the homotopy
`g ∘ f ≃ id` with the change-of-basepoint isomorphisms). Assumed because Mathlib has neither
induced maps on `πₙ` nor change of basepoint for `πₙ`, `n ≥ 2`. Used in the paper's proof of
Theorem 1.1 when it replaces `X` by a standard-form continuum. -/
axiom HomotopyEquiv.isWeakHomotopyEquivalence {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    IsWeakHomotopyEquivalence e.toFun

end Peano
