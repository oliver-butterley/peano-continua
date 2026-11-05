module

public import Peano.Defs

/-!
# Standard facts missing from Mathlib, assumed as axioms

The trust boundary of the formalisation, part 2 of 2 (part 1: `Peano.Axioms.Cited`): textbook
facts that the paper uses without comment and that Mathlib does not provide. Each axiom's
docstring would give a textbook reference and why it is assumed rather than proved. Audit table:
`notes/axioms.md`; review: `notes/checks/axioms-review.md`.

**At present this file contains no axiom.** The last one, `coveringDimLE_one_of_interior_eq_empty`
(planar compacta with empty interior are at most one-dimensional), was removed: the
one-dimensionality of the planar spaces of the formalisation (the models of Theorem 1.2, the
circle, the arc and the earring) is now proved directly, since they are rim-finite
(`Peano.coveringDimLE_one_of_finite_frontier` in `Peano.Dimension`). The file is kept as the
designated place for such axioms.
-/

@[expose] public section
