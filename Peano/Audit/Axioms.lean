module

import Peano

/-!
# Audit: every axiom of the formalisation

Prints each axiom of `Peano/Axioms/Cited.lean` and `Peano/Axioms/Standard.lean` with its full
statement. This list must match the table in `notes/axioms.md`; `grep -rn '^axiom' Peano` must find
axioms only under `Peano/Axioms/`.
-/

-- Cited from the literature (`Peano/Axioms/Cited.lean`).
#print Peano.isClosed_wildSet
#print Peano.exists_homotopyEquiv_standardForm
#print Peano.nonempty_homeomorph_wildSet

-- Standard facts missing from Mathlib (`Peano/Axioms/Standard.lean`).
#print Peano.HomotopyEquiv.isWeakHomotopyEquivalence
