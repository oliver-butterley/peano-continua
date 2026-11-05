module

import Peano

/-!
# Audit: every axiom of the formalisation

Prints each axiom of `Peano/Axioms/Cited.lean` and `Peano/Axioms/Standard.lean` with its full
statement. This list must match the table in `notes/axioms.md`; `grep -rn '^axiom' Peano` must find
axioms only under `Peano/Axioms/`.
-/

-- Cited from the literature (`Peano/Axioms/Cited.lean`).
#print Peano.exists_homotopyEquiv_standardForm
#print Peano.exists_homotopyEquiv_finiteGraph
#print Peano.eda_exists_map_earring
#print Peano.exists_nhds_monodromy
#print Peano.eda_homotopyEquiv_of_homeomorph
#print Peano.exists_reduced_homotopy
#print Peano.isReparam_of_reduced_homotopic
#print Peano.eda_zeroForm
#print Peano.exists_simpleClosedCurve

-- Standard facts missing from Mathlib (`Peano/Axioms/Standard.lean`).
#print Peano.coveringDimLE_one_of_interior_eq_empty
