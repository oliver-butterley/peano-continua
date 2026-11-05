module

import Peano

/-!
# Audit: Theorem 1.1 ("if" direction)

Restates the formalised statements of Brazas–Pavešić, Theorem 1.1 ("if"), in full with `recall`
(which fails unless the restatement matches the proved declaration), then prints their axioms.

Expected axioms:
* `exists_countable_weq_of_standardForm`: `propext`, `Classical.choice`, `Quot.sound`,
  `Peano.isClosed_wildSet` (Lemma 2.3).
* `exists_countable_weq`: the above plus `Peano.exists_homotopyEquiv_standardForm` (Theorem 4.2),
  `Peano.nonempty_homeomorph_wildSet` (Brazas–Fischer Thm 9.15) and
  `Peano.HomotopyEquiv.isWeakHomotopyEquivalence` (standard).
-/

open Peano

recall Peano.exists_countable_weq_of_standardForm (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X)
    (hsf : IsStandardForm X) (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f

recall Peano.exists_countable_weq (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) (hne : (wildSet X).Nonempty)
    (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f

#print axioms Peano.exists_countable_weq_of_standardForm
#print axioms Peano.exists_countable_weq
