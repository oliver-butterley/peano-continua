module

import Peano

/-!
# Audit: Theorem 1.1 and Lemma 6.4

Restates Brazas–Pavešić, Theorem 1.1 (both directions) and Lemma 6.4 in full with `recall` (which
fails unless the restatement matches the proved declaration), then prints their axioms.

Expected axioms (besides `propext`, `Classical.choice`, `Quot.sound`):
* `exists_countable_weq_of_standardForm`: none.
* `injOn_wildSet` (Lemma 6.4), `countable_wildSet_of_weq` ("only if"):
  `Peano.eda_exists_map_earring` (Theorem 6.1), `Peano.exists_nhds_monodromy` (Brazas–Fischer).
* `exists_countable_weq` ("if"): the two above plus `Peano.exists_homotopyEquiv_arcReduced`
  (Meilstrup's Theorem 2.9 and Corollary 2.10; the paper's Theorem 4.2 and the case `w = ∅`).
* `exists_countable_weq_iff` (Theorem 1.1), `exists_countable_weq_iff_loopWildSet`: the three cited
  axioms above.
* `exists_finite_weq_of_loopWildSet_eq_empty` (case `w = ∅`):
  `Peano.exists_homotopyEquiv_arcReduced` only.

`exists_countable_weq_of_standardForm` keeps the hypothesis `CoveringDimLE 1 X` of the paper
although its proof does not use it (the binder is `_hdim` in `Peano.Main`; `recall` ignores binder
names).
-/

open Peano

recall Peano.exists_countable_weq_of_standardForm (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X)
    (hsf : IsStandardForm X) (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f

recall Peano.exists_countable_weq (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f

recall Peano.injOn_wildSet (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Bijective (FundamentalGroup.map f x)) :
    Set.InjOn f (wildSet X)

recall Peano.exists_countable_weq_iff (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) :
    (∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f) ↔ (wildSet X).Countable

recall Peano.exists_countable_weq_iff_loopWildSet (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) :
    (∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f) ↔ (loopWildSet X).Countable

recall Peano.exists_finite_weq_of_loopWildSet_eq_empty (X : Type) [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X)
    (hw : loopWildSet X = ∅) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Finite Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f

recall Peano.countable_wildSet_of_weq (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*}
    [TopologicalSpace Y] [Countable Y] {f : C(X, Y)} (hf : IsWeakHomotopyEquivalence f) :
    (wildSet X).Countable

#print axioms Peano.exists_countable_weq_of_standardForm
#print axioms Peano.exists_countable_weq
#print axioms Peano.injOn_wildSet
#print axioms Peano.exists_countable_weq_iff
#print axioms Peano.countable_wildSet_of_weq
#print axioms Peano.exists_countable_weq_iff_loopWildSet
#print axioms Peano.exists_finite_weq_of_loopWildSet_eq_empty
