module

import Peano

/-!
# Audit: non-vacuity and the counterexample to the paper's Theorem 1.2

Prints the axioms of the sanity theorems of `Peano.Sanity`: weak homotopy equivalence is not a
trivial notion, the earring has wild set `{b₀}`, Theorem 1.1 has instances with non-empty wild
set, the paper's canonical correspondence of Theorem 1.2 is not a bijection (the point and the
circle; the circle and an arc, both of dimension exactly one), and `CoveringDimLE` is not trivial
(the unit interval is not zero-dimensional), and the "only if" direction of Theorem 1.1 has an
instance (a continuum with uncountable wild set and no countable weak model).
Also restates Remark 6.5 (`Peano.Remark6_5`): the
injection of Lemma 6.4 need not be a bijection.

Expected axioms:
* `not_isWeakHomotopyEquivalence_addCircle_const`, `remark6_5`: the standard three only;
* `wildSet_earring`: the standard three only;
* `not_coveringDimLE_zero_unitInterval`, `earringCircle_zero_finite_weq`: the standard three only;
* `exists_countable_weq_of_wildSet_nonempty`: those of Theorem 1.1 ("if" direction:
  `exists_homotopyEquiv_arcReduced`, `eda_exists_map_earring`, `exists_nhds_monodromy`) only;
* `thm1_2_counterexample`, `thm1_2_counterexample_dim_one`,
  `not_forall_nonempty_homotopyEquiv_iff_wildSet`: the standard three only (one-dimensionality is
  proved, `Peano.Dimension`);
* `exists_peano_wildSet_not_countable` (a one-dimensional Peano continuum with uncountable wild
  set): the standard three only;
* `exists_no_countable_model` (hence no countable weak model): those of the "only if" direction
  of Theorem 1.1 (`eda_exists_map_earring`, `exists_nhds_monodromy`) and, since it goes through the
  equivalence `exists_countable_weq_iff`, also `exists_homotopyEquiv_arcReduced`;
* `coveringDimLE_one_of_finite_frontier`, `ModelData.coveringDimLE_model`: the standard three only.
-/

open Peano unitInterval

recall Peano.Remark6_5.remark6_5 :
    (∀ x, Peano.Remark6_5.earringProdHomotopyEquiv x = (x, 0)) ∧
      wildSet earring = {earringBase} ∧
      {earringBase} ×ˢ Set.univ ⊆ wildSet (earring × I) ∧
      ¬ Set.SurjOn Peano.Remark6_5.earringProdHomotopyEquiv (wildSet earring)
        (wildSet (earring × I)) ∧
      ¬ (wildSet (earring × I)).Countable

#check @Peano.Sanity.not_isWeakHomotopyEquivalence_addCircle_const
#check @Peano.Sanity.wildSet_earring
#check @Peano.Sanity.exists_countable_weq_of_wildSet_nonempty
#check @Peano.Sanity.thm1_2_counterexample
#check @Peano.Sanity.not_forall_nonempty_homotopyEquiv_iff_wildSet
#check @Peano.Sanity.thm1_2_counterexample_dim_one

recall Peano.Sanity.not_coveringDimLE_zero_unitInterval : ¬ CoveringDimLE 0 I

#print axioms Peano.Sanity.not_isWeakHomotopyEquivalence_addCircle_const
#print axioms Peano.Sanity.wildSet_earring
#print axioms Peano.Sanity.exists_countable_weq_of_wildSet_nonempty
#print axioms Peano.Sanity.thm1_2_counterexample
#print axioms Peano.Sanity.not_forall_nonempty_homotopyEquiv_iff_wildSet
#print axioms Peano.Sanity.thm1_2_counterexample_dim_one
#print axioms Peano.Sanity.not_coveringDimLE_zero_unitInterval
#print axioms Peano.Sanity.earringCircle_zero_finite_weq
#print axioms Peano.Remark6_5.remark6_5

#check @Peano.Sanity.not_coveringDimLE_zero
#print axioms Peano.Sanity.not_coveringDimLE_zero
#print axioms Peano.Sanity.thm1_2_counterexample_dim_one

-- An instance of the "only if" direction of Theorem 1.1: uncountable wild set, no countable model.
recall Peano.Sanity.exists_peano_wildSet_not_countable :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X) (_ : ConnectedSpace X)
      (_ : LocallyPathConnectedSpace X), CoveringDimLE 1 X ∧ ¬ (wildSet X).Countable

recall Peano.Sanity.exists_no_countable_model :
    ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X) (_ : ConnectedSpace X)
      (_ : LocallyPathConnectedSpace X), CoveringDimLE 1 X ∧ ¬ (wildSet X).Countable ∧
        ¬ ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
          ∃ f : C(X, Y), IsWeakHomotopyEquivalence f

#print axioms Peano.Sanity.exists_peano_wildSet_not_countable
#print axioms Peano.Sanity.exists_no_countable_model

-- One-dimensionality without axioms (`Peano.Dimension`).
#check @Peano.coveringDimLE_one_of_finite_frontier
#print axioms Peano.coveringDimLE_one_of_finite_frontier
#print axioms Peano.ModelData.coveringDimLE_model
