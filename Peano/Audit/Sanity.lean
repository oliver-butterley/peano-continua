module

import Peano

/-!
# Audit: non-vacuity and the counterexample to the paper's Theorem 1.2

Prints the axioms of the sanity theorems of `Peano.Sanity`: weak homotopy equivalence is not a
trivial notion, the earring has wild set `{b₀}`, Theorem 1.1 has instances with non-empty wild
set, the paper's canonical correspondence of Theorem 1.2 is not a bijection (the point and the
circle; the circle and an arc, both of dimension exactly one), and `CoveringDimLE` is not trivial
(the unit interval is not zero-dimensional). Also restates Remark 6.5 (`Peano.Remark6_5`): the
injection of Lemma 6.4 need not be a bijection.

Expected axioms:
* `not_isWeakHomotopyEquivalence_addCircle_const`, `remark6_5`: the standard three only;
* `wildSet_earring`: the standard three only;
* `not_coveringDimLE_zero_unitInterval`, `earringCircle_zero_finite_weq`: the standard three only;
* `exists_countable_weq_of_wildSet_nonempty`: those of Theorem 1.1 ("if" direction:
  `exists_homotopyEquiv_standardForm`, `exists_homotopyEquiv_finiteGraph`,
  `eda_exists_map_earring`, `exists_nhds_monodromy`) and `coveringDimLE_one_of_interior_eq_empty`;
* `thm1_2_counterexample`, `thm1_2_counterexample_dim_one`,
  `not_forall_nonempty_homotopyEquiv_iff_wildSet`: `coveringDimLE_one_of_interior_eq_empty`.
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
