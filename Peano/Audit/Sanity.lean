module

import Peano

/-!
# Audit: non-vacuity and the counterexample to the paper's Theorem 1.2

Checks, with `#guard_msgs`, the axioms of the sanity theorems of `Peano.Sanity`: weak homotopy equivalence is not a
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

/--
info: Sanity.not_isWeakHomotopyEquivalence_addCircle_const : ¬IsWeakHomotopyEquivalence (ContinuousMap.const (AddCircle 1) ())
-/
#guard_msgs in
#check @Peano.Sanity.not_isWeakHomotopyEquivalence_addCircle_const
/--
info: Sanity.wildSet_earring : wildSet ↑earring = {earringBase}
-/
#guard_msgs in
#check @Peano.Sanity.wildSet_earring
/--
info: Sanity.exists_countable_weq_of_wildSet_nonempty : ∃ X x,
  CompactSpace X ∧
    ConnectedSpace X ∧
      LocallyPathConnectedSpace X ∧
        CoveringDimLE 1 X ∧ (wildSet X).Nonempty ∧ ∃ Y x_1, Countable Y ∧ ∃ f, IsWeakHomotopyEquivalence f
-/
#guard_msgs in
#check @Peano.Sanity.exists_countable_weq_of_wildSet_nonempty
/--
info: Sanity.thm1_2_counterexample : (CompactSpace Unit ∧
    ConnectedSpace Unit ∧
      LocallyPathConnectedSpace Unit ∧
        CoveringDimLE 1 Unit ∧ wildSet Unit = ∅ ∧ ∃ Y x, Countable Y ∧ ∃ f, IsWeakHomotopyEquivalence f) ∧
  (CompactSpace ↑(earringCircle 0) ∧
      ConnectedSpace ↑(earringCircle 0) ∧
        LocallyPathConnectedSpace ↑(earringCircle 0) ∧
          CoveringDimLE 1 ↑(earringCircle 0) ∧
            wildSet ↑(earringCircle 0) = ∅ ∧ ∃ Y x, Countable Y ∧ ∃ f, IsWeakHomotopyEquivalence f) ∧
    IsEmpty (ContinuousMap.HomotopyEquiv Unit ↑(earringCircle 0)) ∧
      ∀ (X : Type) [inst : TopologicalSpace X],
        (wildSet X).Nonempty →
          IsEmpty (ContinuousMap.HomotopyEquiv X Unit) ∧ IsEmpty (ContinuousMap.HomotopyEquiv X ↑(earringCircle 0))
-/
#guard_msgs in
#check @Peano.Sanity.thm1_2_counterexample
/--
info: Sanity.not_forall_nonempty_homotopyEquiv_iff_wildSet : ¬∀ (X Y : Type) [inst : MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [inst_4 : MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    [LocallyPathConnectedSpace Y],
    CoveringDimLE 1 X →
      CoveringDimLE 1 Y →
        (wildSet X).Countable →
          (wildSet Y).Countable → (Nonempty (ContinuousMap.HomotopyEquiv X Y) ↔ Nonempty (↑(wildSet X) ≃ₜ ↑(wildSet Y)))
-/
#guard_msgs in
#check @Peano.Sanity.not_forall_nonempty_homotopyEquiv_iff_wildSet
/--
info: Sanity.thm1_2_counterexample_dim_one : (CompactSpace ↑(earringCircle 0) ∧
    ConnectedSpace ↑(earringCircle 0) ∧
      LocallyPathConnectedSpace ↑(earringCircle 0) ∧
        CoveringDimLE 1 ↑(earringCircle 0) ∧
          ¬CoveringDimLE 0 ↑(earringCircle 0) ∧
            wildSet ↑(earringCircle 0) = ∅ ∧ ∃ Y x, Finite Y ∧ ∃ f, IsWeakHomotopyEquivalence f) ∧
  (CompactSpace ↑Sanity.planarArc ∧
      ConnectedSpace ↑Sanity.planarArc ∧
        LocallyPathConnectedSpace ↑Sanity.planarArc ∧
          CoveringDimLE 1 ↑Sanity.planarArc ∧
            ¬CoveringDimLE 0 ↑Sanity.planarArc ∧
              wildSet ↑Sanity.planarArc = ∅ ∧ ∃ Y x, Finite Y ∧ ∃ f, IsWeakHomotopyEquivalence f) ∧
    IsEmpty (ContinuousMap.HomotopyEquiv ↑(earringCircle 0) ↑Sanity.planarArc)
-/
#guard_msgs in
#check @Peano.Sanity.thm1_2_counterexample_dim_one

recall Peano.Sanity.not_coveringDimLE_zero_unitInterval : ¬ CoveringDimLE 0 I

/--
info: 'Peano.Sanity.not_isWeakHomotopyEquivalence_addCircle_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.not_isWeakHomotopyEquivalence_addCircle_const
/--
info: 'Peano.Sanity.wildSet_earring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.wildSet_earring
/--
info: 'Peano.Sanity.exists_countable_weq_of_wildSet_nonempty' depends on axioms: [propext,
 Classical.choice,
 eda_exists_map_earring,
 exists_homotopyEquiv_arcReduced,
 exists_nhds_monodromy,
 Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.exists_countable_weq_of_wildSet_nonempty
/--
info: 'Peano.Sanity.thm1_2_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.thm1_2_counterexample
/--
info: 'Peano.Sanity.not_forall_nonempty_homotopyEquiv_iff_wildSet' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.not_forall_nonempty_homotopyEquiv_iff_wildSet
/--
info: 'Peano.Sanity.thm1_2_counterexample_dim_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.thm1_2_counterexample_dim_one
/--
info: 'Peano.Sanity.not_coveringDimLE_zero_unitInterval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.not_coveringDimLE_zero_unitInterval
/--
info: 'Peano.Sanity.earringCircle_zero_finite_weq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.earringCircle_zero_finite_weq
/--
info: 'Peano.Remark6_5.remark6_5' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Remark6_5.remark6_5

/--
info: @Sanity.not_coveringDimLE_zero : ∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X] [ConnectedSpace X] {a b : X},
  a ≠ b → ¬CoveringDimLE 0 X
-/
#guard_msgs in
#check @Peano.Sanity.not_coveringDimLE_zero
/--
info: 'Peano.Sanity.not_coveringDimLE_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.not_coveringDimLE_zero
/--
info: 'Peano.Sanity.thm1_2_counterexample_dim_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
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

/--
info: 'Peano.Sanity.exists_peano_wildSet_not_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.exists_peano_wildSet_not_countable
/--
info: 'Peano.Sanity.exists_no_countable_model' depends on axioms: [propext,
 Classical.choice,
 eda_exists_map_earring,
 exists_homotopyEquiv_arcReduced,
 exists_nhds_monodromy,
 Quot.sound]
-/
#guard_msgs in
#print axioms Peano.Sanity.exists_no_countable_model

-- One-dimensionality without axioms (`Peano.Dimension`).
/--
info: @coveringDimLE_one_of_finite_frontier : ∀ {X : Type u_1} [inst : TopologicalSpace X] [CompactSpace X] [T2Space X],
  (∀ (x : X), ∀ N ∈ nhds x, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ (frontier W).Finite) → CoveringDimLE 1 X
-/
#guard_msgs in
#check @Peano.coveringDimLE_one_of_finite_frontier
/--
info: 'Peano.coveringDimLE_one_of_finite_frontier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.coveringDimLE_one_of_finite_frontier
/--
info: 'Peano.ModelData.coveringDimLE_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ModelData.coveringDimLE_model
