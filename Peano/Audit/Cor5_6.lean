module

import Peano

/-!
# Audit: Lemmas 5.4, 5.4′, 5.5 and Corollary 5.6

Restates the extension lemmas, the lifting lemma and Corollary 5.6 (for an arbitrary `ArcSystem`,
the abstract form of a standard-form continuum), and the arc system of a standard-form continuum,
with `recall`, then checks their axioms with `#guard_msgs` (the build fails if the list changes).

Expected axioms for all: `propext`, `Classical.choice`, `Quot.sound` only.
-/

open Peano Topology unitInterval

recall Peano.ArcSystem.exists_extension_preimage_eq {B : Type*} [MetricSpace B] {A : Set B}
    (hA : IsClosed A) (h : C(A, I)) (h01 : ∀ a, h a = 0 ∨ h a = 1) :
    ∃ k : C(B, I), (∀ a : A, k a = h a) ∧ {b | k b = 0 ∨ k b = 1} = A

recall Peano.ArcSystem.exists_extension_interior {B : Type*} [MetricSpace B] {A : Set B}
    (hA : IsClosed A) (h : C(A, I)) :
    ∃ k : C(B, I), (∀ a : A, k a = h a) ∧ ∀ b ∉ A, k b ∈ openUnit

recall Peano.IsStandardForm.exists_arcSystem {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (hX : IsStandardForm X) : ∃ S : ArcSystem X, S.W = wildSet X

recall Peano.ArcSystem.exists_lift {X : Type*} [MetricSpace X] (S : ArcSystem X)
    (hnull : Filter.Tendsto (fun i => Metric.diam (S.closedArc i)) Filter.cofinite (𝓝 0))
    {B : Type*} [MetricSpace B] {A : Set B} (hA : IsClosed A) (f : C(A, X))
    (g : C(B, S.Coarse)) (hfg : ∀ a, S.q (f a) = g a) :
    ∃ G : C(B, X), (∀ a : A, G a = f a) ∧ ∀ b, S.q (G b) = g b

recall Peano.ArcSystem.isSerreFibration_q {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (S : ArcSystem X) : IsSerreFibration S.q

recall Peano.ArcSystem.isWeakHomotopyEquivalence_q {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (S : ArcSystem X) : IsWeakHomotopyEquivalence S.q

recall Peano.ArcSystem.countable_weq_q {X : Type*} [MetricSpace X] (S : ArcSystem X)
    [TopologicalSpace.SeparableSpace X]
    (hnull : Filter.Tendsto (fun i => Metric.diam (S.closedArc i)) Filter.cofinite (𝓝 0))
    (hW : S.W.Countable) : Countable S.Coarse ∧ IsWeakHomotopyEquivalence S.q

recall Peano.ArcSystem.finite_weq_q_of_finite {X : Type*} [MetricSpace X] [CompactSpace X]
    (S : ArcSystem X) [Finite S.ι] (hW : S.W.Finite) :
    Finite S.Coarse ∧ IsWeakHomotopyEquivalence S.q

/--
info: 'Peano.ArcSystem.exists_extension_preimage_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.exists_extension_preimage_eq
/--
info: 'Peano.ArcSystem.exists_extension_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.exists_extension_interior
/--
info: 'Peano.IsStandardForm.exists_arcSystem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.IsStandardForm.exists_arcSystem
/--
info: 'Peano.ArcSystem.exists_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.exists_lift
/--
info: 'Peano.ArcSystem.countable_weq_q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.countable_weq_q
/--
info: 'Peano.ArcSystem.finite_weq_q_of_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.finite_weq_q_of_finite
/--
info: 'Peano.ArcSystem.isSerreFibration_q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.isSerreFibration_q
/--
info: 'Peano.ArcSystem.isWeakHomotopyEquivalence_q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.isWeakHomotopyEquivalence_q
