module

import Peano

/-!
# Audit: Lemma 5.5 and Corollary 5.6

Restates the lifting lemma and Corollary 5.6 (for an arbitrary `ArcSystem`, the abstract form of a
standard-form continuum) with `recall`, then prints their axioms.

Expected axioms for all three: `propext`, `Classical.choice`, `Quot.sound` only.
-/

open Peano Topology unitInterval

recall Peano.ArcSystem.exists_lift {X : Type*} [MetricSpace X] (S : ArcSystem X)
    [CompactSpace X] [LocallyPathConnectedSpace X]
    (hnull : Filter.Tendsto (fun i => Metric.diam (S.closedArc i)) Filter.cofinite (𝓝 0))
    {B : Type*} [MetricSpace B] {A : Set B} (hA : IsClosed A) (f : C(A, X))
    (g : C(B, S.Coarse)) (hfg : ∀ a, S.q (f a) = g a) :
    ∃ G : C(B, X), (∀ a : A, G a = f a) ∧ ∀ b, S.q (G b) = g b

recall Peano.ArcSystem.isSerreFibration_q {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (S : ArcSystem X) : IsSerreFibration S.q

recall Peano.ArcSystem.isWeakHomotopyEquivalence_q {X : Type*} [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] (S : ArcSystem X) : IsWeakHomotopyEquivalence S.q

#print axioms Peano.ArcSystem.exists_lift
#print axioms Peano.ArcSystem.isSerreFibration_q
#print axioms Peano.ArcSystem.isWeakHomotopyEquivalence_q
