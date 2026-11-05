module

import Peano

/-!
# Audit: Lemmas 4.3, 4.5, Corollary 4.4 and Remark 5.1, Lemma 5.2

Restates the §4 results and the countability and openness of the coarsification with `recall`,
then checks their axioms with `#guard_msgs` (the build fails if the list changes).

Expected axioms for all: `propext`, `Classical.choice`, `Quot.sound` only.
-/

open Peano Filter Topology

recall Peano.ArcSystem.tendsto_diam_closedArc {X : Type*} [MetricSpace X] (S : ArcSystem X)
    [CompactSpace X] [LocallyPathConnectedSpace X] :
    Tendsto (fun i => Metric.diam (S.closedArc i)) cofinite (𝓝 0)

recall Peano.ArcSystem.eventually_closedArc_subset {X : Type*} [MetricSpace X] (S : ArcSystem X)
    [CompactSpace X] [LocallyPathConnectedSpace X] {u : ℕ → S.ι} (hu : Function.Injective u)
    {e : ℕ → X} (he : ∀ k, e k ∈ S.ends (u k)) {x : X} (hx : Tendsto e atTop (𝓝 x)) {U : Set X}
    (hU : U ∈ 𝓝 x) : ∀ᶠ k in atTop, S.closedArc (u k) ⊆ U

recall Peano.ArcSystem.isOpen_iff_localCondition {X : Type*} [MetricSpace X] (S : ArcSystem X)
    [CompactSpace X] [LocallyPathConnectedSpace X] {U : Set X} :
    IsOpen U ↔ S.LocalCondition U

recall Peano.ArcSystem.countable_coarse {X : Type*} [MetricSpace X] (S : ArcSystem X)
    [TopologicalSpace.SeparableSpace X] (hW : S.W.Countable) : Countable S.Coarse

recall Peano.ArcSystem.isOpenMap_q {X : Type*} [MetricSpace X] (S : ArcSystem X) :
    IsOpenMap S.q

/--
info: 'Peano.ArcSystem.tendsto_diam_closedArc' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.tendsto_diam_closedArc
/--
info: 'Peano.ArcSystem.eventually_closedArc_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.eventually_closedArc_subset
/--
info: 'Peano.ArcSystem.isOpen_iff_localCondition' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.isOpen_iff_localCondition
/--
info: 'Peano.ArcSystem.countable_coarse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.countable_coarse
/--
info: 'Peano.ArcSystem.isOpenMap_q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Peano.ArcSystem.isOpenMap_q
