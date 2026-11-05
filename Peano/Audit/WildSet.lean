module

import Peano

/-!
# Audit: wild sets (Definition 2.2 vs the introduction, Lemmas 2.3, 2.5, 6.2, |w(X)| ≤ |w(Y)|)

`wildSet_eq_loopWildSet` is the bridge used by every axiom stated with `loopWildSet` (the
definition of the cited sources). Expected axioms: the standard three, except
`eq_of_homotopic_conj` (Lemma 6.2), which uses `Peano.exists_nhds_monodromy`, and `mk_wildSet_le`
(consequence of Lemma 6.4), which uses `Peano.exists_nhds_monodromy` and
`Peano.eda_exists_map_earring`.
-/

open Peano

recall Peano.wildSet_eq_loopWildSet (X : Type*) [TopologicalSpace X] [FirstCountableTopology X] :
    wildSet X = loopWildSet X

recall Peano.isClosed_wildSet (X : Type*) [MetricSpace X] [LocallyPathConnectedSpace X] :
    IsClosed (wildSet X)

recall Peano.image_wildSet_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Injective (FundamentalGroup.map f x)) :
    f '' wildSet X ⊆ wildSet Y

recall Peano.earringBase_mem_wildSet : earringBase ∈ wildSet earring

recall Peano.eq_of_homotopic_conj {X : Type} [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {x y : X} {γ : ℕ → Path x x} {δ : ℕ → Path y y}
    (hγ : LoopsShrinkTo x γ) (hδ : LoopsShrinkTo y δ)
    (hess : ∀ k, ¬ (γ k).Homotopic (Path.refl x)) (α : Path y x)
    (hconj : ∀ k, (γ k).Homotopic ((α.symm.trans (δ k)).trans α)) : y = x

recall Peano.mk_wildSet_le (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Bijective (FundamentalGroup.map f x)) :
    Cardinal.mk (wildSet X) ≤ Cardinal.mk (wildSet Y)

#print axioms Peano.wildSet_eq_loopWildSet
#print axioms Peano.isClosed_wildSet
#print axioms Peano.image_wildSet_subset
#print axioms Peano.earringBase_mem_wildSet
#print axioms Peano.eq_of_homotopic_conj
#print axioms Peano.mk_wildSet_le
