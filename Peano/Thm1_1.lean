module

public import Peano.Main

/-!
# Theorem 1.1

Brazas–Pavešić (arXiv:2610.35875), Theorem 1.1: a one-dimensional Peano continuum `X` admits a weak
homotopy equivalence to a countable space iff its wild set `w(X)` is countable.

Both directions are proved:

* "if": `Peano.exists_countable_weq` (`Peano.Main`): Meilstrup's arc-reduced form (cited axiom
  `exists_homotopyEquiv_arcReduced`, thesis Theorem 2.9 and Corollary 2.10) gives the standard form
  (Theorem 4.2), then Lemmas 2.5 and 6.4 keep `w` countable and the coarsification (Corollary 5.6)
  applies; for `w(X) = ∅` (a case the paper misses) it gives a finite graph and its finite
  coarsification.
* "only if": `Peano.countable_wildSet_of_weq` (`Peano.OnlyIf`), from Lemma 6.4.

Lemma 6.4 (`Peano.injOn_wildSet`) is proved in `Peano.OnlyIf` by a homology-free argument from
Theorem 6.1 (Eda, cited) and Lemma 6.2 (from the cited discrete monodromy of Brazas–Fischer). The
paper's own proof of Lemma 6.4, through first homology (Part A: Lemmas 2.8, 3.3, 3.4, 6.3, in
`PeanoPartA.Homology` and `PeanoPartA.Lemmas`), is formalised separately in
`PeanoPartA.Lemma6_4Paper`
(`Peano.injOn_wildSet_of_paper`) and is not used here. The axioms used are listed in
`Peano/Audit/Thm1_1.lean`. The wild set may equivalently be taken in the loop sense of the
introduction (`exists_countable_weq_iff_loopWildSet`).

The countable space ranges over `Type`; any countable space in another universe is homeomorphic to
one in `Type`, so this loses nothing. `X : Type` because the cited axioms are stated for `Type`;
a compact metric space has at most continuum many points, so this is no restriction in substance.
-/

@[expose] public section

namespace Peano

/-- **Theorem 1.1**: a one-dimensional Peano continuum is weakly homotopy equivalent to a countable
space iff its wild set is countable. -/
theorem exists_countable_weq_iff (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) :
    (∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f) ↔ (wildSet X).Countable := by
  refine ⟨?_, exists_countable_weq X hdim⟩
  rintro ⟨Y, _, hY, f, hf⟩
  exact countable_wildSet_of_weq X hdim hf

/-- **Theorem 1.1** with the wild set of the paper's introduction (`loopWildSet`: every
neighbourhood contains an essential loop based at the point). -/
theorem exists_countable_weq_iff_loopWildSet (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) :
    (∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f) ↔ (loopWildSet X).Countable := by
  rw [exists_countable_weq_iff X hdim, wildSet_eq_loopWildSet]

end Peano
