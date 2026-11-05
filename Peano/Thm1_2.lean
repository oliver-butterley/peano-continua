module

public import Peano.Thm1_1
public import Peano.BrazasFischer
public import Peano.WildSet
public import Peano.Models
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Theorem 1.2, corrected

Brazas–Pavešić state (Theorem 1.2): there is a canonical bijection between homeomorphism types of
compact countable ordinals and homotopy types of one-dimensional Peano continua that admit a weak
homotopy equivalence to a countable space, `λ ↦ Ho(A_λ)` (inverse `X ↦ w(X)`). This canonical
correspondence is not a bijection: the point and the circle (or, in dimension exactly one, the
circle and an arc) both have such models and empty wild sets, are not homotopy equivalent, and are
not homotopy equivalent to any of the paper's models `A_λ`, so `λ ↦ Ho(A_λ)` is not surjective and
`X ↦ w(X)` is not injective (`notes/checks/D.md`; formalised as
`Peano.Sanity.thm1_2_counterexample`, `Peano.Sanity.thm1_2_counterexample_dim_one`). The cited
Theorem 6.6 (Eda 2022) is false without the hypothesis "non-empty wild sets". What is refuted is
the classification and its proof, not the existence of some bijection: both sets have cardinality
`ℵ₁`, so a bijection exists for cardinality reasons.

The corrected statement, for one-dimensional Peano continua with **non-empty** countable wild set
(by Theorem 1.1 these are exactly the ones with a countable weak model and `w ≠ ∅`), is split into:

* **injectivity / well-definedness** (`nonempty_homotopyEquiv_iff`): two such continua are
  homotopy equivalent iff their wild sets are homeomorphic (Brazas–Fischer Thm 9.15 and Eda 2022);
* **surjectivity** (`exists_wildSet_homeomorph`): every non-empty countable compact metric space is
  the wild set of such a continuum, a planar model built in `Peano.Models` (a segment with an
  earring attached at each point of a copy of `K`; the repaired construction of the paper's `A_λ`,
  `notes/checks/D.md`). Its one-dimensionality is proved directly (the model is rim-finite,
  `Peano.Dimension`), so this half uses no axiom beyond Lean's.

So `X ↦ w(X)` is a bijection from homotopy types onto homeomorphism types of non-empty countable
compact metric spaces: it lands there (`w(X)` is compact, `compactSpace_wildSet`, by Lemma 2.3),
is well defined on homotopy types ("⇒" of `nonempty_homotopyEquiv_iff`), injective ("⇐") and
surjective (`exists_wildSet_homeomorph`). `nonempty_homotopyEquiv_iff_of_weq` restates the
classification for the class of the paper (continua with a countable weak model), via Theorem 1.1.
`CoveringDimLE 1` means dimension `≤ 1`; with `w(X) ≠ ∅` the dimension is exactly `1` (a
zero-dimensional continuum is a point). The paper indexes the models by countable ordinals `λ`;
indexing by arbitrary countable compact `K` avoids the ordinal conventions criticised in
`notes/checks/D.md` (`λ` vs `λ + 1`, the case `λ = 1`). The paper's phrasing with ordinals is
the Mazurkiewicz–Sierpiński classification of the latter, which is not formalised.

One-dimensionality of both continua matters in "⇒" (Brazas–Fischer Thm 9.15): `Peano.Remark6_5`
shows that the earring `𝔼` and `𝔼 × I` are homotopy equivalent while `w(𝔼)` is a point and
`w(𝔼 × I)` is uncountable (Remark 6.5 of the paper).

Design: "homotopy types" and "homeomorphism types" are not formed as quotient types; the bijection
is stated as the two properties above.
-/

@[expose] public section

open Set Topology

namespace Peano

/-- **Theorem 1.2, injectivity and well-definedness.** One-dimensional Peano continua with
non-empty countable wild sets are homotopy equivalent iff their wild sets are homeomorphic.
"⇒" is Brazas–Fischer Thm 9.15; "⇐" is Eda's Theorem 6.6 (countable compact metric spaces are
zero-dimensional). -/
theorem nonempty_homotopyEquiv_iff (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (hXc : (wildSet X).Countable) (hXne : (wildSet X).Nonempty)
    (hYc : (wildSet Y).Countable) (hYne : (wildSet Y).Nonempty) :
    Nonempty (ContinuousMap.HomotopyEquiv X Y) ↔ Nonempty (wildSet X ≃ₜ wildSet Y) := by
  refine ⟨fun ⟨e⟩ => nonempty_homeomorph_wildSet X Y hX hY e, fun ⟨φ⟩ => ?_⟩
  rw [wildSet_eq_loopWildSet] at hXc hXne φ
  rw [wildSet_eq_loopWildSet] at hYc hYne φ
  exact eda_homotopyEquiv_of_homeomorph X Y hX hY hXne hYne hXc.zeroDimensionalSpace
    hYc.zeroDimensionalSpace φ

/-- **Theorem 1.2, surjectivity.** Every non-empty countable compact metric space `K` is
homeomorphic to the wild set of a one-dimensional Peano continuum (whose wild set is then
non-empty and countable, so by Theorem 1.1 it has a countable weak model). -/
theorem exists_wildSet_homeomorph (K : Type) [MetricSpace K] [CompactSpace K] [Countable K]
    [Nonempty K] :
    ∃ (X : Type) (_ : MetricSpace X), CompactSpace X ∧ ConnectedSpace X ∧
      LocallyPathConnectedSpace X ∧ CoveringDimLE 1 X ∧ Nonempty (wildSet X ≃ₜ K) := by
  obtain ⟨A, hAc, -, hconn, hlpc, hdim, ι, hι, hsub, hsub'⟩ := exists_model K
  have hA : CompactSpace A := isCompact_iff_compactSpace.1 hAc
  have heq : wildSet A = range ι :=
    subset_antisymm ((wildSet_subset_loopWildSet A).trans hsub') hsub
  exact ⟨A, inferInstance, hA, hconn, hlpc, hdim,
    ⟨(Homeomorph.setCongr heq).trans hι.toHomeomorph.symm⟩⟩

/-- The wild set of a compact metric locally path-connected space is compact (it is closed,
Lemma 2.3); so for the continua of Theorem 1.2 it is a non-empty countable compact metric space. -/
theorem compactSpace_wildSet (X : Type*) [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] : CompactSpace (wildSet X) :=
  isCompact_iff_compactSpace.1 (isClosed_wildSet X).isCompact

/-- **Theorem 1.2** for the class of the paper: one-dimensional Peano continua that admit a weak
homotopy equivalence to a countable space and have non-empty wild set are homotopy equivalent iff
their wild sets are homeomorphic. -/
theorem nonempty_homotopyEquiv_iff_of_weq (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y)
    (hXm : ∃ (Z : Type) (_ : TopologicalSpace Z), Countable Z ∧
      ∃ f : C(X, Z), IsWeakHomotopyEquivalence f) (hXne : (wildSet X).Nonempty)
    (hYm : ∃ (Z : Type) (_ : TopologicalSpace Z), Countable Z ∧
      ∃ f : C(Y, Z), IsWeakHomotopyEquivalence f) (hYne : (wildSet Y).Nonempty) :
    Nonempty (ContinuousMap.HomotopyEquiv X Y) ↔ Nonempty (wildSet X ≃ₜ wildSet Y) :=
  nonempty_homotopyEquiv_iff X Y hX hY ((exists_countable_weq_iff X hX).1 hXm) hXne
    ((exists_countable_weq_iff Y hY).1 hYm) hYne

end Peano
