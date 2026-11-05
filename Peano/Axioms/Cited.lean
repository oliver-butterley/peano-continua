module

public import Peano.Defs

/-!
# Results cited by Brazas–Pavešić, assumed as axioms

The trust boundary of the formalisation, part 1 of 2 (part 2: `Peano.Axioms.Standard`). Each
axiom is a theorem from the literature that the paper quotes without proof; its docstring gives
the statement in words, the exact reference, and the paper's use. Audit table: `notes/axioms.md`;
adversarial review: `notes/checks/axioms-review.md`. `#print axioms` on any theorem shows which of
these it uses (`Peano/Audit/`).

Every axiom is stated no more strongly than its source (where a weaker form suffices, the weaker
form is taken), and only for the spaces the paper applies it to.
-/

@[expose] public section

open Topology

namespace Peano

/-- **Lemma 2.3** of the paper, from Brazas–Mitra, *Higher homotopy wild sets*, arXiv:2505.23665,
Prop. 2.9 (case `n = 1`): in a locally path-connected first-countable space the wild set is
closed. Taken here only for metric spaces (which are first countable). Used to see that a
standard-form continuum gives an `ArcSystem`. -/
axiom isClosed_wildSet (X : Type*) [MetricSpace X] [LocallyPathConnectedSpace X] :
    IsClosed (wildSet X)

/-- **Theorem 4.2** of the paper, from Meilstrup, *Classifying homotopy types of one-dimensional
Peano continua*, Master's thesis, Brigham Young University, 2005: every one-dimensional Peano
continuum is homotopy equivalent to a one-dimensional Peano continuum in standard form.

**Hypothesis `(wildSet X).Nonempty` added** (not in the paper's statement): with Definition 4.1 a
non-empty standard-form space has non-empty wild set (an arc's end points lie in `w`), and
homotopy equivalences preserve emptiness of `w`, so the theorem as quoted is false for, e.g., a
point; without this hypothesis the axiom would be inconsistent. Found by the Part B check
(`notes/checks/B.md`). -/
axiom exists_homotopyEquiv_standardForm (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X)
    (hw : (wildSet X).Nonempty) :
    ∃ (X' : Type) (_ : MetricSpace X'), CompactSpace X' ∧ ConnectedSpace X' ∧
      LocallyPathConnectedSpace X' ∧ CoveringDimLE 1 X' ∧ IsStandardForm X' ∧
      Nonempty (ContinuousMap.HomotopyEquiv X X')

/-- From Brazas–Fischer, *On the failure of the first Čech homotopy group to register
geometrically relevant fundamental group elements*, Bull. London Math. Soc. 52 (2020), Thm 9.15,
quoted in the paper's proof of Theorem 1.2: a homotopy equivalence of one-dimensional Peano
continua restricts to a homeomorphism of wild sets. Only the existence of a homeomorphism of the
wild sets is assumed. Used in place of the paper's Lemma 6.4 to keep `w(X)` countable when
passing to standard form (the paper's own route there needs Part A, which is not formalised). -/
axiom nonempty_homeomorph_wildSet (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (e : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (wildSet X ≃ₜ wildSet Y)

end Peano
