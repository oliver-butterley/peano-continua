module

public import Peano.StandardForm
public import Peano.Coarsify
public import Peano.WeakEquiv
public import Peano.Axioms.Cited
public import Peano.Axioms.Standard

/-!
# Theorem 1.1, "if" direction

Brazas–Pavešić, Corollary 5.6 and the "if" half of Theorem 1.1, in two layers.

* `ArcSystem.isWeakHomotopyEquivalence_q` (Corollary 5.6): the coarsification map of an arc system
  is a Serre fibration and a weak homotopy equivalence (Lemma 5.5 on cubes plus
  `Peano.WeakEquiv`). No axioms beyond the standard three.
* `exists_countable_weq_of_standardForm`: a one-dimensional Peano continuum in standard form with
  countable wild set is weakly homotopy equivalent to a countable space. Uses the cited Lemma 2.3
  (`isClosed_wildSet`) only, to build the arc system with `W = w(X)`.
* `exists_countable_weq`: the general case. Uses Meilstrup's Theorem 4.2, Brazas–Fischer
  Thm 9.15 (to keep `w` countable, in place of the paper's Lemma 6.4) and the standard fact that
  homotopy equivalences are weak equivalences.

The "only if" direction (Lemma 6.4 and Part A) and Theorem 1.2 are not formalised; see
`notes/lean-map.md`.
-/

@[expose] public section

open Set Topology unitInterval

noncomputable section

namespace Peano

namespace ArcSystem

variable {X : Type*} [MetricSpace X] [CompactSpace X] [LocallyPathConnectedSpace X]
  (S : ArcSystem X)

/-- Lemma 5.5 applied to cubes. -/
theorem hasCubeLifting_q : HasCubeLifting S.q :=
  fun _ _ hA f g hfg => S.exists_lift S.tendsto_diam_closedArc hA f g hfg

/-- **Corollary 5.6** (first half). The coarsification map is a Serre fibration. -/
theorem isSerreFibration_q : IsSerreFibration S.q :=
  isSerreFibration_of_hasCubeLifting S.hasCubeLifting_q

/-- **Corollary 5.6** (second half). The coarsification map is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_q : IsWeakHomotopyEquivalence S.q :=
  isWeakHomotopyEquivalence_of_hasCubeLifting S.hasCubeLifting_q

end ArcSystem

/-- A standard-form continuum gives an arc system whose closed set is the wild set (uses the
cited Lemma 2.3 for closedness, so that the relatively open arcs are open in `X`). -/
theorem IsStandardForm.exists_arcSystem {X : Type*} [MetricSpace X] [LocallyPathConnectedSpace X]
    (hX : IsStandardForm X) : ∃ S : ArcSystem X, S.W = wildSet X := by
  obtain ⟨ι, h, hinj, hmem, hdisj, hU, hopen⟩ := hX
  have hWc : IsOpen (wildSet X)ᶜ := (isClosed_wildSet X).isOpen_compl
  refine ⟨⟨wildSet X, isClosed_wildSet X, ι, h, hinj, hmem, hdisj, hU, fun i => ?_⟩, rfl⟩
  have hsub : h i '' openUnit ⊆ (wildSet X)ᶜ := hU ▸ subset_iUnion (fun j => h j '' openUnit) i
  have := hWc.isOpenMap_subtype_val _ (hopen i)
  rwa [Subtype.image_preimage_coe, inter_eq_right.2 hsub] at this

/-- **Theorem 1.1, "if" direction, standard form.** A one-dimensional Peano continuum in standard
form with countable wild set admits a weak homotopy equivalence to a countable space (namely its
coarsification). -/
theorem exists_countable_weq_of_standardForm (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X)
    (hsf : IsStandardForm X) (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f := by
  obtain ⟨S, hS⟩ := hsf.exists_arcSystem
  exact ⟨S.Coarse, inferInstance, S.countable_coarse (hS ▸ hw), S.q,
    S.isWeakHomotopyEquivalence_q⟩

/-- **Theorem 1.1, "if" direction**, for non-empty wild set. A one-dimensional Peano continuum
with countable non-empty wild set admits a weak homotopy equivalence to a countable space.

The case `w(X) = ∅` is excluded: the paper's proof goes through Theorem 4.2, which fails there
(see `exists_homotopyEquiv_standardForm`); that case needs a separate argument (such an `X` is
homotopy equivalent to a finite graph, which has a finite model by McCord) and is not
formalised. -/
theorem exists_countable_weq (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) (hne : (wildSet X).Nonempty)
    (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f := by
  obtain ⟨X', _, hc, hconn, hlpc, hdim', hsf, ⟨e⟩⟩ := exists_homotopyEquiv_standardForm X hdim hne
  obtain ⟨φ⟩ := nonempty_homeomorph_wildSet X X' hdim hdim' e
  have hw' : (wildSet X').Countable := by
    have : Countable (wildSet X) := hw.to_subtype
    have : Countable (wildSet X') := φ.symm.injective.countable
    exact Set.countable_coe_iff.1 this
  obtain ⟨Y, _, hY, f', hf'⟩ := exists_countable_weq_of_standardForm X' hdim' hsf hw'
  exact ⟨Y, inferInstance, hY, f'.comp e.toFun,
    hf'.comp (HomotopyEquiv.isWeakHomotopyEquivalence e)⟩

end Peano
