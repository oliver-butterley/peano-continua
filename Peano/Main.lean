module

public import Peano.StandardForm
public import Peano.Coarsify
public import Peano.WeakEquiv
public import Peano.Axioms.Cited
public import Peano.HomotopyEquiv
public import Peano.WildSet
public import Peano.OnlyIf

/-!
# Corollary 5.6 and Theorem 1.1, "if" direction

Brazas–Pavešić (arXiv:2610.35875), Corollary 5.6 and the "if" half of Theorem 1.1, in three
layers.

* `ArcSystem.isWeakHomotopyEquivalence_q` (Corollary 5.6): the coarsification map of an arc system
  is a Serre fibration and a weak homotopy equivalence (Lemma 5.5 on cubes plus
  `Peano.WeakEquiv`). No axioms beyond the standard three. `ArcSystem.countable_weq_q` is the
  same without the paper's standing hypotheses.
* `exists_countable_weq_of_standardForm`: a one-dimensional Peano continuum in standard form with
  countable wild set is weakly homotopy equivalent to a countable space (its coarsification). No
  cited axioms: closedness of `w(X)` (Lemma 2.3) is proved (`isClosed_wildSet`, `Peano.WildSet`)
  and gives the arc system with `W = w(X)`.
* `exists_countable_weq`: the general case. If `w(X) ≠ ∅`: Meilstrup's Theorem 4.2 (cited axiom
  `exists_homotopyEquiv_standardForm`) gives a homotopy equivalent `X'` in standard form; the
  homotopy inverse `X' → X` is a weak homotopy equivalence
  (`HomotopyEquiv.isWeakHomotopyEquivalence`, proved in `Peano.HomotopyEquiv`), so Lemmas 2.5
  and 6.4 (`mapsTo_wildSet`, `injOn_wildSet`, `Peano.OnlyIf`) keep `w(X')` countable, exactly as in the paper. If `w(X) = ∅` (a case the
  paper's proof overlooks: Theorem 4.2 does not apply), `X` is homotopy equivalent to a finite
  graph (cited axiom `exists_homotopyEquiv_finiteGraph`), whose coarsification is a finite model.

The "only if" direction is `countable_wildSet_of_weq` in `Peano.OnlyIf`, and the equivalence is
`exists_countable_weq_iff` in `Peano.Thm1_1`. Brazas–Fischer Theorem 9.15, used for Theorem 1.2,
is proved in `Peano.BrazasFischer`.
See `notes/lean-map.md`.
-/

@[expose] public section

open Set Topology unitInterval

noncomputable section

namespace Peano

namespace ArcSystem

section General

variable {X : Type*} [MetricSpace X] (S : ArcSystem X)

/-- Lemma 5.5 applied to cubes, for an arc system with null arcs (no compactness needed). -/
theorem hasCubeLifting_q_of_null
    (hnull : Filter.Tendsto (fun i => Metric.diam (S.closedArc i)) Filter.cofinite (𝓝 0)) :
    HasCubeLifting S.q :=
  fun _ _ hA f g hfg => S.exists_lift hnull hA f g hfg

/-- Finitely many arcs are null: the cofinite filter on a finite type is `⊥`. -/
theorem tendsto_diam_closedArc_of_finite [Finite S.ι] :
    Filter.Tendsto (fun i => Metric.diam (S.closedArc i)) Filter.cofinite (𝓝 0) := by
  rw [Filter.cofinite_eq_bot]
  exact Filter.tendsto_bot

/-- **Countable model of an arc system.** For an arc system with null arcs on a separable metric
space whose closed set `W` is countable, the coarsification is a countable space and `q` is a weak
homotopy equivalence. This is the content of Remark 5.1 and Corollary 5.6 without the paper's
standing hypotheses (one-dimensionality, connectedness, compactness), which the proofs do not use;
for a compact locally path-connected space the null hypothesis is Lemma 4.3. -/
theorem countable_weq_q [TopologicalSpace.SeparableSpace X]
    (hnull : Filter.Tendsto (fun i => Metric.diam (S.closedArc i)) Filter.cofinite (𝓝 0))
    (hW : S.W.Countable) : Countable S.Coarse ∧ IsWeakHomotopyEquivalence S.q :=
  ⟨S.countable_coarse hW,
    isWeakHomotopyEquivalence_of_hasCubeLifting (S.hasCubeLifting_q_of_null hnull)⟩

end General

variable {X : Type*} [MetricSpace X] [CompactSpace X] [LocallyPathConnectedSpace X]
  (S : ArcSystem X)

/-- Lemma 5.5 applied to cubes. -/
theorem hasCubeLifting_q : HasCubeLifting S.q :=
  S.hasCubeLifting_q_of_null S.tendsto_diam_closedArc

/-- **Corollary 5.6** (first half). The coarsification map is a Serre fibration. -/
theorem isSerreFibration_q : IsSerreFibration S.q :=
  isSerreFibration_of_hasCubeLifting S.hasCubeLifting_q

/-- **Corollary 5.6** (second half). The coarsification map is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_q : IsWeakHomotopyEquivalence S.q :=
  isWeakHomotopyEquivalence_of_hasCubeLifting S.hasCubeLifting_q

end ArcSystem

/-- A standard-form continuum gives an arc system whose closed set is the wild set (uses the
Lemma 2.3, `isClosed_wildSet`, for closedness, so that the relatively open arcs are open in `X`). -/
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
coarsification).

The one-dimensionality hypothesis `_hdim` is not used by the proof (the arc system and its
coarsification need only a compact, locally path-connected metric space in standard form, see
`ArcSystem.countable_weq_q`). It is kept so that the statement is the paper's (the standard-form
case of Theorem 1.1, for one-dimensional Peano continua) and matches the frozen restatement in
`Peano/Audit/Thm1_1.lean`. -/
theorem exists_countable_weq_of_standardForm (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (_hdim : CoveringDimLE 1 X)
    (hsf : IsStandardForm X) (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f := by
  obtain ⟨S, hS⟩ := hsf.exists_arcSystem
  exact ⟨S.Coarse, inferInstance, S.countable_coarse (hS ▸ hw), S.q,
    S.isWeakHomotopyEquivalence_q⟩

/-- A finite graph (a compact metric space with an arc system with finitely many arcs and finite
`W`) is weakly homotopy equivalent to a finite space, its coarsification. This replaces McCord's
theorem in the case `w(X) = ∅` of Theorem 1.1: the coarsification of §5 already handles it. -/
theorem ArcSystem.finite_weq_q_of_finite {X : Type*} [MetricSpace X] [CompactSpace X]
    (S : ArcSystem X) [Finite S.ι] (hW : S.W.Finite) :
    Finite S.Coarse ∧ IsWeakHomotopyEquivalence S.q :=
  ⟨S.finite_coarse hW,
    (S.countable_weq_q S.tendsto_diam_closedArc_of_finite hW.countable).2⟩

/-- **Theorem 1.1, "if" direction, case `w(X) = ∅`** (missed by the paper), with the wild set
taken in the loop sense of the cited source (`loopWildSet`). Such a continuum is weakly homotopy
equivalent to a *finite* space. Uses the cited finite-graph theorem
(`exists_homotopyEquiv_finiteGraph`). -/
theorem exists_finite_weq_of_loopWildSet_eq_empty (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X)
    (hw : loopWildSet X = ∅) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Finite Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f := by
  obtain ⟨X', _, S, _, hW, hι, ⟨e⟩⟩ := exists_homotopyEquiv_finiteGraph X hdim hw
  obtain ⟨hfin, hq⟩ := S.finite_weq_q_of_finite hW
  exact ⟨S.Coarse, inferInstance, hfin, S.q.comp e.toFun,
    hq.comp (HomotopyEquiv.isWeakHomotopyEquivalence e)⟩

/-- **Theorem 1.1, "if" direction.** A one-dimensional Peano continuum with countable wild set
admits a weak homotopy equivalence to a countable space.

Two cases. If `w(X) ≠ ∅`, the paper's proof: Meilstrup's standard form `X'` (Theorem 4.2); the
homotopy inverse `X' → X` maps `w(X')` injectively into `w(X)` (Lemmas 2.5 and 6.4), so `w(X')`
is countable; then the coarsification of `X'` (Corollary 5.6). If `w(X) = ∅` (missed by the
paper), `X` is homotopy equivalent to a finite graph and the coarsification of that graph is a
finite model. -/
theorem exists_countable_weq (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X) (hw : (wildSet X).Countable) :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
      ∃ f : C(X, Y), IsWeakHomotopyEquivalence f := by
  rcases (wildSet X).eq_empty_or_nonempty with hne | hne
  · rw [wildSet_eq_loopWildSet] at hne
    obtain ⟨Y, _, hY, f, hf⟩ := exists_finite_weq_of_loopWildSet_eq_empty X hdim hne
    exact ⟨Y, inferInstance, Finite.to_countable, f, hf⟩
  obtain ⟨X', _, hc, hconn, hlpc, hdim', hsf, ⟨e⟩⟩ := exists_homotopyEquiv_standardForm X hdim hne
  have hinv := (HomotopyEquiv.isWeakHomotopyEquivalence e.symm).fundamentalGroup_map_bijective
  have hw' : (wildSet X').Countable :=
    (mapsTo_wildSet fun x => (hinv x).1).countable_of_injOn (injOn_wildSet X' hdim' hinv) hw
  obtain ⟨Y, _, hY, f', hf'⟩ := exists_countable_weq_of_standardForm X' hdim' hsf hw'
  exact ⟨Y, inferInstance, hY, f'.comp e.toFun,
    hf'.comp (HomotopyEquiv.isWeakHomotopyEquivalence e)⟩

end Peano
