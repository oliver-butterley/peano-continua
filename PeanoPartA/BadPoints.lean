module

public import PeanoPartA.Lemmas

/-!
# Meilstrup's bad points are the wild set

Meilstrup, *Classifying homotopy types of one-dimensional Peano continua* (Master's thesis, BYU,
2005), §1.1: "all neighborhoods will be open […]. In a one-dimensional Peano continuum `X`, a point
`x` is *bad* if it has no simply connected neighborhood. We denote the set of all bad points of `X`
by `B(X)`". Here `badSet X` encodes this literally: no open set `U ∋ x` that is simply connected in
the subspace topology (Mathlib's `IsSimplyConnected U`, i.e. `SimplyConnectedSpace U`: non-empty,
path-connected, trivial fundamental group).

Main result (`badSet_eq_loopWildSet`, `badSet_eq_wildSet`): for a one-dimensional metric space
which is locally path-connected (in particular for a one-dimensional Peano continuum),
`B(X) = loopWildSet X = wildSet X`.

* `loopWildSet X ⊆ badSet X` (`loopWildSet_subset_badSet`, any topological space): a loop at `x`
  inside a simply connected open `U ∋ x` is null-homotopic in `U`, hence in `X`.
* `badSet X ⊆ loopWildSet X` (`badSet_subset_loopWildSet`): if every loop at `x` inside a
  neighbourhood `U` is null-homotopic in `X`, take a path-connected open `V ∋ x` inside `U`
  (local path-connectedness). A loop `δ` in `V` at any `y ∈ V` is conjugate in `V`, by a path `p`
  in `V` from `x` to `y`, to the loop `p δ p⁻¹` at `x` in `V ⊆ U`, which is null in `X`, hence
  null in `V` by Lemma 2.8 of Brazas–Pavešić (`fundamentalGroup_map_val_injective`). So `δ` is null
  in `V` and `V` is simply connected.

**Use.** This justifies stating the cited structure axiom
`Peano.exists_homotopyEquiv_arcReduced` (Meilstrup's Theorem 2.9 and Corollary 2.10, which are
stated with `B(X)`) with `loopWildSet` in the hypothesis and `wildSet` in the conclusion
(`IsStandardForm`).

**Why in `PeanoPartA`.** Lemma 2.8 is proved from the cited Cannon–Conner axioms
(`PeanoPartA.Axioms`). Keeping this file out of the main library `Peano` means Theorem 1.1 does
not inherit those axioms; the identification `B = loopWildSet` is only needed to check the
statement of the structure axiom against the thesis, not by any proof.
-/

@[expose] public section

open Set Topology

namespace Peano

/-- Meilstrup's **bad points** `B(X)`: the points with no simply connected (open) neighbourhood. -/
def badSet (X : Type*) [TopologicalSpace X] : Set X :=
  {x | ¬ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsSimplyConnected U}

/-- A point is good (not bad) iff it has a simply connected open neighbourhood. -/
theorem notMem_badSet_iff {X : Type*} [TopologicalSpace X] {x : X} :
    x ∉ badSet X ↔ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsSimplyConnected U := by
  simp [badSet]

/-- Points with arbitrarily small essential loops are bad: a loop inside a simply connected open
neighbourhood is null-homotopic there, hence in `X`. -/
theorem loopWildSet_subset_badSet (X : Type*) [TopologicalSpace X] :
    loopWildSet X ⊆ badSet X := by
  rintro x hx ⟨U, hU, hxU, hsc⟩
  have := hsc.simplyConnectedSpace
  obtain ⟨γ, hγU, hγ⟩ := hx U (hU.mem_nhds hxU)
  have hmem : ∀ t, γ t ∈ U := fun t => hγU ⟨t, rfl⟩
  have h1 : (pathIn γ U hmem).Homotopic (Path.refl _) := SimplyConnectedSpace.paths_homotopic _ _
  exact hγ (h1.map ⟨Subtype.val, continuous_subtype_val⟩)

open Path.Homotopic.Quotient in
/-- In a one-dimensional, locally path-connected metric space, bad points have arbitrarily small
essential loops. Uses Lemma 2.8 (`fundamentalGroup_map_val_injective`). -/
theorem badSet_subset_loopWildSet (X : Type) [MetricSpace X] [LocallyPathConnectedSpace X]
    (hX : CoveringDimLE 1 X) : badSet X ⊆ loopWildSet X := by
  intro x hx
  by_contra hw
  simp only [loopWildSet, mem_ofPred_eq] at hw
  push Not at hw
  obtain ⟨U, hU, hnull⟩ := hw
  obtain ⟨V, ⟨hVo, hxV, hVpc⟩, hVU⟩ := (isOpen_isPathConnected_basis x).mem_iff.1 hU
  refine hx ⟨V, hVo, hxV, ?_⟩
  change SimplyConnectedSpace V
  have : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.1 hVpc
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun y δ => ?_⟩
  let p : Path (⟨x, hxV⟩ : V) y := PathConnectedSpace.somePath _ _
  let γ : Path (⟨x, hxV⟩ : V) ⟨x, hxV⟩ := (p.trans δ).trans p.symm
  have hγX : (γ.map continuous_subtype_val).Homotopic (Path.refl x) := by
    refine hnull _ ?_
    rintro _ ⟨t, rfl⟩
    exact hVU (γ t).2
  have hγ : γ.Homotopic (Path.refl _) :=
    homotopic_of_map_val_homotopic X hX V hγX
  -- conjugation by `p` in the fundamental groupoid of `V`
  rw [← Path.Homotopic.Quotient.eq]
  have h : ((mk p).trans (mk δ)).trans (mk p).symm = Path.Homotopic.Quotient.refl _ := by
    simpa [γ] using (Path.Homotopic.Quotient.eq.2 hγ)
  calc mk δ = (mk p).symm.trans ((((mk p).trans (mk δ)).trans (mk p).symm).trans (mk p)) := by
        rw [trans_assoc, symm_trans, trans_refl, ← trans_assoc, symm_trans, refl_trans]
    _ = mk (Path.refl y) := by
        rw [h]
        simp

/-- **Bad points are loop-wild points.** For a one-dimensional, locally path-connected metric
space (e.g. a one-dimensional Peano continuum), Meilstrup's `B(X)` is `loopWildSet X`. -/
theorem badSet_eq_loopWildSet (X : Type) [MetricSpace X] [LocallyPathConnectedSpace X]
    (hX : CoveringDimLE 1 X) : badSet X = loopWildSet X :=
  (badSet_subset_loopWildSet X hX).antisymm (loopWildSet_subset_badSet X)

/-- **Bad points are wild points.** For a one-dimensional, locally path-connected metric space,
Meilstrup's `B(X)` is the paper's wild set `w(X)` (Definition 2.2). -/
theorem badSet_eq_wildSet (X : Type) [MetricSpace X] [LocallyPathConnectedSpace X]
    (hX : CoveringDimLE 1 X) : badSet X = wildSet X := by
  rw [badSet_eq_loopWildSet X hX, wildSet_eq_loopWildSet]

end Peano
