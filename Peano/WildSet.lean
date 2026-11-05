module

public import Peano.Earring
public import Peano.HomotopyEquiv
public import Peano.LoopWildSet

/-!
# The wild set: loops versus earrings, closedness, π₁-injective maps

Basic properties of the wild set `w(X)` of Brazas–Pavešić (arXiv:2610.35875), §2.

* **Two definitions agree** (the remark after Definition 2.2). `wildSet X` (Definition 2.2: the
  base points of fully essential maps `𝔼 → X` from the infinite earring) is contained in
  `loopWildSet X` (every neighbourhood of `x` contains an essential loop at `x`) for every space:
  the loops `f ∘ ℓₖ` of a map `f` from the earring shrink into every neighbourhood of `f b₀`
  (`wildSet_subset_loopWildSet`). For first-countable `X` the converse holds: choose a decreasing
  countable neighbourhood basis `uₖ` of `x`, an essential loop `γₖ` at `x` inside `uₖ`, and glue the
  `γₖ` to a map `𝔼 → X` with the gluing lemma `earringMap` (`loopWildSet_subset_wildSet`,
  `wildSet_eq_loopWildSet`).
* **Lemma 2.3** (cited by the paper from Brazas–Mitra, arXiv:2505.23665, Prop. 2.9). In a locally
  path-connected space `loopWildSet X` is closed (`isClosed_loopWildSet`): if `x` lies in the
  closure, inside a path-connected neighbourhood `V ⊆ U` of `x` there is a point `x'` of the loop
  wild set with `V` a neighbourhood of `x'`, hence an essential loop `δ` at `x'` in `V`; the
  conjugate `p · δ · p⁻¹` by a path `p` in `V` from `x` to `x'` is an essential loop at `x` in `U`.
  Hence `wildSet X` is closed for first-countable locally path-connected `X`
  (`isClosed_wildSet_of_firstCountableTopology`), in particular for metric ones
  (`isClosed_wildSet`, the form used downstream; it was first assumed as an axiom).
* **Lemma 2.5.** A π₁-injective map `f : X → Y` (injective on every `FundamentalGroup X x`) sends
  `w(X)` into `w(Y)` (`image_wildSet_subset`), and likewise for the loop wild sets
  (`image_loopWildSet_subset`).
* Reusable facts: a conjugate of an essential loop is essential
  (`not_homotopic_refl_conj`); a point with a neighbourhood in which every loop is null-homotopic
  in `X`, e.g. a simply connected neighbourhood, is not in the loop wild set
  (`notMem_loopWildSet_of_forall`, `notMem_loopWildSet_of_simplyConnected`).

## Design

Essentiality of a loop is `¬ γ.Homotopic (Path.refl x)`, as in `FullyEssential` and `loopWildSet`.
Path algebra (conjugation) is done in `Path.Homotopic.Quotient`, whose groupoid laws are `simp`
lemmas in Mathlib. The π₁-injectivity hypothesis of Lemma 2.5 is phrased with Mathlib's
`FundamentalGroup.map` and is used through `Peano.homotopic_of_map_homotopic`. No separation axiom
is assumed anywhere; first countability is used only for the inclusion `loopWildSet ⊆ wildSet`.
-/

@[expose] public section

open Set Filter Topology

namespace Peano

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Essential loops -/

/-- A conjugate `p · γ · p⁻¹` of an essential loop `γ` at `x'`, by a path `p` from `x` to `x'`, is
an essential loop at `x`. -/
theorem not_homotopic_refl_conj {x x' : X} (p : Path x x') {γ : Path x' x'}
    (hγ : ¬ γ.Homotopic (Path.refl x')) :
    ¬ ((p.trans γ).trans p.symm).Homotopic (Path.refl x) := by
  intro h
  apply hγ
  rw [← Path.Homotopic.Quotient.eq] at h ⊢
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_refl] at h
  rw [Path.Homotopic.Quotient.mk_refl]
  set P := Path.Homotopic.Quotient.mk p
  set G := Path.Homotopic.Quotient.mk γ
  calc G = ((P.symm.trans ((P.trans G).trans P.symm)).trans P) := by
        simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
          Path.Homotopic.Quotient.trans_refl]
        rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
          Path.Homotopic.Quotient.refl_trans]
    _ = _ := by rw [h]; simp

/-- The image of a loop under a map whose induced map on `π₁` is injective at the base point is
essential if the loop is. -/
theorem not_homotopic_refl_map_of_injective {f : C(X, Y)} {x : X}
    (hf : Function.Injective (FundamentalGroup.map f x)) {γ : Path x x}
    (hγ : ¬ γ.Homotopic (Path.refl x)) :
    ¬ (γ.map f.continuous).Homotopic (Path.refl (f x)) := by
  intro h
  apply hγ
  have hr : (Path.refl x).map f.continuous = Path.refl (f x) := by ext; rfl
  exact homotopic_of_map_homotopic hf (by rwa [hr])

/-! ### The loop wild set -/

/-- If every loop at `x` with image in some neighbourhood `U` of `x` is null-homotopic in `X`,
then `x` is not in the loop wild set. -/
theorem notMem_loopWildSet_of_forall {x : X} {U : Set X} (hU : U ∈ 𝓝 x)
    (h : ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x)) : x ∉ loopWildSet X :=
  fun hx => by
    obtain ⟨γ, hγU, hγ⟩ := hx U hU
    exact hγ (h γ hγU)

/-- A point with a simply connected neighbourhood is not in the loop wild set. -/
theorem notMem_loopWildSet_of_simplyConnected {x : X} {U : Set X} (hU : U ∈ 𝓝 x)
    [SimplyConnectedSpace U] : x ∉ loopWildSet X := by
  refine notMem_loopWildSet_of_forall hU fun γ hγU => ?_
  have hx : x ∈ U := mem_of_mem_nhds hU
  let γ' : Path (⟨x, hx⟩ : U) ⟨x, hx⟩ :=
    { toFun := fun t => ⟨γ t, hγU ⟨t, rfl⟩⟩
      continuous_toFun := by fun_prop
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have h1 : γ'.map continuous_subtype_val = γ := by ext; rfl
  have h2 : (Path.refl (⟨x, hx⟩ : U)).map continuous_subtype_val = Path.refl x := by ext; rfl
  rw [← h1, ← h2]
  exact (SimplyConnectedSpace.paths_homotopic γ' (Path.refl _)).map
    ⟨Subtype.val, continuous_subtype_val⟩

/-! ### Wild set versus loop wild set -/

variable (X) in
/-- The base point of a fully essential map is a loop wild point: the essential loops `f ∘ ℓₖ`
shrink into every neighbourhood of `f b₀`. -/
theorem wildSet_subset_loopWildSet : wildSet X ⊆ loopWildSet X := by
  rintro _ ⟨f, rfl, hf⟩ U hU
  obtain ⟨k, hk⟩ := (loopsShrinkTo_map_earringLoop f U hU).exists
  exact ⟨(earringLoop k).map f.continuous, hk, hf k⟩

variable (X) in
/-- In a first-countable space every loop wild point is a wild point: essential loops in the
members of a decreasing countable neighbourhood basis glue to a fully essential map. -/
theorem loopWildSet_subset_wildSet [FirstCountableTopology X] : loopWildSet X ⊆ wildSet X := by
  intro x hx
  obtain ⟨u, hu⟩ := (𝓝 x).exists_antitone_basis
  choose γ hγu hγ using fun k => hx (u k) (hu.mem k)
  have hshrink : LoopsShrinkTo x γ := fun U hU =>
    (hu.eventually_subset hU).mono fun k hk => (hγu k).trans hk
  refine ⟨earringMap x γ hshrink, earringMap_base hshrink, fun k => ?_⟩
  rw [earringLoop_map_earringMap, cast_homotopic_refl_iff]
  exact hγ k

variable (X) in
/-- The remark after Definition 2.2: for first-countable spaces the wild set (through fully
essential maps from the earring) is the loop wild set (through small essential loops). -/
theorem wildSet_eq_loopWildSet [FirstCountableTopology X] : wildSet X = loopWildSet X :=
  (wildSet_subset_loopWildSet X).antisymm (loopWildSet_subset_wildSet X)

/-! ### Lemma 2.3: the wild set is closed -/

variable (X) in
/-- **Lemma 2.3**, loop version: in a locally path-connected space the loop wild set is
closed. -/
theorem isClosed_loopWildSet [LocallyPathConnectedSpace X] : IsClosed (loopWildSet X) := by
  refine isClosed_of_closure_subset fun x hx U hU => ?_
  obtain ⟨V, ⟨hV, hVpc⟩, hVU⟩ := (path_connected_basis x).mem_iff.1 hU
  obtain ⟨x', hx'V, hx'⟩ := mem_closure_iff_nhds.1 hx (interior V) (interior_mem_nhds.2 hV)
  have hVx' : V ∈ 𝓝 x' := mem_of_superset (isOpen_interior.mem_nhds hx'V) interior_subset
  obtain ⟨δ, hδV, hδ⟩ := hx' V hVx'
  have hj : JoinedIn V x x' := hVpc.joinedIn x (mem_of_mem_nhds hV) x' (interior_subset hx'V)
  refine ⟨(hj.somePath.trans δ).trans hj.somePath.symm, ?_, not_homotopic_refl_conj _ hδ⟩
  have hp : range hj.somePath ⊆ V := by
    rintro _ ⟨t, rfl⟩
    exact hj.somePath_mem t
  rw [Path.trans_range, Path.trans_range, Path.symm_range]
  exact union_subset (union_subset hp hδV) hp |>.trans hVU

variable (X) in
/-- **Lemma 2.3**: in a first-countable locally path-connected space the wild set is closed. -/
theorem isClosed_wildSet_of_firstCountableTopology [FirstCountableTopology X]
    [LocallyPathConnectedSpace X] : IsClosed (wildSet X) := by
  rw [wildSet_eq_loopWildSet]
  exact isClosed_loopWildSet X

/-- **Lemma 2.3** for metric spaces: in a locally path-connected metric space the wild set is
closed. This is the form used downstream and restated in `Peano/Audit/WildSet.lean`; the general
statement is `isClosed_wildSet_of_firstCountableTopology` (first-countable locally path-connected
spaces), and `isClosed_loopWildSet` is the version for the loop wild set, which needs no
countability.
(History: this statement was first assumed, under the same name, as an axiom citing
Brazas–Mitra; it is now proved.) -/
theorem isClosed_wildSet (X : Type*) [MetricSpace X] [LocallyPathConnectedSpace X] :
    IsClosed (wildSet X) :=
  isClosed_wildSet_of_firstCountableTopology X

/-! ### Lemma 2.5: π₁-injective maps preserve wild points -/

/-- **Lemma 2.5**: a π₁-injective map sends wild points to wild points. -/
theorem image_wildSet_subset {f : C(X, Y)}
    (hf : ∀ x, Function.Injective (FundamentalGroup.map f x)) : f '' wildSet X ⊆ wildSet Y := by
  rintro _ ⟨_, ⟨g, rfl, hg⟩, rfl⟩
  refine ⟨f.comp g, rfl, fun k => ?_⟩
  exact not_homotopic_refl_map_of_injective (hf _) (hg k) (γ := (earringLoop k).map g.continuous)

/-- **Lemma 2.5**, loop version: a π₁-injective map sends loop wild points to loop wild
points. -/
theorem image_loopWildSet_subset {f : C(X, Y)}
    (hf : ∀ x, Function.Injective (FundamentalGroup.map f x)) :
    f '' loopWildSet X ⊆ loopWildSet Y := by
  rintro _ ⟨x, hx, rfl⟩ U hU
  obtain ⟨γ, hγU, hγ⟩ := hx (f ⁻¹' U) (f.continuous.continuousAt hU)
  refine ⟨γ.map f.continuous, ?_, not_homotopic_refl_map_of_injective (hf x) hγ⟩
  rw [Path.map_coe, range_comp]
  exact image_subset_iff.2 hγU

end Peano
