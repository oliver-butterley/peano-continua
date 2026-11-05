module

public import Peano.OnlyIf
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Brazas–Fischer Theorem 9.15: homotopy equivalences restrict to homeomorphisms of wild sets

Brazas–Fischer, *On the failure of the first Čech homotopy group to register geometrically relevant
fundamental group elements*, Bull. London Math. Soc. 52 (2020), arXiv:1902.08887v2, Theorem 9.15,
quoted by Brazas–Pavešić (arXiv:2610.35875) in the proof of Theorem 1.2: a homotopy equivalence
`f : X → Y` of one-dimensional metric spaces (with homotopy inverse `g`) restricts to a
homeomorphism `w(X) → w(Y)` with inverse the restriction of `g`.

It is proved from the cited discrete-monodromy axiom `exists_nhds_monodromy`, following
Brazas–Fischer's own argument (Lemma 9.17, Corollary 9.18, proof of Theorem 9.15).

* `apply_eq_of_homotopic_id` (Lemma 9.17 / Corollary 9.18 for the loop wild set): in a
  path-connected one-dimensional metric space, a self-map `h ≃ id` fixes every wild point `x`.
  Let `β : h x ⟶ x` be the track of `x` under the homotopy. For every loop `γ` at `x`,
  `γ ≃ β⁻ (h ∘ γ) β` (naturality, Mathlib's `Path.Homotopic.map_trans_evalAt`). If `h x ≠ x`,
  the monodromy axiom (points `x`, `h x`, path `β⁻`) gives neighbourhoods `U ∋ x`, `V ∋ h x`; an
  essential loop `γ` at `x` inside `U ∩ h⁻¹ V` (which exists since `x` is wild) would then be
  null-homotopic. Note that π₁-injectivity of `h` is not even needed.
* `HomotopyEquiv.loopWildSetHomeomorph` / `HomotopyEquiv.wildSetHomeomorph` (Theorem 9.15): `f` and
  `g` are π₁-injective (a homotopy equivalence is a weak homotopy equivalence), so they map wild
  sets into wild sets (Lemma 2.5, `image_loopWildSet_subset`, `mapsTo_wildSet`); `g ∘ f = id` on
  `w(X)` and `f ∘ g = id` on `w(Y)` by the previous item; the restrictions are continuous.
* `nonempty_homeomorph_loopWildSet`, `nonempty_homeomorph_wildSet`: the existence statements used
  downstream (the latter is restated in `Peano/Audit/Thm1_2.lean`).

## Design

The general construction `homeomorphOfMapsTo` builds a homeomorphism between subsets `A ⊆ X`,
`B ⊆ Y` from continuous maps `f : X → Y`, `g : Y → X` mapping `A` into `B` and `B` into `A` that
are mutually inverse there. Brazas–Fischer's hypothesis is the discrete monodromy property; here
it enters through their Proposition 9.13 and the axiom, whence the hypotheses metric,
path-connected, covering dimension `≤ 1`; the spaces are in `Type` because the axiom is; compactness
and local path-connectedness are not needed for the loop
wild set. For `wildSet` (Definition 2.2) only `wildSet ⊆ loopWildSet` is used, so no first
countability argument is needed either.
-/

@[expose] public section

open Set Topology

noncomputable section

namespace Peano

/-- A homeomorphism between subsets `A ⊆ X` and `B ⊆ Y`, from continuous maps `f : X → Y` and
`g : Y → X` that map `A` into `B` and `B` into `A` and are mutually inverse there. -/
def homeomorphOfMapsTo {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (g : C(Y, X)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (hg : MapsTo g B A)
    (hgf : ∀ x ∈ A, g (f x) = x) (hfg : ∀ y ∈ B, f (g y) = y) : A ≃ₜ B where
  toFun := hf.restrict
  invFun := hg.restrict
  left_inv x := Subtype.ext (hgf x x.2)
  right_inv y := Subtype.ext (hfg y y.2)
  continuous_toFun := f.continuous.restrict hf
  continuous_invFun := g.continuous.restrict hg

/-- **Brazas–Fischer, Lemma 9.17 / Corollary 9.18** (loop wild set form). In a path-connected
one-dimensional metric space, a self-map homotopic to the identity fixes every point of the loop
wild set. Derived from the cited discrete-monodromy axiom `exists_nhds_monodromy`. -/
theorem apply_eq_of_homotopic_id {X : Type} [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {h : C(X, X)} (hh : h.Homotopic (ContinuousMap.id X)) {x : X}
    (hx : x ∈ loopWildSet X) : h x = x := by
  obtain ⟨H⟩ := hh
  by_contra hne
  set β : Path (h x) x := H.evalAt x
  obtain ⟨U, hU, V, hV, hUV⟩ := exists_nhds_monodromy X hX (Ne.symm hne) β.symm
  obtain ⟨γ, hγUV, hγ⟩ :=
    hx (U ∩ h ⁻¹' V) (Filter.inter_mem hU (h.continuous.continuousAt.preimage_mem_nhds hV))
  refine hγ (hUV γ (γ.map h.continuous) (hγUV.trans inter_subset_left) ?_ ?_)
  · rw [Path.map_coe, range_comp]
    exact image_subset_iff.2 (hγUV.trans inter_subset_right)
  · have hnat : ((γ.map h.continuous).trans β).Homotopic (β.trans γ) :=
      Path.Homotopic.map_trans_evalAt H γ
    rw [← Path.Homotopic.Quotient.eq] at hnat ⊢
    simp only [Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm] at hnat ⊢
    rw [Path.Homotopic.Quotient.trans_assoc, hnat, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- **Brazas–Fischer, Corollary 9.18** for the wild set of Brazas–Pavešić's Definition 2.2. -/
theorem apply_eq_of_homotopic_id_of_mem_wildSet {X : Type} [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {h : C(X, X)} (hh : h.Homotopic (ContinuousMap.id X)) {x : X}
    (hx : x ∈ wildSet X) : h x = x :=
  apply_eq_of_homotopic_id hX hh (wildSet_subset_loopWildSet X hx)

namespace HomotopyEquiv

/-- A homotopy equivalence is π₁-injective at every point. -/
theorem injective_fundamentalGroup_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Injective (FundamentalGroup.map e.toFun x) :=
  ((Peano.HomotopyEquiv.isWeakHomotopyEquivalence e).fundamentalGroup_map_bijective x).1

variable {X Y : Type} [MetricSpace X] [PathConnectedSpace X] [MetricSpace Y]
  [PathConnectedSpace Y] (hX : CoveringDimLE 1 X) (hY : CoveringDimLE 1 Y)
  (e : ContinuousMap.HomotopyEquiv X Y)

/-- **Brazas–Fischer, Theorem 9.15** (loop wild set form). A homotopy equivalence `e` of
path-connected one-dimensional metric spaces restricts to a homeomorphism of loop wild sets, whose
inverse is the restriction of the homotopy inverse (`loopWildSetHomeomorph_apply`,
`loopWildSetHomeomorph_symm_apply`). -/
def loopWildSetHomeomorph : loopWildSet X ≃ₜ loopWildSet Y :=
  homeomorphOfMapsTo e.toFun e.invFun
    (fun x hx => image_loopWildSet_subset (injective_fundamentalGroup_map e) ⟨x, hx, rfl⟩)
    (fun y hy => image_loopWildSet_subset (injective_fundamentalGroup_map e.symm) ⟨y, hy, rfl⟩)
    (fun _ hx => apply_eq_of_homotopic_id hX e.left_inv hx)
    (fun _ hy => apply_eq_of_homotopic_id hY e.right_inv hy)

/-- The homeomorphism of loop wild sets is the restriction of `e`. -/
@[simp] theorem loopWildSetHomeomorph_apply (x : loopWildSet X) :
    (loopWildSetHomeomorph hX hY e x : Y) = e.toFun x := rfl

/-- The inverse of the homeomorphism of loop wild sets is the restriction of the homotopy
inverse. -/
@[simp] theorem loopWildSetHomeomorph_symm_apply (y : loopWildSet Y) :
    ((loopWildSetHomeomorph hX hY e).symm y : X) = e.invFun y := rfl

/-- **Brazas–Fischer, Theorem 9.15** (Definition 2.2 form). A homotopy equivalence `e` of
path-connected one-dimensional metric spaces restricts to a homeomorphism of wild sets, whose
inverse is the restriction of the homotopy inverse (`wildSetHomeomorph_apply`,
`wildSetHomeomorph_symm_apply`). -/
def wildSetHomeomorph : wildSet X ≃ₜ wildSet Y :=
  homeomorphOfMapsTo e.toFun e.invFun
    (mapsTo_wildSet (injective_fundamentalGroup_map e))
    (mapsTo_wildSet (injective_fundamentalGroup_map e.symm))
    (fun _ hx => apply_eq_of_homotopic_id_of_mem_wildSet hX e.left_inv hx)
    (fun _ hy => apply_eq_of_homotopic_id_of_mem_wildSet hY e.right_inv hy)

/-- The homeomorphism of wild sets is the restriction of `e`. -/
@[simp] theorem wildSetHomeomorph_apply (x : wildSet X) :
    (wildSetHomeomorph hX hY e x : Y) = e.toFun x := rfl

/-- The inverse of the homeomorphism of wild sets is the restriction of the homotopy inverse. -/
@[simp] theorem wildSetHomeomorph_symm_apply (y : wildSet Y) :
    ((wildSetHomeomorph hX hY e).symm y : X) = e.invFun y := rfl

end HomotopyEquiv

/-- **Brazas–Fischer, Theorem 9.15** (existence form): homotopy equivalent one-dimensional Peano
continua have homeomorphic loop wild sets. -/
theorem nonempty_homeomorph_loopWildSet (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (e : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (loopWildSet X ≃ₜ loopWildSet Y) :=
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  have : PathConnectedSpace Y := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  ⟨HomotopyEquiv.loopWildSetHomeomorph hX hY e⟩

/-- **Brazas–Fischer, Theorem 9.15** for the wild set of Definition 2.2: homotopy equivalent
one-dimensional Peano continua have homeomorphic wild sets (used for Theorem 1.2). The explicit
homeomorphism, the restriction of the homotopy equivalence, is
`HomotopyEquiv.wildSetHomeomorph`. -/
theorem nonempty_homeomorph_wildSet (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (e : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (wildSet X ≃ₜ wildSet Y) :=
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  have : PathConnectedSpace Y := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  ⟨HomotopyEquiv.wildSetHomeomorph hX hY e⟩

end Peano
