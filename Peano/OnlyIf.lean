module

public import Peano.EarringOps
public import Peano.WildSet
public import Peano.Axioms.Cited

/-!
# Lemmas 6.2 and 6.4, and Theorem 1.1 "only if"

Brazas–Pavešić (arXiv:2610.35875), §6.

* **Lemma 6.2** (`eq_of_homotopic_conj`, earring form `eq_of_fullyEssential_homotopic_conj`): in
  a path-connected one-dimensional metric space, if essential loops `γₖ` shrinking to `x` are
  homotopic to `α⁻ δₖ α` for loops `δₖ` shrinking to `y` and a path `α : y ⟶ x`, then `y = x`.
  Derived from the cited discrete-monodromy axiom `exists_nhds_monodromy`: if `y ≠ x`, for large
  `k` the loop `γₖ` lies in the neighbourhood `U` of `x` and `δₖ` in the neighbourhood `V` of `y`
  given by the axiom (with `β = α⁻`), so `γₖ` is null-homotopic.
* **Lemma 6.4** (`injOn_wildSet`): a map `f : X → Y` from a one-dimensional Peano continuum to any
  space, inducing bijections on all fundamental groups, is injective on `w(X)`; with Lemma 2.5
  (`mapsTo_wildSet`) it restricts to an injection `w(X) → w(Y)`, so `|w(X)| ≤ |w(Y)|`
  (`mk_wildSet_le`). Deviations from the paper: the paper states Lemma 6.4 for path-connected,
  locally path-connected one-dimensional metric spaces, but its proof applies Theorem 6.1, which is
  quoted for Peano continua (`notes/checks/D.md`, finding 2), so `X` is a Peano continuum here; on
  the other hand `Y` is an arbitrary space (the paper assumes it path-connected).
* **Theorem 1.1, "only if"** (`countable_wildSet_of_weq`). The equivalence is
  `Peano.exists_countable_weq_iff` in `Peano.Thm1_1`; Lemma 6.4 is also used by the "if" half
  (`Peano.exists_countable_weq`), as in the paper.

## The proof of Lemma 6.4

The paper's proof of Lemma 6.4 uses first homology (Lemmas 3.3, 3.4, 6.3, i.e. Part A); that
route is formalised separately (`Peano.injOn_wildSet_of_paper` in `PeanoPartA.Lemma6_4Paper`, on top
of
`PeanoPartA.Lemmas`, with more cited axioms). The main development uses instead a homology-free
argument using Theorem 6.1 (Eda, axiom `eda_exists_map_earring`) and Lemma 6.2 twice. Suppose
`x₀ ≠ x₁` in `w(X)`, `f x₀ = f x₁`, with fully essential `g₀, g₁` based at `x₀, x₁`. Let
`h : 𝔼 → Y` interleave `f ∘ g₀` (even circles) and `f ∘ g₁` (odd circles). Theorem 6.1 applied to
`f#⁻¹ ∘ h# : π₁(𝔼, b₀) → π₁(X, x₁)` gives `g : 𝔼 → X` and `α : g b₀ ⟶ x₁` with
`f ∘ (α⁻ (g ∘ ℓₖ) α) ≃ h ∘ ℓₖ` for all `k` (`exists_map_earring_homotopic`).

* Odd circles: by π₁-injectivity at `x₁`, `g₁ ∘ ℓⱼ ≃ α⁻ (g ∘ ℓ_{2j+1}) α`, and Lemma 6.2 gives
  `g b₀ = x₁`.
* Even circles: choose a path `q : x₀ ⟶ x₁` with `f ∘ q` null-homotopic (a path `p` corrected by
  a loop `β` at `x₁` with `f ∘ β ≃ f ∘ p`, by π₁-surjectivity at `x₁`). With `r = α q⁻`,
  `f ∘ (r⁻ (g ∘ ℓ_{2j}) r) ≃ f ∘ g₀ ∘ ℓⱼ`; by π₁-injectivity at `x₀`,
  `g₀ ∘ ℓⱼ ≃ r⁻ (g ∘ ℓ_{2j}) r`, and Lemma 6.2 gives `g b₀ = x₀`.

Hence `x₀ = x₁`. Only π₁-bijectivity at `x₀` (injectivity) and `x₁` is used.

## Design

Lemma 6.2 is stated first for loop families (`LoopsShrinkTo`), which avoids the casts that
sub-earring maps `g ∘ earringSub ν` would introduce (`earringSub ν b₀ = b₀` holds only
propositionally); the earring form follows. All path algebra is done with `Path.Homotopic` and
`Path.Homotopic.Quotient`; the group level appears only in `exists_map_earring_homotopic`, where
the Eda axiom requires a homomorphism `ψ`. There `ψ = f#⁻¹ ∘ (h#, cast to the base point f x₁)`,
built from `fundamentalGroupMapEquiv` (`Peano.HomotopyEquiv`) and Mathlib's
`FundamentalGroup.mapOfEq`. Points of `Y` that agree only propositionally (`f x₀ = f x₁`) are
handled by `Path.cast` and two small private lemmas proved by `subst`.
-/

@[expose] public section

open Set Filter Topology unitInterval

noncomputable section

namespace Peano

/-! ### Lemma 6.2 -/

/-- **Lemma 6.2**, loop-family form. In a path-connected one-dimensional metric space, let
`γ k` be essential loops at `x` shrinking to `x`, `δ k` loops at `y` shrinking to `y`, and
`α : y ⟶ x` a path with `γ k ≃ α⁻ (δ k) α` for all `k`. Then `y = x`. Derived from the cited
discrete monodromy property `exists_nhds_monodromy`. -/
theorem eq_of_homotopic_conj {X : Type} [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {x y : X} {γ : ℕ → Path x x} {δ : ℕ → Path y y}
    (hγ : LoopsShrinkTo x γ) (hδ : LoopsShrinkTo y δ)
    (hess : ∀ k, ¬ (γ k).Homotopic (Path.refl x)) (α : Path y x)
    (hconj : ∀ k, (γ k).Homotopic ((α.symm.trans (δ k)).trans α)) : y = x := by
  by_contra hne
  obtain ⟨U, hU, V, hV, hUV⟩ := exists_nhds_monodromy X hX (Ne.symm hne) α.symm
  obtain ⟨k, hkU, hkV⟩ := ((hγ U hU).and (hδ V hV)).exists
  exact hess k (hUV _ _ hkU hkV (by simpa only [Path.symm_symm] using hconj k))

/-- **Lemma 6.2** (the paper's form). In a path-connected one-dimensional metric space, let
`f₁, f₂ : 𝔼 → X` be maps with `f₁` fully essential and `α : f₂ b₀ ⟶ f₁ b₀` a path with
`f₁ ∘ ℓⱼ ≃ α⁻ (f₂ ∘ ℓⱼ) α` for all `j`. Then `f₂ b₀ = f₁ b₀`. (The paper also assumes `f₂`
fully essential; this is not needed.) -/
theorem eq_of_fullyEssential_homotopic_conj {X : Type} [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {f₁ f₂ : C(earring, X)} (hf₁ : FullyEssential f₁)
    (α : Path (f₂ earringBase) (f₁ earringBase))
    (h : ∀ j, ((earringLoop j).map f₁.continuous).Homotopic
      ((α.symm.trans ((earringLoop j).map f₂.continuous)).trans α)) :
    f₂ earringBase = f₁ earringBase :=
  eq_of_homotopic_conj hX (loopsShrinkTo_map_earringLoop f₁) (loopsShrinkTo_map_earringLoop f₂)
    hf₁ α h

/-! ### Path algebra -/

section PathAlgebra

variable {Y : Type*} [TopologicalSpace Y]

/-- If `d ≃ c` (a loop at `b`, and a path `c : a ⟶ b` cast to a loop along `b = a`), then
`c d⁻ ≃` the constant path (cast to a path `a ⟶ b`). -/
private theorem homotopic_trans_symm_cast {a b : Y} (e : b = a) (c : Path a b) (d : Path b b)
    (hd : d.Homotopic (c.cast e rfl)) :
    (c.trans d.symm).Homotopic ((Path.refl a).cast rfl e) := by
  subst e
  rw [← Path.Homotopic.Quotient.eq] at hd ⊢
  rw [Path.cast_rfl_rfl] at hd ⊢
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm, hd,
    Path.Homotopic.Quotient.trans_symm]
  rfl

/-- Conjugating by a null-homotopic path: if `c : a ⟶ b` is homotopic to the constant path
(cast along `b = a`) and `M ≃ L` (a loop at `a` cast to a loop at `b`), then `L ≃ c M c⁻`. -/
private theorem homotopic_conj_of_homotopic_refl_cast {a b : Y} (e : b = a) (c : Path a b)
    (hc : c.Homotopic ((Path.refl a).cast rfl e)) (L : Path a a) (M : Path b b)
    (hM : M.Homotopic (L.cast e e)) : L.Homotopic ((c.trans M).trans c.symm) := by
  subst e
  rw [← Path.Homotopic.Quotient.eq] at hc hM ⊢
  rw [Path.cast_rfl_rfl] at hc hM
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, hc, hM, ← Path.Homotopic.Quotient.mk_symm, Path.refl_symm,
    ← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]

end PathAlgebra

/-! ### Theorem 6.1 applied to `f#⁻¹ ∘ h#` -/

/-- Theorem 6.1 (Eda) applied to `f#⁻¹ ∘ h#`: for a one-dimensional Peano continuum `X`, a map
`f : X → Y` bijective on `π₁(X, x₁)` and a map `h : 𝔼 → Y` with `h b₀ = f x₁`, there are
`g : 𝔼 → X` and `α : g b₀ ⟶ x₁` with `f ∘ (α⁻ (g ∘ ℓₖ) α) ≃ h ∘ ℓₖ` for every `k` (the
right-hand side cast to a loop at `f x₁`). -/
theorem exists_map_earring_homotopic (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*}
    [TopologicalSpace Y] {f : C(X, Y)} {x₁ : X}
    (hf : Function.Bijective (FundamentalGroup.map f x₁)) (h : C(earring, Y))
    (hb : h earringBase = f x₁) :
    ∃ (g : C(earring, X)) (α : Path (g earringBase) x₁), ∀ k,
      (((α.symm.trans ((earringLoop k).map g.continuous)).trans α).map f.continuous).Homotopic
        (((earringLoop k).map h.continuous).cast hb.symm hb.symm) := by
  set e := fundamentalGroupMapEquiv f x₁ hf
  obtain ⟨g, α, hgα⟩ := eda_exists_map_earring X hX x₁
    (e.symm.toMonoidHom.comp (FundamentalGroup.mapOfEq h hb))
  refine ⟨g, α, fun k => ?_⟩
  have hk := congrArg e (hgα k)
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply] at hk
  rw [← fundamentalGroup_fromPath_eq_iff, ← fundamentalGroup_map_fromPath,
    ← fundamentalGroupMapEquiv_apply f x₁ hf, ← hk, fundamentalGroup_mapOfEq_fromPath]

/-! ### Lemma 6.4 -/

/-- **Lemma 6.4**: a map `f : X → Y` from a one-dimensional Peano continuum to any space that
induces bijections on all fundamental groups is injective on the wild set `w(X)`. (Proved without
homology; see the module docstring.) -/
theorem injOn_wildSet (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Bijective (FundamentalGroup.map f x)) :
    Set.InjOn f (wildSet X) := by
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  rintro _ ⟨g₀, rfl, hg₀⟩ _ ⟨g₁, rfl, hg₁⟩ hf01
  -- `hf01 : f (g₀ b₀) = f (g₁ b₀)`
  set x₀ := g₀ earringBase with hx₀
  set x₁ := g₁ earringBase with hx₁
  let h := earringInterleave (f.comp g₀) (f.comp g₁) hf01
  have hb : h earringBase = f x₁ := (earringInterleave_base _ _ _).trans hf01
  obtain ⟨g, α, hk⟩ := exists_map_earring_homotopic X hX (hf x₁) h hb
  -- Odd circles: `g b₀ = x₁`.
  have hodd : ∀ j, ((earringLoop j).map g₁.continuous).Homotopic
      ((α.symm.trans ((earringLoop (2 * j + 1)).map g.continuous)).trans α) := by
    intro j
    refine (homotopic_of_map_homotopic (hf x₁).1 ?_).symm
    have := hk (2 * j + 1)
    rwa [earringLoop_map_earringInterleave_two_mul_add_one, path_cast_cast] at this
  have h₁ : g earringBase = x₁ :=
    eq_of_homotopic_conj hX (loopsShrinkTo_map_earringLoop g₁)
      ((loopsShrinkTo_map_earringLoop g).comp_tendsto tendsto_nat_two_mul_add_one_atTop) hg₁ α hodd
  -- Even circles: `g b₀ = x₀`.
  have hx : f x₁ = f x₀ := hf01.symm
  obtain ⟨β, hβ⟩ := exists_map_homotopic (hf x₁).2
    (((PathConnectedSpace.somePath x₀ x₁).map f.continuous).cast hx rfl)
  set p := PathConnectedSpace.somePath x₀ x₁
  set q := p.trans β.symm
  have hq : (q.map f.continuous).Homotopic ((Path.refl (f x₀)).cast rfl hx) := by
    rw [Path.map_trans, ← Path.map_symm]
    exact homotopic_trans_symm_cast hx _ _ hβ
  set r := α.trans q.symm
  have heven : ∀ j, ((earringLoop j).map g₀.continuous).Homotopic
      ((r.symm.trans ((earringLoop (2 * j)).map g.continuous)).trans r) := by
    intro j
    refine homotopic_of_map_homotopic (hf x₀).1 ?_
    have h2 := hk (2 * j)
    rw [earringLoop_map_earringInterleave_two_mul, path_cast_cast] at h2
    have h3 := homotopic_conj_of_homotopic_refl_cast hx _ hq
      (((earringLoop j).map g₀.continuous).map f.continuous) _ h2
    refine h3.trans (Path.Homotopic.Quotient.eq.1 ?_)
    simp only [r, Path.trans_symm, Path.symm_symm, Path.map_trans, ← Path.map_symm,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc]
  have h₀ : g earringBase = x₀ :=
    eq_of_homotopic_conj hX (loopsShrinkTo_map_earringLoop g₀)
      ((loopsShrinkTo_map_earringLoop g).comp_tendsto tendsto_nat_two_mul_atTop) hg₀ r heven
  exact h₀.symm.trans h₁

/-- **Lemma 2.5** for the maps of Lemma 6.4: a π₁-injective map sends `w(X)` into `w(Y)`. -/
theorem mapsTo_wildSet {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Injective (FundamentalGroup.map f x)) :
    Set.MapsTo f (wildSet X) (wildSet Y) :=
  fun x hx => image_wildSet_subset hf ⟨x, hx, rfl⟩

/-- The paper's consequence of Lemma 6.4 (introduction): for a map from a one-dimensional Peano
continuum inducing bijections on all fundamental groups (e.g. a weak homotopy equivalence),
`|w(X)| ≤ |w(Y)|`. -/
theorem mk_wildSet_le (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Bijective (FundamentalGroup.map f x)) :
    Cardinal.mk (wildSet X) ≤ Cardinal.mk (wildSet Y) :=
  Cardinal.mk_le_of_injective (f := (mapsTo_wildSet fun x => (hf x).1).restrict)
    ((mapsTo_wildSet fun x => (hf x).1).restrict_inj.2 (injOn_wildSet X hX hf))

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1, "only if"**: if a one-dimensional Peano continuum `X` admits a weak homotopy
equivalence to a countable space, then its wild set is countable. -/
theorem countable_wildSet_of_weq (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*} [TopologicalSpace Y]
    [Countable Y] {f : C(X, Y)} (hf : IsWeakHomotopyEquivalence f) : (wildSet X).Countable :=
  (Set.mapsTo_univ f _).countable_of_injOn
    (injOn_wildSet X hX hf.fundamentalGroup_map_bijective) Set.countable_univ

end Peano
