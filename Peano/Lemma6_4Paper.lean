module

public import Peano.PartA
public import Peano.OnlyIf

/-!
# Lemma 6.4 by the paper's own (homological) proof

Brazas–Pavešić (arXiv:2610.35875), §6, proof of Lemma 6.4, with the repairs of
`notes/checks/D.md`. **This file exists only to check the paper's route.** The main theorems use
the shorter homology-free proof `Peano.injOn_wildSet` (`Peano.OnlyIf`); the two statements are the
same (`injOn_wildSet_of_paper_iff`).

## The argument formalised

Let `X` be a one-dimensional Peano continuum, `f : X → Y` inducing bijections on all fundamental
groups, and suppose `x₀ ≠ x₁` in `w(X)` with `f x₀ = f x₁`.

1. `g₀ : 𝔼 → X` at `x₀` is the special map of Lemma 6.3
   (`exists_earringMap_not_mem_commutator_fullyEssential`): fully essential, and no loop
   `g₀ ∘ ℓₙ` is null-homologous. `g₁` at `x₁` is any fully essential map.
2. `h : 𝔼 → Y` interleaves `f ∘ g₀` and `f ∘ g₁`. Convention: `Peano.earringInterleave` puts the
   first map on the even circles `ℓ_{2n}` and the second on the odd circles `ℓ_{2n+1}`; the paper
   puts `g₀` on the odd circles. Only the indexing changes.
3. Theorem 6.1 (Eda) for `f#⁻¹ ∘ h#` (`exists_map_earring_homotopic`) gives `g : 𝔼 → X` and a
   path `α : g b₀ ⟶ x₁` with `f ∘ (α⁻ (g ∘ ℓₖ) α) ≃ h ∘ ℓₖ` for all `k`.
4. Odd circles and Lemma 6.2 (`eq_of_homotopic_conj`, with the fully essential `g₁`, as repaired
   in D.md): `g b₀ = x₁`.
5. Even circles: for every `n`, with `a` any path `x₀ ⟶ x₁` and `M = α⁻ (g ∘ ℓ_{2n}) α`, the loop
   `L = a M a⁻ (g₀ ∘ ℓₙ)⁻` at `x₀` satisfies `f ∘ L ≃ b c b⁻¹ c⁻¹` with `b = f ∘ a`,
   `c = f ∘ g₀ ∘ ℓₙ` (`fromPath_conj_cast_trans_symm_mem_commutator`), so `[f ∘ L]` lies in the
   commutator subgroup of `π₁(Y, f x₀)`. Since `f#` is an isomorphism at `x₀`, `[L]` lies in the
   commutator subgroup of `π₁(X, x₀)` (`mulEquiv_map_mem_commutator_iff`). Hence `g₀ ∘ ℓₙ` and
   `g ∘ ℓ_{2n}` are homologous (`IsHomologous`, along the path `a α⁻ : x₀ ⟶ g b₀`).
6. The loops `g₀ ∘ ℓₙ` shrink to `x₀` and `g ∘ ℓ_{2n}` shrink to `g b₀ = x₁ ≠ x₀`, so for large `n`
   their images are disjoint, and Lemma 3.4 (`not_isHomologous_of_disjoint`, which needs no
   reducedness: D.md's repair) contradicts step 5.

Unlike the paper (which writes the loop at `x₀` through `δ̄ (g₃ ∘ ℓₙ) δ` after identifying
`g b₀ = x₁`), step 5 keeps `α` as a path `g b₀ ⟶ x₁`: `IsHomologous` compares loops at different
base points, so no cast along `g b₀ = x₁` is needed.

Axioms: those of Part A (`exists_reduced_homotopy`, `isReparam_of_reduced_homotopic`,
`eda_zeroForm`, `exists_simpleClosedCurve`), Theorem 6.1 (`eda_exists_map_earring`) and the
discrete monodromy property behind Lemma 6.2 (`exists_nhds_monodromy`).
-/

@[expose] public section

open Set Filter Topology unitInterval

noncomputable section

namespace Peano

/-- In `π₁(Y, u)`, the class of `b c' b⁻¹ c⁻¹` is a commutator, where `b : u ⟶ v` becomes a loop
along `v = u` and `c'` is the loop `c` at `u` cast to `v`. -/
theorem fromPath_conj_cast_trans_symm_mem_commutator {Y : Type*} [TopologicalSpace Y] {u v : Y}
    (e : v = u) (b : Path u v) (c : Path u u) :
    FundamentalGroup.fromPath ⟦((b.trans (c.cast e e)).trans b.symm).trans c.symm⟧ ∈
      commutator (FundamentalGroup Y u) := by
  subst e
  rw [mem_commutator_iff_abelianization_of_eq_one]
  show Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
    (((b.trans (c.cast rfl rfl)).trans b.symm).trans c.symm))) = 1
  rw [Path.cast_rfl_rfl]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    fundamentalGroup_fromPath_trans, fundamentalGroup_fromPath_symm, map_mul, map_inv]
  rw [mul_comm (Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c))),
    inv_mul_cancel_left, inv_mul_cancel]

/-- **Lemma 6.4, by the paper's proof** (homology, Lemmas 3.4 and 6.3; see the module docstring):
a map `f : X → Y` from a one-dimensional Peano continuum to any space that induces bijections on
all fundamental groups is injective on the wild set `w(X)`. Same statement as
`Peano.injOn_wildSet`. -/
theorem injOn_wildSet_of_paper (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Bijective (FundamentalGroup.map f x)) :
    Set.InjOn f (wildSet X) := by
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  intro x₀ hx₀ x₁ hx₁ hf01
  by_contra hne
  -- 1. the special map `g₀` (Lemma 6.3) and any fully essential `g₁`
  obtain ⟨g₀, rfl, -, hg₀⟩ := exists_earringMap_not_mem_commutator_fullyEssential X hX hx₀
  obtain ⟨g₁, rfl, hg₁⟩ := hx₁
  -- 2–3. interleave and apply Theorem 6.1
  let h := earringInterleave (f.comp g₀) (f.comp g₁) hf01
  have hb : h earringBase = f (g₁ earringBase) := (earringInterleave_base _ _ _).trans hf01
  obtain ⟨g, α, hk⟩ := exists_map_earring_homotopic X hX (hf (g₁ earringBase)) h hb
  -- 4. odd circles and Lemma 6.2: `g b₀ = x₁`
  have hodd : ∀ j, ((earringLoop j).map g₁.continuous).Homotopic
      ((α.symm.trans ((earringLoop (2 * j + 1)).map g.continuous)).trans α) := by
    intro j
    refine (homotopic_of_map_homotopic (hf _).1 ?_).symm
    have := hk (2 * j + 1)
    rwa [earringLoop_map_earringInterleave_two_mul_add_one, path_cast_cast] at this
  have h₁ : g earringBase = g₁ earringBase :=
    eq_of_homotopic_conj hX (loopsShrinkTo_map_earringLoop g₁)
      ((loopsShrinkTo_map_earringLoop g).comp_tendsto tendsto_nat_two_mul_add_one_atTop) hg₁ α hodd
  -- 6. (choice of `n`) disjoint images for large `n`
  obtain ⟨U, V, hUo, hVo, hx₀U, hx₁V, hUV⟩ := t2_separation hne
  have hV : V ∈ 𝓝 (g earringBase) := h₁ ▸ hVo.mem_nhds hx₁V
  obtain ⟨n, hnU, hnV⟩ := ((loopsShrinkTo_map_earringLoop g₀ U (hUo.mem_nhds hx₀U)).and
    ((loopsShrinkTo_map_earringLoop g).comp_tendsto tendsto_nat_two_mul_atTop V hV)).exists
  set G0 := (earringLoop n).map g₀.continuous with hG0
  set γ := (earringLoop (2 * n)).map g.continuous with hγ
  have hdisj : Disjoint (range G0) (range γ) := hUV.mono hnU hnV
  -- 5. even circles: `[f ∘ L]` is a commutator
  set a := PathConnectedSpace.somePath (g₀ earringBase) (g₁ earringBase)
  set M := (α.symm.trans γ).trans α with hM_def
  set L := ((a.trans M).trans a.symm).trans G0.symm with hL
  have hM : (M.map f.continuous).Homotopic ((G0.map f.continuous).cast hf01.symm hf01.symm) := by
    have h2 := hk (2 * n)
    rw [earringLoop_map_earringInterleave_two_mul, path_cast_cast] at h2
    exact h2
  have hfL : FundamentalGroup.fromPath ⟦L.map f.continuous⟧ ∈
      commutator (FundamentalGroup Y (f (g₀ earringBase))) := by
    have hq : Path.Homotopic.Quotient.mk (L.map f.continuous) = Path.Homotopic.Quotient.mk
        ((((a.map f.continuous).trans ((G0.map f.continuous).cast hf01.symm hf01.symm)).trans
          (a.map f.continuous).symm).trans (G0.map f.continuous).symm) := by
      simp only [hL, Path.map_trans, ← Path.map_symm, Path.Homotopic.Quotient.mk_trans]
      rw [Path.Homotopic.Quotient.eq.2 hM]
    show FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (L.map f.continuous)) ∈ _
    rw [hq]
    exact fromPath_conj_cast_trans_symm_mem_commutator hf01.symm _ _
  have hL' : FundamentalGroup.fromPath ⟦L⟧ ∈ commutator (FundamentalGroup X (g₀ earringBase)) := by
    rw [← mulEquiv_map_mem_commutator_iff (fundamentalGroupMapEquiv f _ (hf _)),
      fundamentalGroupMapEquiv_apply, fundamentalGroup_map_fromPath]
    exact hfL
  -- hence `g₀ ∘ ℓₙ` and `g ∘ ℓ_{2n}` are homologous
  have hhom : IsHomologous G0 γ := by
    refine ⟨a.trans α.symm, ?_⟩
    have hq : Path.Homotopic.Quotient.mk (((a.trans α.symm).trans γ).trans (a.trans α.symm).symm)
        = Path.Homotopic.Quotient.mk ((a.trans M).trans a.symm) := by
      simp only [hM_def, Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc]
    rw [mem_commutator_iff_abelianization_of_eq_one] at hL'
    change Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((a.trans M).trans a.symm).trans G0.symm))) = 1 at hL'
    rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      fundamentalGroup_fromPath_trans, fundamentalGroup_fromPath_symm, map_mul, map_inv,
      inv_mul_eq_one] at hL'
    show Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk G0)) =
      Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((a.trans α.symm).trans γ).trans (a.trans α.symm).symm)))
    rw [hq, hL']
  -- 6. contradiction with Lemma 3.4
  exact not_isHomologous_of_disjoint X hX G0 γ hdisj (hg₀ n) hhom

/-- The paper's proof and the homology-free proof `Peano.injOn_wildSet` establish the same
statement. -/
theorem injOn_wildSet_of_paper_iff (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*}
    [TopologicalSpace Y] {f : C(X, Y)} (hf : ∀ x, Function.Bijective (FundamentalGroup.map f x)) :
    injOn_wildSet_of_paper X hX hf = injOn_wildSet X hX hf :=
  rfl

end Peano
