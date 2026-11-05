module

public import PeanoPartA.SingularH1Generators
public import PeanoPartA.Lemma3_3General

/-!
# Lemmas 3.2, 3.3, 3.4 and 6.3 with genuine singular homology

Brazas–Pavešić (arXiv:2610.35875), §3 and Lemma 6.3, restated with the first singular homology
group `H₁(X; ℤ)` (`Peano.singularH1`) and the singular class `[α]_h` of a loop (`Peano.h1Class`),
as the paper states them. The proofs are corollaries of the abelianisation-based theorems of
`PeanoPartA.Lemmas` and `PeanoPartA.Lemma3_3General`, through the Hurewicz bridge of
`PeanoPartA.SingularH1` (Tau Ceti's degree-one Hurewicz theorem) and the normal form of
`PeanoPartA.SingularH1Generators`.

* **Lemma 3.3** (`singularHomologyMap_val_injective`): for a one-dimensional Peano continuum `X`
  and **any** subset `A ⊆ X`, the map `H₁(A) → H₁(X)` induced by the inclusion is injective. This
  is the paper's statement verbatim (with the scope restriction below), including subsets with
  several path components. Proof: every element of `H₁(A)` is `Σ_{c ∈ s} [ℓ c]_h` with loops `ℓ c`
  at chosen points of pairwise distinct path components of `A` (`exists_finset_sum_h1Class`); if
  its image vanishes, the abelianisation form of the general Lemma 3.3
  (`fromPath_mem_commutator_of_sum_homologyClass_eq_zero`, transported along the Hurewicz
  isomorphism of `X` by `hurewiczHomologyAddEquiv_homologyClass`) makes every `ℓ c`
  null-homologous in `A`. Loop form: `h1Class_eq_zero_of_map_val`.
* **Lemma 3.4** (`h1Class_ne_of_disjoint`, `h1Class_ne_of_disjoint_of_or`): loops with disjoint
  images, one of which has `[α]_h ≠ 0` in `H₁(X)`, have different classes in `H₁(X)`.
* **Lemma 6.3** (`exists_earringMap_h1Class_ne_zero`): for `x ∈ w(X)` there is `f : 𝔼 → X`
  based at `x` with `[f ∘ ℓₙ]_h ≠ 0` in `H₁(X)` for every `n`.
* **Lemma 3.2**, the cited direction, in Eda's own terms (`eda_zeroForm_of_h1Class_eq_zero`):
  the axiom `eda_zeroForm` with the hypothesis `[α]_h = 0` in `H₁(X)` (Eda 2016, Lemma 3.6) in
  place of commutator membership; a corollary of the axiom and the bridge, so the axiom as stated
  (with the abelianisation hypothesis) says exactly what Eda's lemma says on path-connected spaces.

**Scope.** As in `PeanoPartA.Lemmas`: one-dimensional Peano continua `X : Type` (compact, connected,
locally path-connected metric spaces of covering dimension `≤ 1`), the scope of `eda_zeroForm`; the
paper states the lemmas for one-dimensional (path-connected) metrizable spaces. Axioms: those of
the abelianisation-based statements (Tau Ceti's Hurewicz theorem adds none).
-/

@[expose] public section

open Set Function Topology TauCeti.HurewiczOne

noncomputable section

namespace Peano

/-! ### Lemma 3.3 -/

/-- **Lemma 3.3** (Brazas–Pavešić): in a one-dimensional Peano continuum `X`, for **every**
subset `A ⊆ X` the map `H₁(A; ℤ) → H₁(X; ℤ)` induced by the inclusion is injective. The paper
states Lemma 3.3 for any one-dimensional metrizable space; the restriction to Peano continua (and
to `X : Type`) is the scope of the axiom `eda_zeroForm`. -/
theorem singularHomologyMap_val_injective (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (A : Set X) :
    Function.Injective (ContinuousMap.singularHomologyMap ℤ 1
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))) := by
  classical
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  obtain ⟨x⟩ : Nonempty X := inferInstance
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  obtain ⟨s, ℓ, rfl⟩ := exists_finset_sum_h1Class h
  rw [map_sum] at hh
  simp only [singularHomologyMap_h1Class] at hh
  have hsum : ∑ c : s, homologyClass x ((ℓ c).map continuous_subtype_val) = 0 := by
    rw [← (hurewiczHomologyAddEquiv (X := TopCat.of X) x).map_eq_zero_iff, map_sum]
    refine (Finset.sum_congr rfl fun c _ => hurewiczHomologyAddEquiv_homologyClass x _).trans ?_
    rw [Finset.sum_coe_sort s (fun c => h1Class ((ℓ c).map continuous_subtype_val))]
    exact hh
  have hcomm := fromPath_mem_commutator_of_sum_homologyClass_eq_zero X hX A x
    (fun c : s => componentRep c.1) (fun c => ℓ c.1)
    (fun c c' hcc' => not_joined_componentRep (fun h => hcc' (Subtype.ext h))) hsum
  refine Finset.sum_eq_zero fun c hc => ?_
  exact h1Class_eq_zero_of_mem_commutator _ (hcomm ⟨c, hc⟩)

/-- **Lemma 3.3**, loop form: in a one-dimensional Peano continuum `X`, a loop in any subset `A`
whose class vanishes in `H₁(X)` has class zero in `H₁(A)`. -/
theorem h1Class_eq_zero_of_map_val (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (A : Set X)
    {a : A} (γ : Path a a) (h : h1Class (γ.map continuous_subtype_val) = 0) :
    h1Class γ = 0 := by
  refine singularHomologyMap_val_injective X hX A ?_
  rw [map_zero, singularHomologyMap_h1Class]
  exact h

/-! ### Lemma 3.4 -/

/-- **Lemma 3.4**: in a one-dimensional Peano continuum, if loops `α` at `x₀` and `β` at `x₁`
have disjoint images and `[α]_h ≠ 0` in `H₁(X)`, then `[α]_h ≠ [β]_h`. No reducedness hypothesis is
needed; the restriction to Peano continua is the scope of the axiom `eda_zeroForm`. -/
theorem h1Class_ne_of_disjoint (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x₀ x₁ : X}
    (α : Path x₀ x₀) (β : Path x₁ x₁) (hd : Disjoint (range α) (range β))
    (hα : h1Class α ≠ 0) : h1Class α ≠ h1Class β := by
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  rw [Ne, ← isHomologous_iff_h1Class_eq]
  exact not_isHomologous_of_disjoint X hX α β hd (mt (h1Class_eq_zero_iff α).2 hα)

/-- **Lemma 3.4**, as stated in the paper ("if at least one of them is not null-homologous"):
loops with disjoint images, one of which has nonzero class in `H₁(X)`, have different classes. -/
theorem h1Class_ne_of_disjoint_of_or (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x₀ x₁ : X}
    (α : Path x₀ x₀) (β : Path x₁ x₁) (hd : Disjoint (range α) (range β))
    (h : h1Class α ≠ 0 ∨ h1Class β ≠ 0) : h1Class α ≠ h1Class β := by
  rcases h with hα | hβ
  · exact h1Class_ne_of_disjoint X hX α β hd hα
  · exact fun h => h1Class_ne_of_disjoint X hX β α hd.symm hβ h.symm

/-! ### Lemma 6.3 -/

/-- **Lemma 6.3** (corrected per `notes/checks/D.md`: the paper's proof uses local
path-connectedness, which its statement does not assume; here `X` is a Peano continuum): for a one-dimensional Peano continuum `X`
and a wild point `x ∈ w(X)` there is a map `f : 𝔼 → X` from the earring with `f b₀ = x` such that
`[f ∘ ℓₙ]_h ≠ 0` in `H₁(X)` for every `n`. The restriction to Peano continua is the scope of the
axiom `eda_zeroForm`. -/
theorem exists_earringMap_h1Class_ne_zero (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x : X}
    (hx : x ∈ wildSet X) :
    ∃ f : C(earring, X), f earringBase = x ∧ ∀ n,
      h1Class ((earringLoop n).map f.continuous) ≠ 0 := by
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  obtain ⟨f, hfx, hf⟩ := exists_earringMap_not_mem_commutator X hX hx
  exact ⟨f, hfx, fun n => mt (h1Class_eq_zero_iff _).1 (hf n)⟩

/-! ### Lemma 3.2 in Eda's terms -/

/-- **Lemma 3.2**, the cited direction, with Eda's hypothesis `[α]_h = 0` in `H₁(X)` (Eda 2016,
Lemma 3.6): an essential loop with zero singular homology class has a reduced representative that
is a 0-form. A corollary of the axiom `eda_zeroForm` (stated with commutator membership) and the
Hurewicz bridge `h1Class_eq_zero_iff`. -/
theorem eda_zeroForm_of_h1Class_eq_zero (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x : X}
    (α : Path x x) (hα : ¬ α.Homotopic (Path.refl x)) (h : h1Class α = 0) :
    ∃ ρ : Path x x, IsReducedPath ρ ∧ ρ.Homotopic α ∧ IsZeroFormCut (ρ : C(unitInterval, X)) := by
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  exact eda_zeroForm X hX α hα ((h1Class_eq_zero_iff α).1 h)

end Peano
