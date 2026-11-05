module

import Peano

/-!
# Audit: Part A (§2–3), Lemma 6.3 and the paper's own proof of Lemma 6.4

Restates the Part A results with `recall` (which fails unless the restatement matches the proved
declaration), prints the two homology definitions they use, then prints their axioms.

H₁ of a path-connected space is modelled by the abelianisation of π₁ (Hurewicz); see the header of
`Peano/Homology.lean`. Lemmas 3.3, 3.4 and 6.3 are stated for one-dimensional Peano continua
`X : Type` (the scope of the axiom `eda_zeroForm`); the paper states them for one-dimensional
(path-connected) metrizable spaces.

Expected axioms (besides `propext`, `Classical.choice`, `Quot.sound`):
* Lemma 2.8 (`fundamentalGroup_map_val_injective`): `exists_reduced_homotopy`,
  `isReparam_of_reduced_homotopic` (Cannon–Conner);
* `fromPath_mem_commutator_of_isZeroFormCut` (0-forms are null-homologous): none;
* Lemmas 3.3, 3.4 (`abelianization_map_val_injective`, `not_isHomologous_of_disjoint`), the general
  Lemma 3.3 (`fromPath_mem_commutator_of_sum_eq_zero`) and its core
  (`homologyClass_eq_zero_of_sum_eq_zero`): the two above and `eda_zeroForm` (Eda 2016, direction "⇒" only);
* Lemma 6.3 (`exists_earringMap_not_mem_commutator`): those three and `exists_simpleClosedCurve`;
* `injOn_wildSet_of_paper`: the Lemma 6.3 axioms (all four above) and `eda_exists_map_earring`,
  `exists_nhds_monodromy`.
-/

open Set Function Peano

#print Peano.IsHomologous
#print Peano.homologyClass

-- Lemma 2.8.
recall Peano.fundamentalGroup_map_val_injective (X : Type) [MetricSpace X]
    (hX : CoveringDimLE 1 X) (A : Set X) (a : A) :
    Function.Injective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ a)

-- 0-forms are null-homologous (the direction of Lemma 3.2 the paper uses).
recall Peano.fromPath_mem_commutator_of_isZeroFormCut {X : Type*} [TopologicalSpace X] {x : X}
    (ρ : Path x x) (h : IsZeroFormCut (ρ : C(unitInterval, X))) :
    FundamentalGroup.fromPath ⟦ρ⟧ ∈ commutator (FundamentalGroup X x)

-- Lemma 3.3, one path component of `A` at a time.
recall Peano.abelianization_map_val_injective (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (A : Set X)
    (a : A) :
    Function.Injective
      (Abelianization.map (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ a))

-- Lemma 3.3, general form (several path components of `A`).
recall Peano.fromPath_mem_commutator_of_sum_eq_zero (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (A : Set X)
    (x : X) {ι : Type*} [Fintype ι] (a : ι → A) (α : ∀ i, Path (a i) (a i))
    (ha : Pairwise fun i j => ¬ Joined (a i) (a j)) (p : ∀ i, Path x (a i : X))
    (hsum : ∑ i, Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      ⟦((p i).trans ((α i).map continuous_subtype_val)).trans (p i).symm⟧)) = 0) (i : ι) :
    FundamentalGroup.fromPath ⟦α i⟧ ∈ commutator (FundamentalGroup A (a i))

-- The core of the general Lemma 3.3: loops in `X` with pairwise disjoint images.
recall Peano.homologyClass_eq_zero_of_sum_eq_zero (X : Type) [MetricSpace X] [CompactSpace X]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (x : X)
    {ι : Type*} (ℓ : ι → Σ y : X, Path y y) (s : Finset ι)
    (hd : (s : Set ι).Pairwise (Disjoint on fun i => range (ℓ i).2))
    (hsum : ∑ i ∈ s, homologyClass x (ℓ i).2 = 0) :
    ∀ i ∈ s, homologyClass x (ℓ i).2 = 0

-- Lemma 3.4 (no reducedness hypothesis).
recall Peano.not_isHomologous_of_disjoint (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x₀ x₁ : X}
    (α : Path x₀ x₀) (β : Path x₁ x₁) (hd : Disjoint (range α) (range β))
    (hα : FundamentalGroup.fromPath ⟦α⟧ ∉ commutator (FundamentalGroup X x₀)) :
    ¬ IsHomologous α β

-- Lemma 6.3 (corrected).
recall Peano.exists_earringMap_not_mem_commutator (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x : X}
    (hx : x ∈ wildSet X) :
    ∃ f : C(earring, X), f earringBase = x ∧ ∀ n,
      FundamentalGroup.fromPath ⟦(earringLoop n).map f.continuous⟧ ∉
        commutator (FundamentalGroup X (f earringBase))

-- Lemma 6.4 by the paper's homological proof.
recall Peano.injOn_wildSet_of_paper (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {Y : Type*} [TopologicalSpace Y]
    {f : C(X, Y)} (hf : ∀ x, Function.Bijective (FundamentalGroup.map f x)) :
    Set.InjOn f (wildSet X)

#print axioms Peano.fundamentalGroup_map_val_injective
#print axioms Peano.fromPath_mem_commutator_of_isZeroFormCut
#print axioms Peano.abelianization_map_val_injective
#print axioms Peano.fromPath_mem_commutator_of_sum_eq_zero
#print axioms Peano.homologyClass_eq_zero_of_sum_eq_zero
#print axioms Peano.not_isHomologous_of_disjoint
#print axioms Peano.exists_earringMap_not_mem_commutator
#print axioms Peano.injOn_wildSet_of_paper
