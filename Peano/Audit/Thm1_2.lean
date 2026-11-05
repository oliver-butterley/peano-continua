module

import Peano

/-!
# Audit: Theorem 1.2 (corrected)

The paper's canonical correspondence of Theorem 1.2 (`λ ↦ Ho(A_λ)`, inverse `X ↦ w(X)`) is not a
bijection, because of continua with empty wild set (`Peano.Sanity.thm1_2_counterexample`); some
bijection exists for cardinality reasons (both sets have cardinality `ℵ₁`), so that is not what
fails. The corrected version is a bijection
between homotopy types of one-dimensional Peano continua with non-empty countable wild set and
homeomorphism types of non-empty countable compact metric spaces, `X ↦ w(X)`.

Expected axioms (besides the standard three):
* `nonempty_homeomorph_wildSet` and `HomotopyEquiv.wildSetHomeomorph` (Brazas–Fischer 9.15,
  proved in `Peano.BrazasFischer`): `Peano.exists_nhds_monodromy` (discrete monodromy).
* `nonempty_homotopyEquiv_iff`: `Peano.exists_nhds_monodromy`,
  `Peano.eda_homotopyEquiv_of_homeomorph` (Eda 2022, the paper's Theorem 6.6).
* `nonempty_homotopyEquiv_iff_of_weq`: those two and the other three of Theorem 1.1
  (`eda_exists_map_earring`, `exists_homotopyEquiv_standardForm`,
  `exists_homotopyEquiv_finiteGraph`).
* `exists_wildSet_homeomorph`: `Peano.coveringDimLE_one_of_interior_eq_empty` (dimension theory).
* `compactSpace_wildSet`: none.
-/

open Peano

recall Peano.nonempty_homotopyEquiv_iff (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (hXc : (wildSet X).Countable) (hXne : (wildSet X).Nonempty)
    (hYc : (wildSet Y).Countable) (hYne : (wildSet Y).Nonempty) :
    Nonempty (ContinuousMap.HomotopyEquiv X Y) ↔ Nonempty (wildSet X ≃ₜ wildSet Y)

recall Peano.nonempty_homotopyEquiv_iff_of_weq (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y)
    (hXm : ∃ (Z : Type) (_ : TopologicalSpace Z), Countable Z ∧
      ∃ f : C(X, Z), IsWeakHomotopyEquivalence f) (hXne : (wildSet X).Nonempty)
    (hYm : ∃ (Z : Type) (_ : TopologicalSpace Z), Countable Z ∧
      ∃ f : C(Y, Z), IsWeakHomotopyEquivalence f) (hYne : (wildSet Y).Nonempty) :
    Nonempty (ContinuousMap.HomotopyEquiv X Y) ↔ Nonempty (wildSet X ≃ₜ wildSet Y)

recall Peano.nonempty_homeomorph_wildSet (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (e : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (wildSet X ≃ₜ wildSet Y)

/-- The homeomorphism of Brazas–Fischer 9.15 is the restriction of the homotopy equivalence, with
inverse the restriction of the homotopy inverse. -/
example {X Y : Type} [MetricSpace X] [PathConnectedSpace X] [MetricSpace Y]
    [PathConnectedSpace Y] (hX : CoveringDimLE 1 X) (hY : CoveringDimLE 1 Y)
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (∀ x, (Peano.HomotopyEquiv.wildSetHomeomorph hX hY e x : Y) = e.toFun x) ∧
      ∀ y, ((Peano.HomotopyEquiv.wildSetHomeomorph hX hY e).symm y : X) = e.invFun y :=
  ⟨fun _ => rfl, fun _ => rfl⟩

recall Peano.exists_wildSet_homeomorph (K : Type) [MetricSpace K] [CompactSpace K] [Countable K]
    [Nonempty K] :
    ∃ (X : Type) (_ : MetricSpace X), CompactSpace X ∧ ConnectedSpace X ∧
      LocallyPathConnectedSpace X ∧ CoveringDimLE 1 X ∧ Nonempty (wildSet X ≃ₜ K)

recall Peano.compactSpace_wildSet (X : Type*) [MetricSpace X] [CompactSpace X]
    [LocallyPathConnectedSpace X] : CompactSpace (wildSet X)

#print axioms Peano.compactSpace_wildSet
#print axioms Peano.nonempty_homeomorph_wildSet
#print axioms Peano.HomotopyEquiv.wildSetHomeomorph
#print axioms Peano.nonempty_homotopyEquiv_iff
#print axioms Peano.nonempty_homotopyEquiv_iff_of_weq
#print axioms Peano.exists_wildSet_homeomorph

-- Brazas–Fischer (Peano/BrazasFischer.lean): Lemma 9.17 / Cor 9.18 and the strong form of Thm 9.15.
#check @Peano.apply_eq_of_homotopic_id
#check @Peano.HomotopyEquiv.loopWildSetHomeomorph
#print axioms Peano.apply_eq_of_homotopic_id
#print axioms Peano.HomotopyEquiv.loopWildSetHomeomorph
