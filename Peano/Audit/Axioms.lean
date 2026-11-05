module

import Peano

/-!
# Audit: every axiom of the formalisation

Prints each axiom of `Peano/Axioms/Cited.lean` and `Peano/Axioms/Standard.lean` with its full
statement. This list must match the table in `notes/axioms.md`; `grep -rn '^axiom' Peano` must find
axioms only under `Peano/Axioms/`.
-/

-- Cited from the literature (`Peano/Axioms/Cited.lean`).
/--
info: axiom Peano.exists_homotopyEquiv_arcReduced : ∀ (X : Type) [inst : MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyPathConnectedSpace X],
  Peano.CoveringDimLE 1 X →
    ∃ X' x,
      CompactSpace X' ∧
        ConnectedSpace X' ∧
          LocallyPathConnectedSpace X' ∧
            Peano.CoveringDimLE 1 X' ∧
              Nonempty (ContinuousMap.HomotopyEquiv X X') ∧
                ((Peano.loopWildSet X).Nonempty → Peano.IsStandardForm X') ∧
                  (Peano.loopWildSet X = ∅ → ∃ S, S.W.Finite ∧ Finite S.ι)
-/
#guard_msgs in
#print Peano.exists_homotopyEquiv_arcReduced
/--
info: axiom Peano.eda_exists_map_earring : ∀ (X : Type) [inst : MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyPathConnectedSpace X],
  Peano.CoveringDimLE 1 X →
    ∀ (x₀ : X) (ψ : FundamentalGroup (↑Peano.earring) Peano.earringBase →* FundamentalGroup X x₀),
      ∃ g α,
        ∀ (k : ℕ),
          ψ (FundamentalGroup.fromPath ⟦Peano.earringLoop k⟧) =
            FundamentalGroup.fromPath ⟦(α.symm.trans ((Peano.earringLoop k).map ⋯)).trans α⟧
-/
#guard_msgs in
#print Peano.eda_exists_map_earring
/--
info: axiom Peano.exists_nhds_monodromy : ∀ (X : Type) [inst : MetricSpace X] [PathConnectedSpace X],
  Peano.CoveringDimLE 1 X →
    ∀ {x y : X},
      x ≠ y →
        ∀ (β : Path x y),
          ∃ U ∈ nhds x,
            ∃ V ∈ nhds y,
              ∀ (γ : Path x x) (δ : Path y y),
                Set.range ⇑γ ⊆ U → Set.range ⇑δ ⊆ V → γ.Homotopic ((β.trans δ).trans β.symm) → γ.Homotopic (Path.refl x)
-/
#guard_msgs in
#print Peano.exists_nhds_monodromy
/--
info: axiom Peano.eda_homotopyEquiv_of_homeomorph : ∀ (X Y : Type) [inst : MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyPathConnectedSpace X] [inst_4 : MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y]
  [LocallyPathConnectedSpace Y],
  Peano.CoveringDimLE 1 X →
    Peano.CoveringDimLE 1 Y →
      (Peano.loopWildSet X).Nonempty →
        (Peano.loopWildSet Y).Nonempty →
          ZeroDimensionalSpace ↑(Peano.loopWildSet X) →
            ZeroDimensionalSpace ↑(Peano.loopWildSet Y) →
              ∀ (φ : ↑(Peano.loopWildSet X) ≃ₜ ↑(Peano.loopWildSet Y)), Nonempty (ContinuousMap.HomotopyEquiv X Y)
-/
#guard_msgs in
#print Peano.eda_homotopyEquiv_of_homeomorph

-- Standard facts missing from Mathlib (`Peano/Axioms/Standard.lean`): none at present.
