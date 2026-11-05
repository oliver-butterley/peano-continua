# Lemma map: paper ↔ Lean

The Lean code is the `Peano` library (`Peano/`), built with `lake build`. Axioms are
listed in `axioms.md`.

Status:
- `proved`: no `sorry`.
- `informal`: not formalised, checked in `checks/`.

"Standard three" means `propext`, `Classical.choice` and `Quot.sound`.

| Paper | Lean declaration | File | Status | Axioms (`#print axioms`) |
|---|---|---|---|---|
| Def 2.1 | `Peano.FullyEssential` | `Defs.lean` | definition | — |
| Def 2.2 | `Peano.wildSet` | `Defs.lean` | definition | — |
| L2.3 (cited) | `Peano.isClosed_wildSet` | `Axioms/Cited.lean` | axiom | — |
| Def 2.4 | `Peano.IsWeakHomotopyEquivalence` | `Defs.lean` | definition | — |
| L2.5, L2.8, L3.3, L3.4 | — | — | informal (`checks/A.md`) | — |
| Def 4.1 | `Peano.IsStandardForm`, abstracted as `Peano.ArcSystem` | `Defs.lean`, `StandardForm.lean` | definition | — |
| T4.2 (cited) | `Peano.exists_homotopyEquiv_standardForm` | `Axioms/Cited.lean` | axiom, hypothesis `w ≠ ∅` added | — |
| L4.3 | `Peano.ArcSystem.tendsto_diam_closedArc` | `StandardForm.lean` | proved | standard three |
| C4.4 | `Peano.ArcSystem.eventually_closedArc_subset` | `StandardForm.lean` | proved | standard three |
| L4.5 | `Peano.ArcSystem.isOpen_iff_localCondition` | `StandardForm.lean` | proved | standard three |
| §5 construction | `Peano.ArcSystem.Coarse`, `Peano.ArcSystem.q` | `Coarsify.lean` | definition | — |
| R5.1 | `Peano.ArcSystem.countable_coarse` | `Coarsify.lean` | proved | standard three |
| L5.2 | `Peano.ArcSystem.isOpenMap_q` | `Coarsify.lean` | proved | standard three |
| L5.4 | `Peano.ArcSystem.exists_extension_preimage_eq` | `Coarsify.lean` | proved | standard three |
| L5.4′ (repair, `checks/C.md`) | `Peano.ArcSystem.exists_extension_interior` | `Coarsify.lean` | proved | standard three |
| L5.5 | `Peano.ArcSystem.exists_lift` | `Coarsify.lean` | proved | standard three |
| C5.6 (deduction) | `Peano.isSerreFibration_of_hasCubeLifting`, `Peano.isWeakHomotopyEquivalence_of_hasCubeLifting` | `WeakEquiv.lean` | proved | standard three |
| C5.6 | `Peano.ArcSystem.isSerreFibration_q`, `Peano.ArcSystem.isWeakHomotopyEquivalence_q` | `Main.lean` | proved | standard three |
| — (standard) | `Peano.IsWeakHomotopyEquivalence.comp` | `WeakEquiv.lean` | proved | standard three |
| — (standard) | `Peano.HomotopyEquiv.isWeakHomotopyEquivalence` | `Axioms/Standard.lean` | axiom | — |
| L6.3, L6.4, R6.5 | — | — | informal (`checks/D.md`) | — |
| T1.1, "if", standard form | `Peano.exists_countable_weq_of_standardForm` | `Main.lean` | proved | standard three + `isClosed_wildSet` |
| T1.1, "if", `w(X) ≠ ∅` | `Peano.exists_countable_weq` | `Main.lean` | proved | standard three + `isClosed_wildSet`, `exists_homotopyEquiv_standardForm`, `nonempty_homeomorph_wildSet`, `HomotopyEquiv.isWeakHomotopyEquivalence` |
| T1.1, "only if" | — | — | informal (`checks/D.md`) | — |
| T1.2 | — | — | informal (`checks/D.md`) | — |

The audit files (`Peano/Audit/`) restate the key statements with `recall` and print their axioms:
- `Thm1_1.lean`: Theorem 1.1, both layers.
- `Cor5_6.lean`: Lemma 5.5 and Corollary 5.6.
- `Lemma4_5.lean`: Lemmas 4.3 and 4.5, Remark 5.1 and Lemma 5.2.
- `Axioms.lean`: every axiom.
