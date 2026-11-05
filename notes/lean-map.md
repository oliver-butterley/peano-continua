# Lemma map: paper ↔ Lean

The Lean code is the `Peano` library (`Peano/`), built with `lake build`. Axioms are listed in
`axioms.md`.

Row labels: Def = definition, L = lemma, R = remark, T = theorem, C = corollary (paper numbering).

Status:
- `proved`: no `sorry`.
- `axiom`: a cited result, assumed (see `axioms.md`).

"Standard three" means `propext`, `Classical.choice` and `Quot.sound`. Axiom names below omit the
`Peano.` prefix. The axioms of the cited results used by Theorem 1.1 are abbreviated:
**M** = `exists_homotopyEquiv_arcReduced` (Meilstrup, Theorem 2.9 and Corollary 2.10; standard
form, or a finite graph when the wild set is empty), **E1** = `eda_exists_map_earring` (Eda 2002), **BFm** = `exists_nhds_monodromy`
(Brazas–Fischer, discrete monodromy).

## §2–3 (Part A)

| Paper | Lean declaration | File | Status | Axioms |
|---|---|---|---|---|
| Def 2.1 | `FullyEssential` | `Defs.lean` | definition | — |
| Def 2.2 | `wildSet` | `Defs.lean` | definition | — |
| wild points (introduction) | `loopWildSet` | `LoopWildSet.lean` | definition | — |
| remark after Def 2.2 | `wildSet_eq_loopWildSet` (first countable) | `WildSet.lean` | proved | standard three |
| L2.3 | `isClosed_wildSet` (metric spaces), `isClosed_loopWildSet` (any locally path-connected space) | `WildSet.lean` | proved (was an axiom) | standard three |
| Def 2.4 | `IsWeakHomotopyEquivalence` | `Defs.lean` | definition | — |
| L2.5 | `image_wildSet_subset`, `image_loopWildSet_subset`, `mapsTo_wildSet` | `WildSet.lean`, `OnlyIf.lean` | proved | standard three |
| Def 2.6 | `IsReducedPath` (with `a < b`, `checks/A.md` A-2.6-1) | `Reduced.lean` | definition | — |
| R2.7 (cited) | `exists_reduced_homotopy`, `isReparam_of_reduced_homotopic` | `Axioms/Cited.lean` | axiom | — |
| L2.8 | `fundamentalGroup_map_val_injective` (any one-dimensional metric space) | `PartA.lean` | proved | R2.7 axioms |
| Def 3.1 | `IsZeroFormCut` | `Reduced.lean` | definition | — |
| L3.2 (cited, "⇒"; "⇐" proved) | `eda_zeroForm`, `fromPath_mem_commutator_of_isZeroFormCut` | `Axioms/Cited.lean` | axiom | — |
| L3.3 (general, A-3.3-1 closed) | `fromPath_mem_commutator_of_sum_eq_zero`, core `homologyClass_eq_zero_of_sum_eq_zero` | `Lemma3_3General.lean` | proved | R2.7 axioms, `eda_zeroForm` |
| H₁ (genuine singular homology, via Tau Ceti's degree-one Hurewicz) | `singularH1`, `h1Class`, `h1Class_eq_zero_iff` (↔ commutator), `isHomologous_iff_h1Class_eq`, `exists_finset_sum_h1Class` | `PeanoPartA/SingularH1*.lean` | definitions; proved | standard three |
| H₁ working model (abelianised π₁) | `IsHomologous`, `homologyClass`, `fromPath_mem_commutator_of_isZeroFormCut` (0-forms are null-homologous) | `Homology.lean` | definitions; proved | standard three |
| L3.3 (paper's statement: H₁(A) → H₁(X) injective, any A) | `singularHomologyMap_val_injective` | `PeanoPartA/SingularH1Lemmas.lean` | proved | R2.7 axioms, `eda_zeroForm` |
| L3.4, L6.3 in singular H₁ | `h1Class_ne_of_disjoint(_of_or)`, `exists_earringMap_h1Class_ne_zero` | `PeanoPartA/SingularH1Lemmas.lean` | proved | as the abelianised versions |
| L3.3 (path component of the base point) | `abelianization_map_val_injective` (Peano continua) | `PartA.lean` | proved | R2.7 axioms, `eda_zeroForm` |
| L3.4 (no reducedness needed) | `not_isHomologous_of_disjoint` (Peano continua) | `PartA.lean` | proved | R2.7 axioms, `eda_zeroForm` |
| L6.3 (corrected, `checks/D.md`) | `exists_earringMap_not_mem_commutator` (Peano continua) | `PartA.lean` | proved | the above and `exists_simpleClosedCurve` |
| L6.4, the paper's own proof | `injOn_wildSet_of_paper` | `Lemma6_4Paper.lean` | proved (a check of §3; the main theorems use `injOn_wildSet`) | Part A axioms, E1, BFm |

## §4–5

| Paper | Lean declaration | File | Status | Axioms |
|---|---|---|---|---|
| Def 4.1 | `IsStandardForm`, abstracted as `ArcSystem` | `Defs.lean`, `Arcs.lean` | definition | — |
| T4.2 (cited) | `exists_homotopyEquiv_arcReduced` (merged with the finite-graph case, Meilstrup Cor 2.10) | `Axioms/Cited.lean` | axiom; the standard-form part assumes `w ≠ ∅`, as in Meilstrup Thm 2.9 | — |
| Meilstrup's bad points | `badSet`, `badSet_eq_loopWildSet`, `badSet_eq_wildSet` | `PeanoPartA/BadPoints.lean` | proved | Cannon–Conner axioms (Part A) |
| L4.3 | `ArcSystem.tendsto_diam_closedArc` | `StandardForm.lean` | proved | standard three |
| C4.4 | `ArcSystem.eventually_closedArc_subset` | `StandardForm.lean` | proved | standard three |
| L4.5 | `ArcSystem.isOpen_iff_localCondition` | `StandardForm.lean` | proved | standard three |
| §5 construction | `ArcSystem.Coarse`, `ArcSystem.q` | `Coarsify.lean` | definition | — |
| R5.1 | `ArcSystem.countable_coarse` (separable spaces), `ArcSystem.finite_coarse` | `Coarsify.lean` | proved | standard three |
| L5.2 | `ArcSystem.isOpenMap_q` | `Coarsify.lean` | proved | standard three |
| L5.4 | `ArcSystem.exists_extension_preimage_eq` | `Coarsify.lean` | proved | standard three |
| L5.4′ (repair, `checks/C.md`) | `ArcSystem.exists_extension_interior` | `Coarsify.lean` | proved | standard three |
| L5.5 | `ArcSystem.exists_lift` (null arcs; no compactness) | `Coarsify.lean` | proved | standard three |
| C5.6 | `ArcSystem.isSerreFibration_q`, `ArcSystem.isWeakHomotopyEquivalence_q`; general `ArcSystem.countable_weq_q` | `WeakEquiv.lean`, `Main.lean` | proved | standard three |
| — (standard) | `HomotopyEquiv.isWeakHomotopyEquivalence` (change of base point for `πₙ`) | `HomotopyEquiv.lean` | proved (was an axiom) | standard three |

## §6 and the main theorems

| Paper | Lean declaration | File | Status | Axioms |
|---|---|---|---|---|
| T6.1 (cited) | `eda_exists_map_earring` (on generators) | `Axioms/Cited.lean` | axiom | — |
| L6.2 | `eq_of_homotopic_conj`, `eq_of_fullyEssential_homotopic_conj` | `OnlyIf.lean` | proved from Brazas–Fischer | BFm |
| L6.4 | `injOn_wildSet`, `mk_wildSet_le` (homology-free proof; `X` a Peano continuum, `Y` any space) | `OnlyIf.lean` | proved | E1, BFm |
| R6.5 | `Remark6_5.remark6_5`, `not_surjOn_wildSet_earringProdHomotopyEquiv`, `not_countable_wildSet_earring_prod` | `Remark6_5.lean` | proved (`⊇` of the paper's `w(𝔼 × I) = {b₀} × I`, which suffices) | standard three |
| T1.1 "if", standard form | `exists_countable_weq_of_standardForm` | `Main.lean` | proved | standard three |
| T1.1 "if", `w = ∅` (missed by the paper) | `exists_finite_weq_of_loopWildSet_eq_empty` | `Main.lean` | proved | M |
| T1.1 "if" | `exists_countable_weq` | `Main.lean` | proved | M, E1, BFm |
| T1.1 "only if" | `countable_wildSet_of_weq` | `OnlyIf.lean` | proved | E1, BFm |
| T1.1 | `exists_countable_weq_iff`, `exists_countable_weq_iff_loopWildSet` | `Thm1_1.lean` | proved | M, E1, BFm |
| T6.6 (cited) | `eda_homotopyEquiv_of_homeomorph` ("non-empty" added) | `Axioms/Cited.lean` | axiom | — |
| [5, Thm 9.15] (cited by the paper) | `HomotopyEquiv.wildSetHomeomorph`, `nonempty_homeomorph_wildSet`, `apply_eq_of_homotopic_id` (Lemma 9.17/Cor 9.18) | `BrazasFischer.lean` | proved | BFm |
| T1.2 as stated | the canonical map is not a bijection: `Sanity.thm1_2_counterexample` (point, circle), `Sanity.thm1_2_counterexample_dim_one` (circle, arc: dimension exactly 1); T6.6 without "non-empty" is false: `Sanity.not_forall_nonempty_homotopyEquiv_iff_wildSet` | `Sanity.lean` | proved | standard three |
| T1.2 corrected, injectivity | `nonempty_homotopyEquiv_iff`, `nonempty_homotopyEquiv_iff_of_weq`, `compactSpace_wildSet` | `Thm1_2.lean` | proved | BFm, `eda_homotopyEquiv_of_homeomorph` |
| T1.2 corrected, surjectivity (models `A_λ`) | `exists_wildSet_homeomorph`, `exists_model`; one-dimensionality `ModelData.coveringDimLE_model` via `coveringDimLE_one_of_finite_frontier` | `Thm1_2.lean`, `Models.lean`, `Dimension.lean` | proved | standard three |
| T1.2, ordinal phrasing (Mazurkiewicz–Sierpiński) | — | — | not formalised | — |

## Sanity checks (`Sanity.lean`)

- `not_isWeakHomotopyEquivalence_addCircle_const`: weak homotopy equivalence is not trivial.
- `not_coveringDimLE_zero_unitInterval`: `CoveringDimLE` is not trivial.
- `exists_peano_wildSet_not_countable`, `exists_no_countable_model`: earrings attached at the
  rationals of `[0, 1]` give a one-dimensional Peano continuum with uncountable wild set, hence no
  countable weak model (an instance of the "only if" direction).
- `wildSet_earring`: `w(𝔼) = {b₀}`; `earring_peano`: the earring satisfies the hypotheses of
  Theorem 1.1.
- `exists_countable_weq_of_wildSet_nonempty`: Theorem 1.1 has instances with `w ≠ ∅`.

## Audit files (`Peano/Audit/`)

- `PartA.lean`: Lemmas 2.8, 3.3 (both forms), 3.4, 6.3, 0-forms, the paper's proof of Lemma 6.4.

- `Thm1_1.lean`: Theorem 1.1, Lemma 6.4.
- `Thm1_2.lean`: corrected Theorem 1.2.
- `WildSet.lean`: Lemmas 2.3, 2.5, 6.2, `wildSet_eq_loopWildSet`, `earringBase_mem_wildSet`.
- `Cor5_6.lean`: Lemma 5.5, Corollary 5.6 and the general arc-system theorems.
- `Lemma4_5.lean`: Lemmas 4.3, 4.5, Remark 5.1, Lemma 5.2.
- `Sanity.lean`: the sanity theorems.
- `Defs.lean`: prints every definition the main statements depend on.
- `Axioms.lean`: every axiom.
