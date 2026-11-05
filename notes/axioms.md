# Axioms of the `Peano` formalisation (audit table)

Every axiom is in `Peano/Axioms/`, and `Peano/Audit/Axioms.lean` prints each one in full. Check that
none exists elsewhere with `grep -rn '^axiom' Peano`. The "used by" column comes from the
`#print axioms` lines in `Peano/Audit/*.lean`. Adversarial reviews: `checks/axioms-review.md`
(first set) and `checks/reviews-2026-11-05.md`.

Wild sets. The paper's Definition 2.2 (`wildSet`, through fully essential maps from the earring) and
the definition of its introduction and of the cited sources (`loopWildSet`: every neighbourhood
contains an essential loop based at the point; for locally path-connected spaces, the points at
which the space is not semilocally simply connected) agree for metric spaces. This is proved
(`wildSet_eq_loopWildSet`), so axioms quoting sources are stated with `loopWildSet`, literally.

## Cited results (`Peano/Axioms/Cited.lean`)

| Lean name | Source | Statement (informal) | Used by | Review |
|---|---|---|---|---|
| `exists_homotopyEquiv_standardForm` | paper Thm 4.2, Meilstrup 2005, BYU master's thesis, **Thm 2.9** (inspected 2026-11-05, `papers/Classifying Homotopy Types…pdf`): for `B(X) ≠ ∅` there is a homotopy equivalent `Y` with `G(Y) = Y ∖ B(Y)` a disjoint union of a null sequence of open arcs, and `f` maps `B(X)` homeomorphically onto `B(Y)`. The thesis has the hypothesis `B(X) ≠ ∅` that the paper drops | a one-dimensional Peano continuum **with non-empty wild set** is homotopy equivalent to one in standard form | Theorem 1.1 "if" | true *with* `w ≠ ∅` (false without) |
| `exists_homotopyEquiv_finiteGraph` | Meilstrup 2005, **Cor 2.10** (`B(X) = ∅` ⇒ homotopy equivalent to a bouquet of finitely many, possibly zero, circles); also Brazas–Pavešić arXiv:2510.22901 Thm 3.9, Cor 3.3 | a one-dimensional Peano continuum with empty (loop) wild set is homotopy equivalent to a finite graph (an `ArcSystem` with finite `W` and finitely many arcs) | Theorem 1.1 "if", case `w = ∅` | 2026-11-05: true, literal |
| `eda_exists_map_earring` | paper Thm 6.1, Eda 2002 Thm 1.1 (inspected 2026-11-05: target any one-dimensional metric space; same earring; same base-change convention) | a homomorphism `π₁(𝔼) → π₁(X)`, `X` a one-dimensional Peano continuum, agrees on the generators `[ℓₖ]` with `φ_α ∘ g#` for a map `g` and a path `α` | Lemma 6.4, Theorem 1.1 | 2026-11-05: confirmed against Eda's text; a special case of it |
| `exists_nhds_monodromy` | Brazas–Fischer arXiv:1902.08887v2, Prop 9.13 + Remark 9.4(a) + Lemma 9.5 (`H = 1`) | for a path `β` between distinct points of a path-connected one-dimensional metric space there are neighbourhoods `U ∋ x`, `V ∋ y` with `π(c_x, U) ∩ π(β, V) = 1` | Lemma 6.2 (derived), Lemma 6.4, Theorem 1.1, Brazas–Fischer Thm 9.15 (derived), Theorem 1.2 | 2026-11-05: true, literal (what the proof of 9.13(b) shows) |
| `eda_homotopyEquiv_of_homeomorph` | paper Thm 6.6, Eda 2022 (abstract; text not inspected) | one-dimensional Peano continua with homeomorphic **non-empty** zero-dimensional (loop) wild sets are homotopy equivalent | Theorem 1.2 (well-definedness) | 2026-11-05: true with "non-empty" (the paper omits it) |
| `exists_reduced_homotopy`, `isReparam_of_reduced_homotopic` | paper Remark 2.7, Cannon–Conner 2006 Thm 3.9 (checked against Constantine–Lafont arXiv:1209.3709 Thm 2.10) | in a compact path-connected one-dimensional metric space every loop is homotopic, inside its image, to a reduced loop, unique up to increasing reparametrisation | Part A only (Lemma 2.8, Lemma 3.3) | 2026-11-05: true, scope narrower than the paper |
| `eda_zeroForm` | paper Lemma 3.2, Eda 2016 Lemma 3.6 (inspected 2026-11-05, `papers/fm232-2-01.pdf`; Eda's setting: one-dimensional metric spaces, so the Peano-continuum scope here is stricter), with Hurewicz | direction "⇒" only: a null-homologous essential loop in a one-dimensional Peano continuum has a reduced representative that is a 0-form ("⇐" is proved: `fromPath_mem_commutator_of_isZeroFormCut`) | Part A only (Lemmas 3.3, 3.4, 6.3, general 3.3, `injOn_wildSet_of_paper`) | 2026-11-05: confirmed against Eda's text (Def 3.4, Lemma 3.6; `≡` = up to increasing homeomorphism, as encoded) |
| `exists_simpleClosedCurve` | arXiv:2510.22901 Cor 3.3 and the fact before Def 3.5 | a path-connected one-dimensional metric space with an essential loop contains a simple closed curve | Part A only (Lemma 6.3) | 2026-11-05: true |

## Standard facts (`Peano/Axioms/Standard.lean`)

| Lean name | Source | Statement | Used by | Review |
|---|---|---|---|---|
| `coveringDimLE_one_of_interior_eq_empty` | Hurewicz–Wallman, *Dimension Theory*, Thm IV.3 and Thm V.8 | a compact subset of ℝ² with empty interior has covering dimension ≤ 1 | Theorem 1.2 (surjectivity: the models are one-dimensional); sanity checks | 2026-11-05: true (even without compactness) |

## Former axioms, now theorems

| Former axiom | Now | File |
|---|---|---|
| `isClosed_wildSet` (paper Lemma 2.3, Brazas–Mitra) | `Peano.isClosed_wildSet`, via `isClosed_loopWildSet` and `wildSet_eq_loopWildSet` | `WildSet.lean` |
| `HomotopyEquiv.isWeakHomotopyEquivalence` (Hatcher 1.18, §4.1) | `Peano.HomotopyEquiv.isWeakHomotopyEquivalence`, via change of base point for `πₙ` | `HomotopyEquiv.lean` |
| `nonempty_homeomorph_wildSet` / `nonempty_homeomorph_loopWildSet` (Brazas–Fischer Thm 9.15) | proved from `exists_nhds_monodromy` by Brazas–Fischer's own argument (Lemma 9.17, Cor 9.18), in the stronger form `HomotopyEquiv.wildSetHomeomorph` (the homotopy equivalence restricts to a homeomorphism); Theorem 1.1 does not use it | `BrazasFischer.lean` |

## Changes from the paper's statements

- **Theorem 4.2: hypothesis `(wildSet X).Nonempty` added.** As quoted, the theorem is false when
  `w(X) = ∅` (a point, a circle, a finite graph). The case `w(X) = ∅` of Theorem 1.1 is handled
  by the finite-graph axiom instead; the formal Theorem 1.1 has no non-emptiness hypothesis.
- **Theorem 6.1** is assumed on the generators `[ℓₖ]` only and for Peano continua only.
- **Lemma 6.2** is not an axiom: it is derived from the discrete-monodromy consequence of
  Brazas–Fischer Prop. 9.13, which is what that proposition actually gives (the paper mis-cites it).
- **Theorem 6.6** has "non-empty" added (it is in Eda's abstract).
- **Brazas–Fischer Thm 9.15** is not assumed: it is proved from the discrete-monodromy consequence of their Prop. 9.13.
- **The zero-form lemma** is assumed in the direction "⇒" only; "⇐" is proved.

## Notes from reading Meilstrup's thesis (2026-11-05)

- **Bad points.** The thesis works with bad points: `B(X)` is the set of points with no simply
  connected neighbourhood. For a one-dimensional Peano continuum this is `loopWildSet`, hence
  `wildSet`. One inclusion is immediate. For the other, a small path-connected neighbourhood in which
  loops at `x` are null in `X` is simply connected, by Lemma 2.8 and conjugation. This is not yet a
  Lean lemma; it would use the Cannon–Conner axioms through Lemma 2.8.
- **To check.** Theorem 2.9 says "`G(Y)` is a disjoint union of a null sequence of open arcs". The
  paper's Definition 4.1, and `IsStandardForm`, also ask that the closure of each arc be an arc or a
  simple closed curve with its end points in `w(Y)`. The end points lying in `B(Y)` follows if
  "disjoint union" means topological sum. That the closures are arcs or circles is what the thesis'
  construction gives (vertices retracted along rays into `B(X)`), but its statement does not say so
  explicitly.
- **The two structure axioms** (standard form, finite graphs) both have Meilstrup as their source
  (Thm 2.9 and Cor 2.10). They could be merged into one axiom citing the thesis.
- **Reduced loops.** The thesis's Lemma 2.1 restates Cannon–Conner's reduced loops for
  one-dimensional Peano continua, citing Cannon–Conner.
