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
| `exists_homotopyEquiv_arcReduced` (merges the former `exists_homotopyEquiv_standardForm` and `exists_homotopyEquiv_finiteGraph`) | paper Thm 4.2; Meilstrup 2005, BYU master's thesis (inspected 2026-11-05, `papers/Classifying Homotopy Types…pdf`), **Thm 2.9** (`B(X) ≠ ∅` ⇒ homotopy equivalent to a continuum `Y` with `G(Y) = Y ∖ B(Y)` a disjoint union of a null sequence of open arcs; the paper drops `B(X) ≠ ∅`) and **Cor 2.10** (`B(X) = ∅` ⇒ homotopy equivalent to a bouquet of finitely many, possibly zero, circles). `B(X)`, the bad points (no simply connected neighbourhood), is `loopWildSet X` (`badSet_eq_loopWildSet`, `PeanoPartA/BadPoints.lean`) | a one-dimensional Peano continuum `X` is homotopy equivalent to a one-dimensional Peano continuum `X'` that is in standard form if `loopWildSet X ≠ ∅`, and is a finite graph (an `ArcSystem` with finite `W` and finitely many arcs) if `loopWildSet X = ∅` | Theorem 1.1 "if" (both cases) | 2026-11-05: closures of the arcs are arcs or simple closed curves with end points in `B(Y)`: not in the statement of Thm 2.9, but given by its proof (see below) and implied by the topological-sum reading for Peano continua; the finite-graph case is weaker than the thesis (finite `W`, not a point). Reviewed 2026-11-05: true and implied by the thesis; no counterexample (point, circle, earring, `B(X) = X`) |
| `eda_exists_map_earring` | paper Thm 6.1, Eda 2002 Thm 1.1 (inspected 2026-11-05: target any one-dimensional metric space; same earring; same base-change convention) | a homomorphism `π₁(𝔼) → π₁(X)`, `X` a one-dimensional Peano continuum, agrees on the generators `[ℓₖ]` with `φ_α ∘ g#` for a map `g` and a path `α` | Lemma 6.4, Theorem 1.1 | 2026-11-05: confirmed against Eda's text; a special case of it |
| `exists_nhds_monodromy` | Brazas–Fischer arXiv:1902.08887v2, Prop 9.13 + Remark 9.4(a) + Lemma 9.5 (`H = 1`) | for a path `β` between distinct points of a path-connected one-dimensional metric space there are neighbourhoods `U ∋ x`, `V ∋ y` with `π(c_x, U) ∩ π(β, V) = 1` | Lemma 6.2 (derived), Lemma 6.4, Theorem 1.1, Brazas–Fischer Thm 9.15 (derived), Theorem 1.2 | 2026-11-05: true, literal (what the proof of 9.13(b) shows) |
| `eda_homotopyEquiv_of_homeomorph` | paper Thm 6.6, Eda 2022 Thm 1.1 (checked 2026-11-05 against the 2020 preprint `papers/0dim.pdf`, l.47–50) | one-dimensional Peano continua with homeomorphic **non-empty** zero-dimensional (loop) wild sets are homotopy equivalent | Theorem 1.2 (well-definedness) | 2026-11-05: confirmed against Eda's text; "non-empty" is in his Theorem 1.1 (the paper omits it) |
| `exists_reduced_homotopy`, `isReparam_of_reduced_homotopic` | paper Remark 2.7, Cannon–Conner 2006 Thm 3.9 (inspected 2026-11-05; standing hypotheses compact, path-connected, one-dimensional metric; the image condition is in the proof, and explicit in Constantine–Lafont Thm 2.10) | in a compact path-connected one-dimensional metric space every loop is homotopic, inside its image, to a reduced loop, unique up to increasing reparametrisation | Part A only (Lemma 2.8, Lemma 3.3) | 2026-11-05: confirmed against Cannon–Conner's text; the paper's Remark 2.7 overstates the scope ("metrizable"), though the metrizable form follows by working in compact images |
| `eda_zeroForm` | paper Lemma 3.2, Eda 2016 Lemma 3.6 (inspected 2026-11-05, `papers/fm232-2-01.pdf`; Eda's setting: one-dimensional metric spaces, so the Peano-continuum scope here is stricter), with Hurewicz | direction "⇒" only: a null-homologous essential loop in a one-dimensional Peano continuum has a reduced representative that is a 0-form ("⇐" is proved: `fromPath_mem_commutator_of_isZeroFormCut`) | Part A only (Lemmas 3.3, 3.4, 6.3, general 3.3, `injOn_wildSet_of_paper`) | 2026-11-05: confirmed against Eda's text (Def 3.4, Lemma 3.6; `≡` = up to increasing homeomorphism, as encoded) |
| `exists_simpleClosedCurve` | arXiv:2510.22901 Cor 3.3 and the fact before Def 3.5; also Cannon–Conner Def 3.6 + dendrites contractible (no dimension hypothesis needed) | a path-connected one-dimensional metric space with an essential loop contains a simple closed curve | Part A only (Lemma 6.3) | 2026-11-05: confirmed (two sources) |

## Standard facts (`Peano/Axioms/Standard.lean`)

None at present.

## Former axioms, now theorems

| Former axiom | Now | File |
|---|---|---|
| `isClosed_wildSet` (paper Lemma 2.3, Brazas–Mitra) | `Peano.isClosed_wildSet`, via `isClosed_loopWildSet` and `wildSet_eq_loopWildSet` | `WildSet.lean` |
| `HomotopyEquiv.isWeakHomotopyEquivalence` (Hatcher 1.18, §4.1) | `Peano.HomotopyEquiv.isWeakHomotopyEquivalence`, via change of base point for `πₙ` | `HomotopyEquiv.lean` |
| `coveringDimLE_one_of_interior_eq_empty` (Hurewicz–Wallman, planar sets with empty interior have dimension ≤ 1) | replaced by direct proofs: `coveringDimLE_one_of_finite_frontier` (a compact Hausdorff space with arbitrarily small neighbourhoods of finite frontier has covering dimension ≤ 1), applied to the models (`ModelData.coveringDimLE_model`), the circle, the arc and the earring | `Dimension.lean`, `Models.lean`, `Sanity.lean` |
| `nonempty_homeomorph_wildSet` / `nonempty_homeomorph_loopWildSet` (Brazas–Fischer Thm 9.15) | proved from `exists_nhds_monodromy` by Brazas–Fischer's own argument (Lemma 9.17, Cor 9.18), in the stronger form `HomotopyEquiv.wildSetHomeomorph` (the homotopy equivalence restricts to a homeomorphism); Theorem 1.1 does not use it | `BrazasFischer.lean` |

## Changes from the paper's statements

- **Theorem 4.2: hypothesis `(wildSet X).Nonempty` added.** As quoted, the theorem is false when
  `w(X) = ∅` (a point, a circle, a finite graph). The case `w(X) = ∅` of Theorem 1.1 is handled
  by the case `B(X) = ∅` (Meilstrup Cor 2.10) of `exists_homotopyEquiv_arcReduced`; the formal
  Theorem 1.1 has no non-emptiness hypothesis.
- **Theorem 6.1** is assumed on the generators `[ℓₖ]` only and for Peano continua only.
- **Lemma 6.2** is not an axiom: it is derived from the discrete-monodromy consequence of
  Brazas–Fischer Prop. 9.13, which is what that proposition actually gives (the paper mis-cites it).
- **Theorem 6.6** has "non-empty" added (it is in Eda's Theorem 1.1; the preprint's abstract omits it).
- **Brazas–Fischer Thm 9.15** is not assumed: it is proved from the discrete-monodromy consequence of their Prop. 9.13.
- **The zero-form lemma** is assumed in the direction "⇒" only; "⇐" is proved.

## Notes from reading Meilstrup's thesis (2026-11-05)

- **Bad points.** The thesis works with bad points: `B(X)` is the set of points with no simply
  connected neighbourhood. For a one-dimensional Peano continuum this is `loopWildSet`, hence
  `wildSet`. One inclusion is immediate. For the other, a small path-connected neighbourhood in which
  loops at `x` are null in `X` is simply connected, by Lemma 2.8 and conjugation. Lean:
  `Peano.badSet_eq_loopWildSet`, `Peano.badSet_eq_wildSet` in `PeanoPartA/BadPoints.lean` (it uses
  the Cannon–Conner axioms through Lemma 2.8, so it lives in `PeanoPartA` and the main library does
  not depend on it).
- **Meilstrup Theorem 2.9 and Definition 4.1 (settled).** The statement says only "`G(Y)` a
  disjoint union of a null sequence of (open) arcs" (thesis l.592–593). The proof gives the paper's
  Definition 4.1 (and `IsStandardForm`): `Y` is the quotient of `X` "where each ray `r(x)` is
  identified with the point `b(x) ∈ B(X)`" (l.699–701), and "`G(Y)` a disjoint union of arcs,
  corresponding to those edges in `G(X)` that are not part of any ray `r(x)`" (l.703–707). Every
  vertex `x` of the locally finite graph `G(X)` (Theorem 2.7) lies on its ray, so `G(Y)` is the
  union of the images of open edges, each open in `Y` (a topological sum), and the two end vertices
  of each such edge go to points `b(·)` of `B(Y)`: the closure is an arc, or a simple closed curve
  when both go to the same point. The map `g` labels "an end third of `a`" by "the corresponding
  endpoint of `b`" (l.713–715), and `f ∘ g` "slides the end thirds to their endpoints in `B(Y)`"
  (l.721–722); the proof ends with "`f` maps `B(X)` homeomorphically onto `B(Y)`" (l.787–788).
  Independently, in a Peano continuum each end of an open arc that is open in the space converges
  (otherwise local connectedness fails at a limit point of the end), so the closure condition
  follows from the topological-sum reading of the statement. No weakening was needed; a weakening
  to "an `ArcSystem` with `W = wildSet`" would in any case be equivalent to `IsStandardForm`, given
  `isClosed_wildSet`.
- **The two structure axioms** (standard form, finite graphs) both have Meilstrup as their source
  (Thm 2.9 and Cor 2.10). They are now merged into one axiom, `exists_homotopyEquiv_arcReduced`.
- **Reduced loops.** The thesis's Lemma 2.1 restates Cannon–Conner's reduced loops for
  one-dimensional Peano continua, citing Cannon–Conner.

## Notes from reading the cited papers (2026-11-05)

All cited sources have now been read (Meilstrup 2005, Eda 2002, 2016, 2022 (2020 preprint),
Cannon–Conner 2006, Brazas–Fischer 2020). Every cited axiom is confirmed against its source; no
statement changed. Findings:
- **Paper misquotes, confirmed against the sources:**
  - Theorem 4.2 omits Meilstrup's "`B(X) ≠ ∅`".
  - Theorem 6.6 omits Eda's "non-empty". The 2020 preprint's abstract also omits it, a plausible
    origin of the slip.
  - Definition 3.1 asks for exact equality of paired pieces, where Eda's Definition 3.4 has `≡`
    (equality up to an increasing homeomorphism).
  - Remark 2.7 states Cannon–Conner Theorem 3.9 for metrizable spaces; Cannon–Conner assume compact
    path-connected spaces. The metrizable form is still true.
  - Lemma 6.2 cites Brazas–Fischer Prop 9.13 for a consequence of it.
- **Scopes of our axioms, narrower than the sources:**
  - Eda 2002 Theorem 1.1 allows any one-dimensional metric target. By Eda's Lemma 3.15, our
    generator form is equivalent to the full theorem.
  - Eda 2016 Lemma 3.6 holds for one-dimensional metric spaces. Cannon–Conner Theorem 6.1 is a second
    source for the zero-form lemma, for one-dimensional Hausdorff spaces.
- **Not derivable from Cannon–Conner:** the monodromy axiom, which rests on Brazas–Fischer and their
  earlier Lemma 3.11 (J. Topol. Anal. 2020).
