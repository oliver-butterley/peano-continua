# Structure of Brazas–Pavešić, "Countable models of one-dimensional Peano continua"

arXiv:2610.35875v1 [math.GN], 10 Aug 2026, 14 pages. Local copy: `papers/2610.35875.pdf` and
`papers/2610.35875.txt` (gitignored).

A *Peano continuum* is a connected, locally path-connected, compact metrizable space. The *wild
set* `w(X)` is the set of points `x` at which there is a fully essential map `(𝔼, b₀) → (X, x)` from
the infinite earring `𝔼`, that is, a map that is essential on every circle (Definitions 2.1–2.2). A
*weak homotopy equivalence* induces a bijection on `π₀` and isomorphisms on every `πₙ`, at every
basepoint (Definition 2.4).

Labels: Def = definition, L = lemma, R = remark, T = theorem, C = corollary.

## Main results

- **Theorem 1.1.** Let `X` be a one-dimensional Peano continuum. There is a countable space `Y` and
  a weak homotopy equivalence `X → Y` if and only if `w(X)` is countable.
- **Theorem 1.2.** There is a canonical bijection between homeomorphism types of compact countable
  ordinals and homotopy types of one-dimensional Peano continua that admit a weak homotopy
  equivalence to a countable space.

## Results cited from the literature (not proved in the paper)

| Paper | Source | Statement |
|---|---|---|
| L2.3 | [6] Brazas–Mitra, arXiv:2505.23665 | `X` locally path-connected and first countable ⇒ `w(X)` closed |
| R2.7 | [8] Cannon–Conner 2006, Thm 3.9 | one-dimensional metrizable: every loop is homotopic, inside its own image, to a reduced loop; reduced representatives are unique up to reparametrisation |
| L2.8 | [8] Cannon–Conner, Cor 3.3 | subspace inclusions of one-dimensional metrizable spaces are π₁-injective (the paper also gives a proof from R2.7) |
| L3.2 | [13] Eda 2016, Lemma 3.6 | zero-form lemma: an essential loop is null-homologous iff its reduced representative is a 0-form |
| T4.2 | [18] Meilstrup 2005 (Master's thesis) | every one-dimensional Peano continuum is homotopy equivalent to one in standard form |
| T6.1 | [10] Eda 2002, Thm 1.1 | every homomorphism `π₁(𝔼) → π₁(X)` is induced by a map, up to change of basepoint |
| L6.2 | [5] Brazas–Fischer 2020, Prop 9.13 | two fully essential maps conjugate by a path `α` force `α` to be a loop |
| T6.6 | [12] Eda 2022 | one-dimensional Peano continua with zero-dimensional wild sets are homotopy equivalent iff the wild sets are homeomorphic |
| in proof of T1.2 | [5] Brazas–Fischer 2020, Thm 9.15 | a homotopy equivalence of one-dimensional Peano continua restricts to a homeomorphism of wild sets |
| in proof of T1.2 | folklore (Mazurkiewicz–Sierpiński) | a countable compact metrizable space is homeomorphic to a countable ordinal |

## Results proved in the paper, by part

**Part A — §2–3: wild sets, π₁ and H₁ of one-dimensional spaces.**
- L2.5: π₁-injective maps send `w(X)` into `w(Y)`.
- L2.8: proof from R2.7.
- L3.3: subspace inclusions are injective on `H₁` (from L3.2 and R2.7).
- L3.4: disjoint reduced loops, one not null-homologous, are not homologous (from L3.2 and R2.7).

**Part B — §4: standard form.**
- Def 4.1: `X \ w(X)` is a disjoint union of open arcs `Oₙ` whose closures are arcs or simple closed
  curves, with ends in `w(X)`.
- T4.2: cited.
- L4.3: `diam Oₙ → 0`.
- C4.4: if the ends `a_{nᵢ}` converge to `x`, the closures of `O_{nᵢ}` eventually lie in any
  neighbourhood of `x`.
- L4.5: openness in `X` is characterised by conditions (1)–(3).

**Part C — §5: coarsification.**
- The construction: `Oₙ = hₙ((0,1))`; `Bₙ = hₙ((0,½))`, `Cₙ = {hₙ(½)}`, `Dₙ = hₙ((½,1))`. `𝒞X` is
  the quotient that collapses each `Bₙ`, `Cₙ`, `Dₙ` to a point, and `q : X → 𝒞X` is the quotient
  map.
- R5.1: `𝒞X` is countable if `w(X)` is.
- L5.2: `q` is open.
- R5.3: closures and boundaries of `{bₙ}` and `{dₙ}`.
- L5.4: perfectly normal extension.
- L5.5: the lifting lemma for `q`, relative to a closed `A ⊆ B` with `B` locally path-connected and
  metrizable.
- C5.6: `q` is a Serre fibration and a weak homotopy equivalence (L5.5 for `(Iⁿ⁺¹, Iⁿ×0)` and
  `(Iⁿ⁺¹, ∂Iⁿ⁺¹)`).

**Part D — §6: main proofs.**
- L6.3: at a wild point there is a map from `𝔼` whose loops are all non-zero in `H₁` (from L3.3).
- L6.4: if `f` induces a π₁-isomorphism, then `f|w(X)` is injective (from L2.5, L3.4, L6.3, T6.1,
  L6.2).
- R6.5.
- Proof of Theorem 1.1:
  - "only if": L6.4.
  - "if": T4.2 and L6.4, applied to a homotopy inverse, give the reduction to standard form;
    then C5.6 and R5.1.
- Proof of Theorem 1.2: models `A_λ`; injectivity from [5, Thm 9.15]; surjectivity from Theorem 1.1,
  the ordinal fact and T6.6.

## Dependency graph (proved results only)

```
R2.7 ─► L2.8
L3.2, R2.7 ─► L3.3 ─► L6.3 ─┐
L3.2, R2.7 ─► L3.4 ─────────┼─► L6.4 ─► T1.1 (only if)
L2.5, T6.1, L6.2 ───────────┘     │
                                  ▼
T4.2 ──────────────────────────► T1.1 (if) ◄── C5.6 ◄── L5.5 ◄── L5.2 ◄── L4.5 ◄── C4.4 ◄── L4.3
                                         ◄── R5.1            ◄── L5.4, R5.3, C4.4
T1.1, T6.6, [5, Thm 9.15], ordinal fact ─► T1.2
```

## Formalisation scope

Decision of 2026-10-28: Lean covers Parts B and C and the "if" direction of Theorem 1.1. Extended on
2026-11-05 to the whole paper (Parts A–D, both directions of Theorem 1.1, corrected Theorem 1.2,
Remark 6.5); see `README.md` (status, and what is not formalised) and `lean-map.md`.
