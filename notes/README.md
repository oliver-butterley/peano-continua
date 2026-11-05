# Brazas–Pavešić, "Countable models of one-dimensional Peano continua" (arXiv:2610.35875)

This project checks and formalises a 14-page general-topology paper by Jeremy Brazas and Petar
Pavešić. It began as a side project inside the `anosov` repository and moved here on 2026-11-05.

Main claim (Theorem 1.1): a one-dimensional Peano continuum is weakly homotopy equivalent to a
countable space if and only if its wild set is countable.

## Files

| File | Content |
|---|---|
| `structure.md` | The paper's results, what is cited, the dependency graph and the formalisation scope |
| `novelty.md` | What is new: a literature search with evidence and confidence levels |
| `checks/A.md` … `checks/D.md` | Independent adversarial proof checks of §2–3, §4, §5 and §6 |
| `checks/definitions-review.md` | Review of the Lean definitions and statements against the paper |
| `checks/axioms-review.md` | Adversarial review of the first Lean axioms (historical) |
| `checks/reviews-2026-11-05.md` | Record of the adversarial reviews of the extension to the whole paper |
| `axioms.md` | The audit table of every axiom (the trust boundary) |
| `lean-map.md` | Paper result ↔ Lean declaration ↔ status ↔ axioms |

The Lean code is in `../Peano/` (library `Peano`; `lake build` builds it). The audit files
`../Peano/Audit/*.lean` restate the key statements with `recall` and print their axioms; `lake build`
builds them too.

## Findings of the checks

**Errors in the paper's statements**
- **Theorem 1.2 is false as stated** (checks D and novelty): the canonical map `[λ] ↦ Ho(A_λ)` is
  not a bijection onto the claimed set. (Some bijection between the two sets exists for cardinality
  reasons, so the precise failure is of the canonical one, and of the cited Theorem 6.6.)
  - The paper quotes Eda 2022 (its Theorem 6.6) without that theorem's hypothesis "non-empty".
  - Spaces with an empty wild set break the claimed bijection: a point and a circle are not
    homotopy equivalent, both have finite models, and neither is homotopy equivalent to any
    model `A_λ`.
  - The theorem is true when restricted to non-empty wild sets.
- **Theorem 4.2 (Meilstrup), as quoted, is false when `w(X) = ∅`** (checks B, D and the axiom
  review). A non-empty space in standard form has a non-empty wild set. So the proof of Theorem 1.1
  ("if") misses the case `w(X) = ∅`, which needs a separate argument: `X` is then homotopy
  equivalent to a finite graph, which has a finite model by McCord.
- **The sentence after Definition 4.1** ("w(X) infinite ⇒ infinitely many arcs") is false; the
  Sierpiński carpet is a counterexample. Nothing uses it.

**Gaps and errors in proofs, all repairable** (the statements are true)
- Lemma 3.3: the case of several path components is unproved (A).
- Lemma 3.4: several defects, though a two-line proof exists (A).
- Lemma 4.3: the final contradiction does not follow; three-point repair (B).
- Lemma 4.5: the compactness step is circular; repaired with Lemma 4.3 and condition (3) (B).
- Lemma 5.5: the boundary-value step is false; repaired with a strengthened Lemma 5.4 (C).
  Continuity at wild points also needs a fix.
- Lemma 6.4: Eda's Theorem 6.1 is applied outside its stated hypotheses; Lemma 3.4 is applied to
  loops that need not be reduced (D).
- Lemma 6.2 is mis-cited: Brazas–Fischer Prop. 9.13 states something weaker (D).

**What is new** (`novelty.md`)
- The coarsification and its lifting lemma (§5), giving countable weak models.
- Lemma 6.4 with an arbitrary target.

Theorem 1.2 is mostly an assembly of Eda 2022, Brazas–Fischer and Mazurkiewicz–Sierpiński. Lemma
4.5 copies a construction of Brazas–Mitra.

**A homology-free proof of Lemma 6.4** (suggested by the novelty agent, `novelty.md`). It applies
Lemma 6.2 twice (to the even and to the odd circles of the map given by Eda's theorem) and needs
neither `H₁` nor Lemmas 3.3, 3.4, 6.3. It was re-derived independently twice and is now formalised
(`Peano.injOn_wildSet`); the main theorems use it. The paper's own route is formalised as well
(`Peano.injOn_wildSet_of_paper`), as a check of §3.

## Formalisation scope and status (2026-11-05)

Every numbered result of the paper is formalised, with the paper's errors corrected, except
Remark 5.3 and the ordinal phrasing of Theorem 1.2 (see "Not formalised" below). There is no `sorry`
in `Peano/`. `lean-map.md` maps every result to its Lean declaration; `axioms.md` lists the axioms.

- **Theorem 1.1, both directions, all cases** (`Peano.exists_countable_weq_iff`), including the case
  `w(X) = ∅` that the paper misses (a finite graph; its coarsification is a finite model, so
  McCord's theorem is not needed). Cited axioms: Meilstrup's Theorem 4.2 (with `w ≠ ∅`), the
  finite-graph theorem (arXiv:2510.22901 Thm 3.9), Eda's Theorem 6.1 (on generators) and the
  discrete-monodromy consequence of Brazas–Fischer Prop. 9.13.
- **§4–5** for abstract arc systems, from the standard axioms only, without the paper's unused
  hypotheses (`countable_weq_q`, `exists_lift`).
- **Lemma 6.4** by the homology-free proof, and Lemma 6.2 derived from Brazas–Fischer (the paper
  mis-cites Prop. 9.13).
- **Theorem 1.2, corrected** (non-empty wild sets): `X ↦ w(X)` is a bijection from homotopy types of
  one-dimensional Peano continua with non-empty countable wild set onto homeomorphism types of
  non-empty countable compact metric spaces (`Peano/Thm1_2.lean`). Surjectivity is a full planar
  construction of the models (`Peano/Models.lean`); one-dimensionality of the models uses the
  textbook axiom "a compact planar set with empty interior has dimension ≤ 1". The paper's
  statement is formally refuted (`Peano.Sanity.thm1_2_counterexample`: the point and the circle).
- **Part A (§2–3)**: Lemmas 2.5, 2.8, 3.3 (for the path component of the base point; the general
  case in `Peano/Lemma3_3General.lean`), 3.4 (without the reducedness hypothesis), 6.3; `H₁` of a
  path-connected space is modelled by the abelianised `π₁` (Hurewicz). Cited: Cannon–Conner
  (reduced loops), Eda's zero-form lemma, simple closed curves. Lemmas 3.3, 3.4, 6.3 are proved for
  one-dimensional Peano continua (the paper says metrizable spaces), the scope of Eda's lemma.
- **Former axioms now proved**: Brazas–Fischer Thm 9.15 (from their discrete-monodromy
  proposition), Lemma 2.3 (the wild set is closed; locally path-connected suffices
  for the loop definition), "a homotopy equivalence is a weak homotopy equivalence" (change of base
  point for higher homotopy groups), the equivalence of the two definitions of wild points.
- **Remark 6.5** (`Peano/Remark6_5.lean`): `𝔼 → 𝔼 × I` is a homotopy equivalence whose restriction
  to wild sets is not surjective (`{b₀} × I ⊆ w(𝔼 × I)`, uncountable).
- **Sanity checks** (`Peano/Sanity.lean`): weak equivalence is not trivial, `w(𝔼) = {b₀}`, the
  earring and the models satisfy the hypotheses of Theorem 1.1.

**Not formalised.**
- Remark 5.3 (closures and boundaries of the points `bₙ`, `dₙ` of `𝒞X`); the proofs of §5 in Lean do
  not need it.
- The introduction's descriptive claims about `𝒞X` (first countable, locally path-connected, T0),
  and the description at the start of §5 of the coarse earring of Brazas–Matos [7].
- The paragraph after Definition 4.1: its false sentence ("`w(X)` infinite ⇒ infinitely many arcs";
  the Sierpiński carpet is a counterexample) is refuted only informally (`checks/B.md`); its true
  claim is not formalised. Nothing uses either.
- The ordinal phrasing of Theorem 1.2 (Mazurkiewicz–Sierpiński: a countable compact metric space is
  homeomorphic to a countable successor ordinal). The formal statement uses countable compact
  metric spaces directly, which also avoids the ordinal conventions criticised in `checks/D.md`.

**Proved in a narrower setting than the paper states** (enough for every use in the paper):
- Lemma 6.4 for `X` a one-dimensional Peano continuum (the paper: path-connected, locally
  path-connected one-dimensional metric spaces; its proof applies Theorem 6.1, quoted for Peano
  continua). On the other hand `Y` need not be path-connected.
- Lemmas 3.3, 3.4, 6.3 for one-dimensional Peano continua (the paper: metrizable spaces), the scope
  of the cited zero-form lemma.
- Lemma 5.4 for metric spaces (the paper: perfectly normal spaces).
- Remark 6.5: only `{b₀} × I ⊆ w(𝔼 × I)`, which is all the remark needs.
- Theorem 6.1 is assumed on the generators `[ℓₖ]` only.

## Assessment and caveats

**Verdict.** Theorem 1.1 is true, including the case `w(X) = ∅`, which the paper misses. Theorem 1.2
is false as stated and true for non-empty wild sets. The new technical core (§5) is correct and is
machine-checked from the standard axioms. Every repaired proof went through in Lean.

**Trust boundary.** Ten axioms in all (`axioms.md`): nine cited results and one textbook fact of
dimension theory. Theorem 1.1 rests on four cited results; the corrected Theorem 1.2 on Brazas–Fischer's
discrete monodromy and Eda 2022 (injectivity) and the dimension fact (surjectivity). Sources not inspected:
Meilstrup's thesis (checked against the restatement in arXiv:2510.22901 Thm 3.10), Eda 2002 (checked
against Kent arXiv:1305.4215), Eda 2016 and Eda 2022 (abstract only; the source of "non-empty"),
Cannon–Conner 2006 (checked against Constantine–Lafont arXiv:1209.3709). Copies of the accessible
sources are in `papers/`.

**A misleading claim in `checks/C.md`.** It says Lemma 4.5 is false. That checker read the text
extraction, which drops the closure bars; with closures the lemma is true and proved in Lean.

**A near miss on the axioms.** The first Lean version of the Theorem 4.2 axiom, written from the
paper's statement, was inconsistent (a point satisfies its hypotheses). It was caught before any
proof depended on it.

**Lean caveats.**
- The frozen `exists_countable_weq_of_standardForm` keeps the paper's unused hypothesis `hdim`.
- `X : Type` (not universe-polymorphic) in the main theorems, because the cited axioms are stated
  for `Type`; a compact metric space has at most continuum many points, so this is no restriction.
- The weak-equivalence definition asks for bijections on `π₀` and `πₙ`; the homomorphism property
  is automatic and not stated.
- `Peano/Audit/Defs.lean` prints every definition the main statements use; `recall` only freezes
  theorem statements.

## Possible dependency: Tau Ceti (checked 2026-11-05)

Tau Ceti (github.com/TauCetiProject/TauCeti) is the Lean FRO's library of AI-formalised mathematics,
downstream of Mathlib. Depending on it is worthwhile **only if** it stays cheap: import a few
specific modules, so that Lake builds only their small closure, or use its published cache. Never
build the whole library: about 26,000 files, hours from source.

- **What would be used.**
  - Hurewicz in degree one, `π₁(X, x)^ab ≅ H₁(X; ℤ)` (`TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.*`).
    It would replace the abelianised-`π₁` model of `H₁` in Part A by genuine singular homology, and is
    the bridge a proof of the zero-form lemma would need.
  - Possibly its weak-homotopy-equivalence API
    (`TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence`), which duplicates
    `Peano/HomotopyEquiv.lean`.
  - Its Jordan-curve files (`TauCeti.Topology.JordanCurve.*`), which recognise simple closed curves
    traced by paths.
  - None of the ten axioms is discharged by Tau Ceti.
- **Cost measured on commit 482d8ed1.** The import closure of `Hurewicz.One.Basic` is 20 Tau Ceti
  modules, about 4,600 lines; with `Naturality`, 28 modules, about 7,000 lines. That is minutes to
  build from source after `lake exe cache get` for Mathlib. Tau Ceti also publishes an olean cache
  (`scripts/lake-cache-get.sh`, through `uvx`), which misses after a toolchain bump.
- **Constraint.** Tau Ceti uses `leanprover/lean4:v4.36.0-rc2` and Mathlib `master`. A dependency
  means pinning one Tau Ceti commit and moving this repository to exactly its Mathlib revision. A
  Mathlib bump is acceptable for this project. Alternative: port the few needed files, which the
  Apache-2.0 licence allows with attribution.

