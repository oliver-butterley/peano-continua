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
| `checks/axioms-review.md` | Adversarial review of the Lean axioms |
| `axioms.md` | The audit table of every axiom (the trust boundary) |
| `lean-map.md` | Paper result ↔ Lean declaration ↔ status ↔ axioms |

The Lean code is in `../Peano/` (library `Peano`; build it with `scripts/build.sh Peano`). The
audit files `../Peano/Audit/*.lean` restate the key statements with `recall` and print their
axioms. Build them with `scripts/build.sh Peano.Audit.Thm1_1` and so on.

## Findings of the checks

**Errors in the paper's statements**
- **Theorem 1.2 is false as stated** (checks D and novelty).
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

**Unverified suggestion** (novelty agent): Lemma 6.4 may have a proof without homology, which
would make §3 unnecessary. It has not been reviewed, and nothing depends on it.

## Formalisation scope and status

The Lean formalisation covers §4–5 and Theorem 1.1 ("if"); see `lean-map.md` for details.
- §4–5 are stated for an abstract `ArcSystem`: neither section uses one-dimensionality.
- The general form of Theorem 1.1 ("if") assumes `w(X) ≠ ∅`, for the reason above.
- Lemma 5.5 drops the paper's unused hypothesis "B locally path-connected", and takes Lemma 4.3
  as a hypothesis.

Status (2026-10-28): **complete**. There is no `sorry` in `Peano/`.
- §4–5, Corollary 5.6 and the lifting ⇒ weak equivalence step depend only on the standard axioms.
- Theorem 1.1 ("if"), standard-form layer: additionally the cited Lemma 2.3.
- Theorem 1.1 ("if"), general layer (`w(X) ≠ ∅`): additionally Theorem 4.2 (Meilstrup),
  Brazas–Fischer Thm 9.15, and "homotopy equivalence ⇒ weak equivalence".

The audit files' `#print axioms` outputs match `axioms.md`. The formal proofs followed the
repaired arguments of `checks/B.md` and `checks/C.md`, with two simplifications:
- Lemma 4.5 is proved without the auxiliary topology `X′`;
- Lemma 5.5 needs neither compactness nor local path-connectedness of `X`, only the null-diameter
  property.

The standard-form layer of Theorem 1.1 does not use one-dimensionality.
