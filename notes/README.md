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

The Lean code is in `../Peano/` (library `Peano`; `lake build` builds it). The audit files
`../Peano/Audit/*.lean` restate the key statements with `recall` and print their axioms; `lake build`
builds them too.

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

**Not formalised** (checked informally only, in `checks/A.md` and `checks/D.md`):
- Part A (§2–3: Lemmas 2.5, 2.8, 3.3, 3.4);
- Lemmas 6.3 and 6.4;
- the "only if" direction of Theorem 1.1;
- Theorem 1.2;
- the case `w(X) = ∅` of Theorem 1.1 ("if"), which the paper also misses.

## Assessment and caveats (end of formalisation, 2026-10-28)

**Verdict.** The main theorem is true, apart from the case `w(X) = ∅`, which the paper misses but
which follows easily from McCord's theorem.
- The new technical core (§5, the coarsification and its lifting lemma) is correct as stated, and
  is now machine-checked from the standard axioms only.
- Several proofs needed repairs, but every repaired argument went through in Lean without surprises.
- Theorem 1.2 is false as stated, and true once restricted to non-empty wild sets.

**A misleading claim in `checks/C.md`.** It says Lemma 4.5 is false. That checker read the text
extraction, which drops the closure bars. The PDF has closed arcs `Ōₙ` in conditions (2) and (3),
and with closures the lemma is true: it is proved in Lean as
`Peano.ArcSystem.isOpen_iff_localCondition`. Its counterexample applies only to the misread
version. (`checks/B.md` and `checks/definitions-review.md` read the closures correctly.)

**A near miss on the axioms.** The first Lean version of the Theorem 4.2 axiom, written from the
paper's statement, was inconsistent: a point satisfies its hypotheses but cannot be homotopy
equivalent to a standard-form space. The Part B check caught this before any proof depended on it
(see `axioms.md`).

**Sources that nobody inspected.** Claims resting on these come from secondary sources or memory:
- Meilstrup's thesis (the download was blocked). Theorem 4.2 was checked against the restatement in
  Brazas–Pavešić arXiv:2510.22901, Thm 3.10.
- The full texts of Eda 2002 (Theorem 6.1), Eda 2016 (zero-form lemma) and Eda 2022 (Theorem 6.6).
  For Eda 2022 only the abstract was seen; it is the source of the missing word "non-empty".
- Cannon–Conner 2006 (Remark 2.7, Lemma 2.8).

The three cited axioms that the formalisation does use were checked against Brazas–Mitra
(arXiv:2505.23665, Prop. 2.9), Brazas–Fischer (arXiv:1902.08887v2, Thm 9.15 with Prop. 9.13) and
the Meilstrup restatement above. Copies are in `papers/`.

**Lean caveats.**
- Statements were frozen with the paper's hypotheses, some of which the proofs do not use. Lean
  reports them as unused:
  - `hdim` (one-dimensionality) in `exists_countable_weq_of_standardForm`;
  - the instances `[CompactSpace X] [LocallyPathConnectedSpace X]` in `isOpenMap_q`,
    `countable_coarse` and `exists_lift`.

  They were kept, so that the statements match the paper and the audit files.
- `Lemma 5.4′` (`exists_extension_interior`) is not in the paper. It is the strengthened extension
  lemma that the repaired proof of Lemma 5.5 needs.
- The weak-equivalence definition asks for bijections on `π₀` and on `πₙ`, `n ≥ 1`. The group
  homomorphism property is automatic and is not stated.
- No audit file restates the generic theorems of `Peano/WeakEquiv.lean` (lifting for cubes ⇒ Serre
  fibration and weak equivalence; composition). They are covered only through Corollary 5.6.

**Open questions.** See `novelty.md`, "Open questions about novelty". The most interesting is the
unreviewed suggestion that Lemma 6.4 has a proof without homology.
