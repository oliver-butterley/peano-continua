# peano-continua


⚠️ This paragraph is the only part of this entire repo which was contributed by a human. 
All other content was added by AI as a quick experiment during a discussion. 
So far no human has even reviewed any of the material produced.



This repository checks and formalises in Lean 4 the paper by Jeremy Brazas and Petar Pavešić,
*Countable models of one-dimensional Peano continua* (arXiv:2610.35875, v1, 10 Aug 2026).

The paper's main claim (Theorem 1.1): a one-dimensional Peano continuum is weakly homotopy
equivalent to a countable space if and only if its wild set is countable.

## Contents

- `notes/`: the mathematics.
  - `README.md`: findings and status.
  - `structure.md`: the dependency graph.
  - `novelty.md`: what is new in the paper.
  - `checks/`: adversarial proof checks and reviews.
  - `axioms.md`: the trust boundary.
  - `lean-map.md`: paper result ↔ Lean declaration.
- `Peano/`: the Lean library. `Peano/Axioms/` holds every axiom (results cited by the paper, and one
  textbook fact). `Peano/Audit/` restates the key statements with `recall` and prints their axioms.
- `papers/` (gitignored, so absent from a fresh clone): the paper and the cited preprints. The paper
  is at <https://arxiv.org/abs/2610.35875>.

## Building

You need [elan](https://github.com/leanprover/elan); it picks up the toolchain
(`leanprover/lean4:v4.35.0`) from `lean-toolchain`. Mathlib is pinned at `v4.35.0`.

```
lake exe cache get   # download prebuilt Mathlib instead of compiling it
lake build           # the library and the audit files
```

The build prints the axioms each key theorem depends on (from `Peano/Audit/`). Compare them with
`notes/axioms.md`, which lists every axiom and where it comes from.

## Status

Every numbered result of the paper is formalised, with no `sorry`, except Remark 5.3 and the ordinal
phrasing of Theorem 1.2; some lemmas are proved in a narrower setting than stated, which is enough
for the main theorems (`notes/README.md`).
- Theorem 1.1, both directions, including the case `w(X) = ∅` that the paper's proof misses.
- Theorem 1.2 in corrected form (non-empty wild sets). As stated, the canonical bijection claimed by
  the paper is not one (the circle has a countable model but is not homotopy equivalent to any of
  the paper's models `A_λ`), because the cited Theorem 6.6 needs non-empty wild sets; this is
  formalised too.

The trust boundary is a short list of cited theorems and one textbook fact of dimension theory
(`notes/axioms.md`). See `notes/README.md` and `notes/lean-map.md`.
