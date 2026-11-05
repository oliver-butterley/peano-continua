# peano-continua


⚠️ This paragraph is the only part of this entire repo which was contributed by a human. 
All other content was added by AI as a quick experiment during a discussion. 
There was not even an attempt (so far) to review any of the material produced.



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

§4–5 and the "if" direction of Theorem 1.1 are fully formalised, with no `sorry`. See
`notes/README.md` and `notes/lean-map.md`.
