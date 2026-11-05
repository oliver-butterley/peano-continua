# peano-continua

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
- `papers/` (gitignored): the paper and the cited preprints, with `pdftotext` versions.

## Building

The toolchain is `leanprover/lean4:v4.35.0` and Mathlib is pinned at `v4.35.0`.

```
lake exe cache get
scripts/build.sh Peano
scripts/build.sh Peano.Audit.Thm1_1 Peano.Audit.Cor5_6 Peano.Audit.Lemma4_5 Peano.Audit.Axioms
```

`scripts/build.sh` runs a low-impact `lake build` with 2 threads, `nice`/`ionice` and an 8 GB
memory cap.

## Status

§4–5 and the "if" direction of Theorem 1.1 are fully formalised, with no `sorry`. See
`notes/README.md` and `notes/lean-map.md`.
