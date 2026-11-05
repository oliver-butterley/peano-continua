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
- `Peano/`: the main Lean library. `Peano/Axioms/` holds its axioms (all results cited by the
  paper). `Peano/Audit/` restates the key statements with `recall` and checks their axioms with
  `#guard_msgs`.
- `papers/` (gitignored, so absent from a fresh clone): the paper and the cited preprints. The paper
  is at <https://arxiv.org/abs/2610.35875>.

## Building

You need [elan](https://github.com/leanprover/elan); it picks up the toolchain
(`leanprover/lean4:v4.36.0-rc2`) from `lean-toolchain`. Dependencies (`lakefile.toml`):
- Mathlib, pinned to a commit;
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti), pinned to a commit that uses the same
  Mathlib commit. Only Part A imports a few of its modules (degree-one Hurewicz); Lake compiles
  just their small import closure (seconds). Never run `lake build TauCeti`, which compiles the
  whole library (hours).

```
lake exe cache get   # download prebuilt Mathlib instead of compiling it
lake build           # both libraries and their audit files
```

Two libraries: `Peano` (Theorems 1.1 and 1.2 and everything they need) and `PeanoPartA` (§2–3 of
the paper and its own proof of Lemma 6.4), each with its own axioms. The audit files
(`Peano/Audit/`, `PeanoPartA/Audit.lean`) record, under `#guard_msgs`, the axioms each key
theorem depends on; the build fails if any list changes, and is otherwise silent. Compare
them with `notes/axioms.md`, which lists every axiom and where it comes from.

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
