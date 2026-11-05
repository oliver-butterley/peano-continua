# Working conventions for this repository

Project: check and formalise in Lean 4 Brazas–Pavešić, *Countable models of one-dimensional Peano
continua* (arXiv:2610.35875). Findings and status are in `notes/README.md`; the paper ↔ Lean map
is in `notes/lean-map.md`; the axioms are in `notes/axioms.md`.

## Lean

- Toolchain `leanprover/lean4:v4.35.0`, Mathlib tag `v4.35.0`, `autoImplicit = false`. A fresh
  checkout needs `lake exe cache get`.
- Build with `scripts/build.sh` (a low-impact `lake build`: 2 threads, `nice`/`ionice`, 8 GB memory
  cap; arguments are passed to `lake build`). Run **one build at a time**.
- Parallel Lean agents are allowed, two or three at a time. Rules:
  - start `scripts/lean_watchdog.sh 2500 1200 10` in the background first;
  - each agent edits only its own file and checks its work through the MCP diagnostics;
  - only the orchestrator runs `scripts/build.sh`, between waves.
- Mathlib naming conventions; a docstring on every definition and theorem; a module header that
  states the informal meaning of the file and the design choices behind the encodings.
- Axioms live only in `Peano/Axioms/` (`Cited.lean` for results the paper cites, `Standard.lean`
  for textbook facts missing from Mathlib). Every axiom:
  - is listed in `notes/axioms.md`;
  - is printed by `Peano/Audit/Axioms.lean`;
  - gets an adversarial review before anything depends on it.
- Key statements are restated with `recall` and `#print axioms` in `Peano/Audit/`. A change to a
  frozen statement must be mirrored there.

## Notes

- Markdown under `notes/`. Expand every acronym at its first use in each document.
- Every new lemma gets an adversarial review by an agent that has not seen the author's
  assessment, before anything depends on it.
- Downloaded papers live in `papers/` (gitignored), with `pdftotext` versions beside the PDFs.

## Git

- Claude commits on its own branch `dev/claude` at natural completion points, as the configured
  user and without attribution trailers. Never push. The user merges to `master` themselves.
