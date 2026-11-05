# Working conventions for this repository

Project: check and formalise in Lean 4 Brazas–Pavešić, *Countable models of one-dimensional Peano
continua* (arXiv:2610.35875). Findings and status are in `notes/README.md`; the paper ↔ Lean map
is in `notes/lean-map.md`; the axioms are in `notes/axioms.md`.

## Lean

- Toolchain `leanprover/lean4:v4.35.0`, Mathlib tag `v4.35.0`, `autoImplicit = false`. A fresh
  checkout needs `lake exe cache get`.
- `lake build` builds the library and the audit files.
- Parallel Lean agents are allowed, two or three at a time. Rules:
  - start `scripts/lean_watchdog.sh 2500 1200 10` in the background first;
  - each agent edits only its own file and checks its work through the MCP diagnostics;
  - only the orchestrator runs `lake build`, between waves.
- Mathlib naming conventions; a docstring on every definition and theorem; a module header that
  states the informal meaning of the file and the design choices behind the encodings.
- Two libraries: `Peano` (Theorems 1.1 and 1.2 and everything they need) and `PeanoPartA` (§2–3
  and the paper's own proof of Lemma 6.4). Nothing in `Peano` imports `PeanoPartA`.
- Axioms live only in `Peano/Axioms/` (`Cited.lean` for results the paper cites, `Standard.lean`
  for textbook facts missing from Mathlib) and, for Part A only, `PeanoPartA/Axioms.lean`. Every
  axiom:
  - is listed in `notes/axioms.md`;
  - is checked by `Peano/Audit/Axioms.lean` (or `PeanoPartA/Audit.lean`);
  - gets an adversarial review before anything depends on it.
- Key statements are restated with `recall`, and their axioms checked with
  `#guard_msgs in #print axioms`, in `Peano/Audit/`. A change to a
  frozen statement must be mirrored there.
- `lake build` must be silent: no info, no warning. Use `#guard_msgs` for any command that prints.

## Notes

- Markdown under `notes/`. Expand every acronym at its first use in each document.
- Every new lemma gets an adversarial review by an agent that has not seen the author's
  assessment, before anything depends on it.
- Downloaded papers live in `papers/` (gitignored), with `pdftotext` versions beside the PDFs.

## Git

- Claude commits at natural completion points, as the configured user and without attribution
  trailers. Never push.
