# Plan of work (agreed 2026-11-05)

State at the time of writing: the whole paper is formalised (no `sorry`) except Remark 5.3, a few
descriptive sentences and the ordinal phrasing of Theorem 1.2. The trust boundary is 10 axioms:
9 cited results and 1 textbook fact of dimension theory. Every cited source has been read and every
cited axiom confirmed against it (`axioms.md`). All reviews so far were made by AI agents; no human
has reviewed the material (see the note at the top of `../README.md`). Line counts below are rough
estimates of Lean code.

## Phase 0: housekeeping

1. Commit the state of 2026-11-05 (the user's decision).

## Phase 1: cheap and high-value (days)

2. **Replace the dimension axiom by explicit covers.** Prove `CoveringDimLE 1` directly for the
   spaces used: the Theorem 1.2 models (a segment with a null sequence of attached earrings), the
   circle and the earring. Build fine open covers of order ≤ 2 by hand, and use
   `CoveringDimLE.subtype_of_isClosed`. About 1–2k lines. Delete
   `coveringDimLE_one_of_interior_eq_empty`; Theorem 1.2 (surjectivity) and the sanity checks then
   use no axioms.
3. **Split the trust boundary.** Put Part A (`Reduced`, `Homology`, `PartA`, `Lemma3_3General`,
   `Lemma6_4Paper`) and its four axioms in a separate Lean library target, so that the main library
   carries only the axioms of Theorems 1.1 and 1.2. Split the audit files accordingly.
4. **A continuum with no countable model.** Generalise the model construction to attach earrings at
   any countable bounded set of points, e.g. the dyadic rationals of `[0, 1]`. The wild set is then
   all of `[0, 1]`, uncountable, so by Theorem 1.1 there is no countable weak model: a concrete
   instance of the "only if" direction. About 0.5–1.5k lines.
5. **Meilstrup's bad points are the wild set.** `B(X)`, the points with no simply connected
   neighbourhood, equals `loopWildSet X` for a one-dimensional Peano continuum (via Lemma 2.8 and
   conjugation). This lets the structure axioms quote the thesis literally. About 200–400 lines.
6. **Merge the two structure axioms** (standard form, finite graphs) into one axiom citing
   Meilstrup, Theorem 2.9 and Corollary 2.10. Settle the open point: the thesis says only that
   `G(Y)` is "a disjoint union of open arcs", while the paper's Definition 4.1 also asks that each
   arc's closure be an arc or a simple closed curve.

After Phase 1: 9 axioms; Theorem 1.1 rests on three cited results (Meilstrup, Eda 2002,
Brazas–Fischer monodromy).

## Phase 2: shared infrastructure (weeks)

7. **Bump Mathlib and depend on Tau Ceti** (done early, with Phase 1). Pin one Tau Ceti commit and
   import only its degree-one Hurewicz modules (a closure of 20–28 modules), using Tau Ceti's
   Mathlib revision. Restate Part A with genuine singular `H₁` instead of the abelianised `π₁`
   model; possibly reuse Tau Ceti's weak-equivalence API.
8. **Formalise Cannon–Conner's reduced loops** (Theorem 3.9; the source has been read):
   - Corollary 3.2, retraction into the image of the boundary: 2–4k lines.
   - Existence (Zorn and gluing countably many homotopies): 1–2k lines.
   - Uniqueness, the hard part (their proof uses plane topology; a combinatorial route is likely
     10k+ lines).
   Discharges the two reduced-loop axioms.
9. **Simple closed curves**: a Peano continuum with no simple closed curve is contractible
   (dendrite theory). 3–6k lines, less with item 8.
10. **Monodromy axiom**: with item 8, prove Brazas–Fischer Lemma 4.4 and Proposition 9.13(b).
    1.5–3k lines. Theorem 1.1 then rests on Meilstrup and Eda 2002 only.
11. Optional: the zero-form lemma (Eda 2016 Lemma 3.6, or Cannon–Conner Theorem 6.1). Several
    thousand lines.

## Phase 3: research-scale (months; decide explicitly)

12. Meilstrup's structure theorem (cores, removing attached dendrites, retracting along rays):
    10–25k lines.
13. Eda 2002 (the earring group as a free σ-product, Higman's theorem, Čech `π₁`): 15–40k lines;
    possibly together with the Tau Ceti project.
14. Eda 2022 (brick partitions, dendrite theory; some steps only sketched in the source): 10–30k
    lines on top of item 12.

## Parallel track: communication

15. **Report for the authors**, each point backed by a Lean declaration or a source line:
    - Theorem 1.2 is false as stated (the canonical map is not a bijection), with the correction.
    - The case `w(X) = ∅` of Theorem 1.1 is missed.
    - Five misquoted citations: Theorem 4.2, Theorem 6.6, Definition 3.1, Remark 2.7, Lemma 6.2.
    - The proof repairs: Lemmas 3.3, 3.4, 4.3, 4.5, 5.5, 6.4.
    - The homology-free proof of Lemma 6.4.
    - The false sentence after Definition 4.1.
16. Optional upstream contributions (earring infrastructure, change of base point for `πₙ`, the
    coarsification) to Tau Ceti or Mathlib.

Suggested order: 1, then 2–7 with 15 alongside, then 8–10; revisit Phase 3 afterwards.

## Progress log

- 2026-11-05: plan agreed; Phase 1 (items 2–6) and item 7 started.
- 2026-11-05: item 7, first half, done. Toolchain `v4.36.0-rc2`, Mathlib `1b1ccf4b`, Tau Ceti
  `83b84968` pinned; the bump needed no code changes. Item 3 done: Part A moved to the separate
  library `PeanoPartA` with its own axioms file; `Peano` now has 6 axioms.
- 2026-11-05: items 2, 4, 5, 6 done. The dimension axiom is replaced by proofs (`Dimension.lean`);
  a continuum with uncountable wild set and no countable model (`Sanity.lean`); Meilstrup's bad
  points equal the wild set (`PeanoPartA/BadPoints.lean`); the two structure axioms merged into
  `exists_homotopyEquiv_arcReduced` (reviewed). `Peano` now has 4 axioms; Theorem 1.1 rests on 3.
- 2026-11-05: item 7 done. Part A states Lemmas 3.3 (any `A`), 3.4 and 6.3 in genuine singular
  `H₁(X; ℤ)` (`PeanoPartA/SingularH1*.lean`), using Tau Ceti's degree-one Hurewicz theorem; Tau Ceti
  adds no axioms. Phase 1 and item 7 complete, pending reviews.
