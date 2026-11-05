# Axioms of the `Peano` formalisation (audit table)

Every axiom is in `Peano/Axioms/`, and `Peano/Audit/Axioms.lean` prints each one in full. Check that
none exists elsewhere with `grep -rn '^axiom' Peano`. The "used by" column comes from the
`#print axioms` lines in `Peano/Audit/*.lean`. The adversarial review is in `checks/axioms-review.md`.

| Lean name | Kind | Source | Statement (informal) | Used by | Review |
|---|---|---|---|---|---|
| `Peano.isClosed_wildSet` | cited | paper Lemma 2.3, from Brazas–Mitra, arXiv:2505.23665 | the wild set of a locally path-connected metric space is closed | `IsStandardForm.exists_arcSystem`, both Theorem 1.1 layers | reviewed: true, checked against Brazas–Mitra Prop. 2.9 |
| `Peano.exists_homotopyEquiv_standardForm` | cited | paper Theorem 4.2, from Meilstrup 2005 (Master's thesis) | a one-dimensional Peano continuum **with non-empty wild set** is homotopy equivalent to one in standard form | `exists_countable_weq` | reviewed: true *with* `w ≠ ∅` (false without it); primary source (thesis) not accessible, checked against Brazas–Pavešić arXiv:2510.22901 §3, Thm 3.10 |
| `Peano.nonempty_homeomorph_wildSet` | cited | Brazas–Fischer 2020, Bull. LMS, Thm 9.15 (quoted in the paper's proof of Theorem 1.2) | homotopy equivalent one-dimensional Peano continua have homeomorphic wild sets | `exists_countable_weq` | reviewed: true, checked against Brazas–Fischer arXiv:1902.08887v2 Thm 9.15 with Prop. 9.13 |
| `Peano.HomotopyEquiv.isWeakHomotopyEquivalence` | standard | Hatcher, *Algebraic Topology*, Prop. 1.18 and §4.1 | a homotopy equivalence is a weak homotopy equivalence | `exists_countable_weq` | reviewed: true (from memory of Hatcher; π₀, π₁ parts provable from Mathlib) |

## Changes from the paper's statements

- **Theorem 4.2: hypothesis `(wildSet X).Nonempty` added.** As quoted, the theorem is false when
  `w(X) = ∅`, for example for a point, a circle or a finite graph: a non-empty standard-form space
  has a non-empty wild set, and homotopy equivalences preserve that. Without the hypothesis the
  axiom would be inconsistent. Found by the Part B check (`checks/B.md`). As a consequence, the
  formalised Theorem 1.1 assumes `w(X) ≠ ∅`, and the paper's proof has a gap in the case `w(X) = ∅`.
- **Brazas–Fischer Thm 9.15** is assumed only in the weaker form "the wild sets are homeomorphic",
  not "the given homotopy equivalence restricts to a homeomorphism".
- **Lemma 2.3** is assumed only for metric spaces, not for all first-countable spaces.
