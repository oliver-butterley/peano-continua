module

public import Peano.Defs
public import Peano.LoopWildSet
public import Peano.Earring
public import Peano.Arcs
public import Peano.StandardForm
public import Peano.Coarsify
public import Peano.WeakEquiv
public import Peano.HomotopyEquiv
public import Peano.WildSet
public import Peano.Axioms.Cited
public import Peano.Axioms.Standard
public import Peano.Main
public import Peano.Thm1_2
public import Peano.EarringOps
public import Peano.OnlyIf
public import Peano.BrazasFischer
public import Peano.Thm1_1
public import Peano.Dimension
public import Peano.LocJoin
public import Peano.PlaneGeometry
public import Peano.Models
public import Peano.Sanity
public import Peano.Remark6_5

/-!
# Countable models of one-dimensional Peano continua

Formalisation of Brazas–Pavešić, *Countable models of one-dimensional Peano continua*
(arXiv:2610.35875), modulo cited results stated as axioms in `Peano.Axioms` (listed in
`notes/axioms.md`):

* §2: wild sets, Lemma 2.3 (`Peano.WildSet`), Lemma 2.5; §4–§5: standard form, arc systems,
  coarsification, Lemma 5.5 and Corollary 5.6 (`Peano.StandardForm`, `Peano.Coarsify`,
  `Peano.WeakEquiv`, `Peano.Main`);
* Theorem 1.1, both directions (`Peano.Thm1_1`), with Lemmas 6.2 and 6.4 proved homology-free in
  `Peano.OnlyIf`;
* Brazas–Fischer Theorem 9.15 (homotopy equivalences restrict to homeomorphisms of wild sets),
  proved from the cited discrete-monodromy property (`Peano.BrazasFischer`);
* Part A (§2–§3: Lemmas 2.8, 3.3, 3.4) and Lemma 6.3 (`PeanoPartA.Homology`, `PeanoPartA.Lemmas`), and the
  paper's own proof of Lemma 6.4 through them (`PeanoPartA.Lemma6_4Paper`);
* Theorem 1.2, corrected (non-empty wild sets; `Peano.Thm1_2`), with the planar models of
  `Peano.Models`; Remark 6.5 (`Peano.Remark6_5`); sanity checks and the counterexample to
  Theorem 1.2 as stated (`Peano.Sanity`).

Notes, checks and the lemma map are in `notes/`. The audit files `Peano/Audit/*.lean` are not
imported here; `lake build` builds them anyway (see the `globs` in `lakefile.toml`).
-/
