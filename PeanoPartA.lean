module

public import Peano
public import PeanoPartA.Axioms
public import PeanoPartA.Reduced
public import PeanoPartA.Homology
public import PeanoPartA.Lemmas
public import PeanoPartA.Lemma3_3General
public import PeanoPartA.Lemma6_4Paper
public import PeanoPartA.SingularH1
public import PeanoPartA.SingularH1Generators
public import PeanoPartA.SingularH1Lemmas
public import PeanoPartA.BadPoints

/-!
# Part A of Brazas–Pavešić (§2–3) and the paper's own proof of Lemma 6.4

A separate library, so that the main library `Peano` (Theorems 1.1 and 1.2, everything they need)
carries only its own trust boundary. This library adds four cited axioms
(`PeanoPartA/Axioms.lean`: Cannon–Conner reduced loops (two), Eda's zero-form lemma, simple closed
curves). Nothing in `Peano` imports it. The audit file is `PeanoPartA/Audit.lean`.

`H₁` is genuine singular homology through Tau Ceti's degree-one Hurewicz theorem (only the modules
`TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic` and `.Naturality` are imported, by
`PeanoPartA.SingularH1`); the proofs work in the abelianised fundamental group.
-/
