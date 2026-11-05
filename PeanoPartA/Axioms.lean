module

public import PeanoPartA.Reduced
public import Peano.Defs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Cited results used only by Part A, assumed as axioms

The trust boundary of the separate library `PeanoPartA` (§2–3 of Brazas–Pavešić, and the paper's
own proof of Lemma 6.4). The main library `Peano` (Theorems 1.1 and 1.2) does not import this file.
Audit table: `notes/axioms.md`; every axiom here is printed by `PeanoPartA/Audit.lean`.
-/

@[expose] public section

open Topology unitInterval

namespace Peano


/-- **Remark 2.7**, existence half, from Cannon–Conner, *On the fundamental groups of
one-dimensional spaces*, Topology Appl. 153 (2006), Theorem 3.9 (inspected 2026-11-05,
`papers/1-s2.0-S0166864105002907-main.pdf`: stated under the standing hypotheses of their §3.2,
compact, path-connected, one-dimensional metric, l.246; "reduced" as in their Definition 3.8; the
image condition comes from their proof, l.312 and l.322, and Corollary 3.2, and is explicit in the
restatement of Constantine–Lafont, arXiv:1209.3709, Thm 2.10; the paper's Remark 2.7 overstates the
scope as "metrizable"): every loop is homotopic rel end points to a reduced
loop by a homotopy whose image lies in the image of the loop. Assumed only for compact
path-connected spaces, the restatement's scope. -/
axiom exists_reduced_homotopy (X : Type) [MetricSpace X] [CompactSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {x : X} (α : Path x x) :
    ∃ β : Path x x, IsReducedPath β ∧ ∃ H : Path.Homotopy α β, Set.range H ⊆ Set.range α

/-- **Remark 2.7**, uniqueness half (same source and scope as `exists_reduced_homotopy`): reduced
loops that are homotopic rel end points differ by an increasing reparametrisation. -/
axiom isReparam_of_reduced_homotopic (X : Type) [MetricSpace X] [CompactSpace X]
    [PathConnectedSpace X] (hX : CoveringDimLE 1 X) {x : X} {β β' : Path x x}
    (hβ : IsReducedPath β) (hβ' : IsReducedPath β') (h : β.Homotopic β') :
    IsReparam (β : C(I, X)) β'

/-- **Lemma 3.2** (zero-form lemma), direction "⇒", from Eda, *Singular homology groups of
one-dimensional Peano continua*, Fund. Math. 232 (2016), Lemma 3.6, as quoted by the paper: if an
essential loop `α` is null-homologous, then a reduced representative of `α` is (the concatenation
of) a 0-form.

Only this direction is assumed: the converse, "a 0-form is null-homologous", holds in every space
and is proved (`Peano.fromPath_mem_commutator_of_isZeroFormCut`, `Peano.Homology`).
"Null-homologous" is stated through the Hurewicz theorem (Hatcher, Thm 2A.1: for path-connected
`X`, `H₁(X) ≅ π₁(X, x)^ab`, so `[α]_h = 0` iff `[α]` lies in the commutator subgroup; Eda's proof
uses the same translation). Checked against Eda's text (`papers/fm232-2-01.txt`: `≡` l.126–128,
reduced paths l.148–150, Definition 3.4 l.175–180, Lemma 3.6 l.185–187). Eda's `≡` is equality up
to an increasing homeomorphism, so `IsZeroFormCut` is Eda's 0-form; the paper's exact "=" in its
Definition 3.1 is a misquote (`notes/checks/A.md`, A-3.1-1). Eda's Lemma 3.6 holds for
one-dimensional metric spaces; assuming it only for Peano continua is stricter than the source. -/
axiom eda_zeroForm (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x : X} (α : Path x x)
    (hα : ¬ α.Homotopic (Path.refl x))
    (h : FundamentalGroup.fromPath ⟦α⟧ ∈ commutator (FundamentalGroup X x)) :
    ∃ ρ : Path x x, IsReducedPath ρ ∧ ρ.Homotopic α ∧ IsZeroFormCut (ρ : C(I, X))

/-- **Simple closed curves**, the "well-known fact" in the proof of Lemma 6.3 in its corrected form
(`notes/checks/D.md`): a path-connected one-dimensional metric space with an essential loop
contains a simple closed curve (an injective image of the circle). Source: Brazas–Pavešić,
arXiv:2510.22901, Corollary 3.3 (a path-connected one-dimensional Hausdorff space is simply
connected iff it is uniquely arcwise connected) with the fact quoted there before Definition 3.5
(a path-connected Hausdorff space is uniquely arcwise connected iff it contains no simple closed
curve). Alternative source: Cannon–Conner 2006, Definition 3.6 and l.261 (a Peano continuum with no
simple closed curve is a dendrite, and dendrites are contractible), applied to the image of the
loop; this shows the dimension hypothesis is not needed. -/
axiom exists_simpleClosedCurve (X : Type) [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {x : X} (α : Path x x) (hα : ¬ α.Homotopic (Path.refl x)) :
    ∃ c : C(AddCircle (1 : ℝ), X), Function.Injective c

end Peano
