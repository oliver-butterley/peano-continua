module

public import Peano.Defs
public import Peano.Arcs
public import Peano.LoopWildSet
public import Peano.Reduced
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.InductiveDimension.Classes

/-!
# Results cited by Brazas–Pavešić, assumed as axioms

The trust boundary of the formalisation, part 1 of 2 (part 2: `Peano.Axioms.Standard`). Each
axiom is a theorem from the literature that the paper quotes without proof; its docstring gives
the statement in words, the exact reference, and the paper's use. Audit table: `notes/axioms.md`;
adversarial review: `notes/checks/axioms-review.md`. `#print axioms` on any theorem shows which of
these it uses (`Peano/Audit/`).

Every axiom is stated no more strongly than its source (where a weaker form suffices, the weaker
form is taken), and only for the spaces the paper applies it to.
-/

@[expose] public section

open Topology unitInterval

namespace Peano

/-- **Theorem 4.2** of the paper, from Meilstrup, *Classifying homotopy types of one-dimensional
Peano continua*, Master's thesis, Brigham Young University, 2005, Theorem 2.9 (inspected
2026-11-05; it has the hypothesis "`B(X) ≠ ∅`", bad points, which the paper drops): every
one-dimensional Peano continuum is homotopy equivalent to a one-dimensional Peano continuum in
standard form.

**Hypothesis `(wildSet X).Nonempty` added** (not in the paper's statement): with Definition 4.1 a
non-empty standard-form space has non-empty wild set (an arc's end points lie in `w`), and
homotopy equivalences preserve emptiness of `w`, so the theorem as quoted is false for, e.g., a
point; without this hypothesis the axiom would be inconsistent. Found by the Part B check
(`notes/checks/B.md`). -/
axiom exists_homotopyEquiv_standardForm (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X)
    (hw : (wildSet X).Nonempty) :
    ∃ (X' : Type) (_ : MetricSpace X'), CompactSpace X' ∧ ConnectedSpace X' ∧
      LocallyPathConnectedSpace X' ∧ CoveringDimLE 1 X' ∧ IsStandardForm X' ∧
      Nonempty (ContinuousMap.HomotopyEquiv X X')

/-- **Finite graphs.** A one-dimensional Peano continuum with no wild points is homotopy equivalent
to a finite graph. Source: Brazas–Pavešić, *Motion planning on one-dimensional Peano continua*,
arXiv:2510.22901, Theorem 3.9 (a non-simply-connected one-dimensional Peano continuum with empty
wild set deformation retracts onto a finite graph), together with, for the simply connected case,
Corollary 3.3 there (simply connected ⇒ uniquely arcwise connected, i.e. a dendrite) and the
contractibility of dendrites (Nadler, *Continuum Theory*, Ch. X), which gives a homotopy
equivalence with a point.

The source defines wild points by small essential loops (its Definition 3.5), so the hypothesis
uses `loopWildSet`. A finite graph is encoded as a compact metric space carrying an `ArcSystem`
with finitely many arcs and a finite closed set `W` (the vertices; the point is the graph with one
vertex and no edges). Not in the paper: it is needed for the case `w(X) = ∅` of Theorem 1.1, which
the paper's proof overlooks (Theorem 4.2 fails there). -/
axiom exists_homotopyEquiv_finiteGraph (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X)
    (hw : loopWildSet X = ∅) :
    ∃ (X' : Type) (_ : MetricSpace X') (S : ArcSystem X'), CompactSpace X' ∧ S.W.Finite ∧
      Finite S.ι ∧ Nonempty (ContinuousMap.HomotopyEquiv X X')

/-- **Theorem 6.1** of the paper, from Eda, *The fundamental groups of one-dimensional spaces and
spatial homomorphisms*, Topology Appl. 123 (2002), Theorem 1.1: for a one-dimensional Peano
continuum `X`, every homomorphism `ψ : π₁(𝔼, b₀) → π₁(X, x₀)` is induced by a map `g : 𝔼 → X` up
to the change of base point `φ_α([γ]) = [α⁻ γ α]` along a path `α` from `g(b₀)` to `x₀`.

Assumed only on the generators: the conclusion is stated for the classes of the loops `ℓₖ`, not
for all of `π₁(𝔼, b₀)`, which is all the proof of Lemma 6.4 uses. Assumed only for Peano continua,
the scope in which the paper quotes it (`notes/checks/D.md`, finding 2). Checked against Eda's
text (`papers/1-s2.0-S0166864101002140-main.pdf`, Theorem 1.1, Topology Appl. 123 (2002)): the
target may be any one-dimensional metric space; the earring and base point are the same subset of
`ℝ²`; `φ_p([f]) = [p⁻ f p]` with `p` from `f(o)` to `x`, as here. The axiom is a special case; by
Eda's Lemma 3.15 the generator form is in fact equivalent to the full form. -/
axiom eda_exists_map_earring (X : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (x₀ : X)
    (ψ : FundamentalGroup earring earringBase →* FundamentalGroup X x₀) :
    ∃ (g : C(earring, X)) (α : Path (g earringBase) x₀), ∀ k,
      ψ (FundamentalGroup.fromPath ⟦earringLoop k⟧) =
        FundamentalGroup.fromPath ⟦(α.symm.trans ((earringLoop k).map g.continuous)).trans α⟧

/-- **Discrete monodromy, local form**, from Brazas–Fischer, *On the failure of the first Čech
homotopy group to register geometrically relevant fundamental group elements*, Bull. London Math.
Soc. 52 (2020), arXiv:1902.08887v2: Proposition 9.13 (one-dimensional metric spaces have the
discrete monodromy property) combined with Remark 9.4(a) and Lemma 9.5 for `H = 1`, base point
`x₀ = x` and `α` constant. For a path `β` between distinct points `x ≠ y` there are neighbourhoods
`U ∋ x`, `V ∋ y` such that `π(c_x, U) ∩ π(β, V) = 1`: a loop at `x` in `U` that is homotopic to
`β δ β⁻` for a loop `δ` at `y` in `V` is null-homotopic. (This is also exactly what the proof of
Prop. 9.13(b) establishes.)

The paper's Lemma 6.2 cites Prop. 9.13 for a statement that is a consequence of this one; here
Lemma 6.2 is derived from this axiom (`Peano.OnlyIf`). -/
axiom exists_nhds_monodromy (X : Type) [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {x y : X} (hxy : x ≠ y) (β : Path x y) :
    ∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 y, ∀ (γ : Path x x) (δ : Path y y), Set.range γ ⊆ U →
      Set.range δ ⊆ V → γ.Homotopic ((β.trans δ).trans β.symm) → γ.Homotopic (Path.refl x)

/-- **Theorem 6.6** of the paper, from Eda, *One-dimensional Peano continua with zero-dimensional
wild part*, Fund. Math. 259 (2022) 243–253 (abstract): for one-dimensional Peano continua whose wild
parts are zero-dimensional **and non-empty**, homeomorphic wild parts imply homotopy equivalence.

The hypothesis "non-empty" is in Eda's abstract and missing from the paper's quotation; without it
the statement is false (a point and a circle). Only the direction "homeomorphic wild parts ⇒
homotopy equivalent" is assumed (the converse is Brazas–Fischer Thm 9.15, proved in
`Peano.BrazasFischer`). Eda's wild part is the set of points at which `X` is not semilocally simply
connected, which for locally path-connected spaces is `loopWildSet`. Zero-dimensional is Mathlib's `ZeroDimensionalSpace` (a basis of clopen
sets), equivalent for compact metric spaces to covering dimension `0`. Eda's full text was not
inspected. Used for injectivity in the corrected Theorem 1.2. -/
axiom eda_homotopyEquiv_of_homeomorph (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (hXne : (loopWildSet X).Nonempty) (hYne : (loopWildSet Y).Nonempty)
    (hX0 : ZeroDimensionalSpace (loopWildSet X)) (hY0 : ZeroDimensionalSpace (loopWildSet Y))
    (φ : loopWildSet X ≃ₜ loopWildSet Y) : Nonempty (ContinuousMap.HomotopyEquiv X Y)

/-! ### Inputs of Part A (§2–3); used only by the paper's own route to Lemma 6.4 -/

/-- **Remark 2.7**, existence half, from Cannon–Conner, *On the fundamental groups of
one-dimensional spaces*, Topology Appl. 153 (2006), Theorem 3.9 (checked against the restatement in
Constantine–Lafont, arXiv:1209.3709, Thm 2.10, for compact path-connected one-dimensional metric
spaces; Cannon–Conner's text was not inspected): every loop is homotopic rel end points to a reduced
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
curve). -/
axiom exists_simpleClosedCurve (X : Type) [MetricSpace X] [PathConnectedSpace X]
    (hX : CoveringDimLE 1 X) {x : X} (α : Path x x) (hα : ¬ α.Homotopic (Path.refl x)) :
    ∃ c : C(AddCircle (1 : ℝ), X), Function.Injective c

end Peano
