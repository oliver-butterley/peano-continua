module

public import Peano.Defs
public import Peano.Arcs
public import Peano.LoopWildSet
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

/-- **Meilstrup's arc-reduced form** (paper Theorem 4.2, and the finite-graph case it omits), from
Meilstrup, *Classifying homotopy types of one-dimensional Peano continua*, Master's thesis, Brigham
Young University, 2005 (inspected 2026-11-05, `papers/Classifying Homotopy Types…`):

* **Theorem 2.9.** "Let `X` be a one-dimensional Peano continuum with `B(X) ≠ ∅`. Then there is a
  continuum `Y` homotopy equivalent to `X`, with `G(Y)` a disjoint union of a null sequence of
  (open) arcs." The proof shows that `Y` is a one-dimensional Peano continuum.
* **Corollary 2.10.** "If `X` is a one-dimensional Peano continuum with `B(X) = ∅` then `X` is
  homotopy equivalent to a bouquet of finitely many (possibly zero) circles."

Here `B(X)` is the set of *bad points*, those with no simply connected (open) neighbourhood, and
`G(X) = X ∖ B(X)`.

**Encoding of `B(X)`.** For a one-dimensional Peano continuum, `B(X) = loopWildSet X = wildSet X`
(`Peano.badSet_eq_loopWildSet`, `Peano.badSet_eq_wildSet` in `PeanoPartA.BadPoints`; the inclusion
`B ⊆ loopWildSet` uses Brazas–Pavešić Lemma 2.8 (`fundamentalGroup_map_val_injective`) and so the
Cannon–Conner axioms of `PeanoPartA`, which is why
that proof is kept out of the main library: it checks this statement and is not used by any
proof). The hypothesis is stated with `loopWildSet` (Meilstrup's `B(X) ≠ ∅`), the conclusion with
`wildSet` (inside `IsStandardForm`, which equals `B(X')` since `X'` is again a one-dimensional
Peano continuum).

**Encoding of "arc-reduced".** `IsStandardForm X'` (the paper's Definition 4.1). The statement of
Theorem 2.9 says only that `G(Y)` is "a disjoint union of […] (open) arcs"; Definition 4.1 also asks
that the closure of each arc be an arc or a simple closed curve with end points in `B(Y)`. The
proof of Theorem 2.9 gives both (`notes/axioms.md`, "Meilstrup Theorem 2.9 and Definition 4.1"):
`Y` is the quotient of `X` collapsing each ray `r(x)` from a vertex of the locally finite graph
`G(X)` to its limit point `b(x) ∈ B(X)`; `G(Y)` is the disjoint union of the images of the open
edges of `G(X)` that lie on no ray, each open in `Y`; the two end vertices of each such edge are
sent to points `b(·)` of `B(Y)`, so its closure is an arc, or a simple closed curve if both go to
the same point; the map `g` "slides the end thirds to their endpoints in `B(Y)`". Independently,
in a Peano continuum every open arc that is open in the space has convergent ends, so the closure
condition follows from the topological-sum reading of "disjoint union". Countability ("null
sequence") is not asserted (it is not needed, and pairwise disjoint open sets in a separable space
are
countably many).

**Case `B(X) = ∅`.** A bouquet of `n` circles is encoded as a compact metric space with an
`ArcSystem` with finitely many arcs and finite `W` (weaker than the thesis, which has `W` a
single point; zero circles is a point, `W` a singleton, no arcs). The paper overlooks this case
(its Theorem 4.2 drops Meilstrup's hypothesis `B(X) ≠ ∅`, and is false without it: a non-empty
standard-form space has non-empty wild set, and homotopy equivalences preserve emptiness of `w`);
it is needed for the case `w(X) = ∅` of Theorem 1.1.

In both cases `X'` is a one-dimensional Peano continuum (the thesis says so for Theorem 2.9; a
finite bouquet is one). -/
axiom exists_homotopyEquiv_arcReduced (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) :
    ∃ (X' : Type) (_ : MetricSpace X'), CompactSpace X' ∧ ConnectedSpace X' ∧
      LocallyPathConnectedSpace X' ∧ CoveringDimLE 1 X' ∧
      Nonempty (ContinuousMap.HomotopyEquiv X X') ∧
      ((loopWildSet X).Nonempty → IsStandardForm X') ∧
      (loopWildSet X = ∅ → ∃ S : ArcSystem X', S.W.Finite ∧ Finite S.ι)

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
wild part*, Fund. Math. 259 (2022) 243–253, Theorem 1.1 (checked against the 2020 preprint,
`papers/0dim.pdf`, l.47–50): for one-dimensional Peano continua whose wild parts are
zero-dimensional **and non-empty**, homeomorphic wild parts imply homotopy equivalence.

The hypothesis "non-empty" is in Eda's Theorem 1.1 and published abstract and missing from the
paper's quotation (the preprint's abstract also omits it, a plausible source of the slip); without
it the statement is false (a point and a circle). Only the direction "homeomorphic wild parts ⇒
homotopy equivalent" is assumed (the converse is Brazas–Fischer Thm 9.15, proved in
`Peano.BrazasFischer`). Eda's wild part is the set of points at which `X` is not semilocally simply
connected, which is exactly `loopWildSet`. Zero-dimensional is Mathlib's `ZeroDimensionalSpace`
(a basis of clopen sets), equivalent for compact metric spaces to covering dimension `0`; Eda uses
clopen partitions. The converse direction is Eda's Remark 1.2. Used for injectivity in the
corrected Theorem 1.2. -/
axiom eda_homotopyEquiv_of_homeomorph (X Y : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [LocallyPathConnectedSpace Y] (hX : CoveringDimLE 1 X)
    (hY : CoveringDimLE 1 Y) (hXne : (loopWildSet X).Nonempty) (hYne : (loopWildSet Y).Nonempty)
    (hX0 : ZeroDimensionalSpace (loopWildSet X)) (hY0 : ZeroDimensionalSpace (loopWildSet Y))
    (φ : loopWildSet X ≃ₜ loopWildSet Y) : Nonempty (ContinuousMap.HomotopyEquiv X Y)

end Peano
