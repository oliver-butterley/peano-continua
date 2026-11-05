module

public import Peano.Defs

/-!
# Arc systems

The abstract structure behind a standard-form Peano continuum (Brazas–Pavešić, Definition 4.1),
used for §4 and §5: a closed set `W ⊆ X` whose complement is a disjoint union of open arcs
`Oᵢ = hᵢ((0,1))`, each open in `X`, with end points `hᵢ 0, hᵢ 1 ∈ W`.

Design choice: the arguments of §4 and §5 never use one-dimensionality nor the definition of the
wild set through the earring (confirmed by the checks `notes/checks/B.md`, `C.md`), so they are
stated for an `ArcSystem`; a standard-form continuum gives one with `W = w(X)`
(`IsStandardForm.exists_arcSystem` in `Peano.Main`, using the cited Lemma 2.3). This file holds
only definitions, so that §4 (`Peano.StandardForm`) and §5 (`Peano.Coarsify`) can be developed
independently.

Each arc is given by its parametrisation `h i : I → X` as in the paper (`Oᵢ = hᵢ((0,1))`,
`Ōᵢ = hᵢ(I)`, `∂Oᵢ = {hᵢ 0, hᵢ 1}`).
-/

@[expose] public section

open Set Topology unitInterval

noncomputable section

namespace Peano

/-- A closed set `W ⊆ X` whose complement is the disjoint union of the open arcs
`Oᵢ = hᵢ((0, 1))`, each open in `X`, `hᵢ` injective on `(0, 1)`, with end points
`hᵢ 0, hᵢ 1 ∈ W`. -/
structure ArcSystem (X : Type*) [TopologicalSpace X] where
  /-- The closed set (the wild set, for a standard-form continuum). -/
  W : Set X
  isClosed_W : IsClosed W
  /-- Index type of the arcs. -/
  ι : Type
  /-- Parametrisation of the closure of the `i`-th arc. -/
  h : ι → C(I, X)
  injOn : ∀ i, InjOn (h i) openUnit
  mem_W : ∀ i, h i 0 ∈ W ∧ h i 1 ∈ W
  disjoint : Pairwise fun i j => Disjoint (h i '' openUnit) (h j '' openUnit)
  iUnion_eq : (⋃ i, h i '' openUnit) = Wᶜ
  isOpen_arc : ∀ i, IsOpen (h i '' openUnit)

namespace ArcSystem

variable {X : Type*} [MetricSpace X] (S : ArcSystem X)

/-- The open arc `Oᵢ = hᵢ((0, 1))`. -/
def arc (i : S.ι) : Set X := S.h i '' openUnit

/-- The closed arc `Ōᵢ = hᵢ(I)`. -/
def closedArc (i : S.ι) : Set X := range (S.h i)

/-- The end points `∂Oᵢ = {hᵢ 0, hᵢ 1}`. -/
def ends (i : S.ι) : Set X := {S.h i 0, S.h i 1}

end ArcSystem

end Peano
