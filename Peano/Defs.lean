module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card

/-!
# Basic notions for one-dimensional Peano continua

Definitions used to state Brazas–Pavešić, *Countable models of one-dimensional Peano continua*
(arXiv:2610.35875), Theorem 1.1. See `notes/structure.md`.

* **Peano continuum.** Not a definition: a *Peano continuum* is a connected, locally path-connected,
  compact metrizable space; theorems take `[MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyPathConnectedSpace X]`. A metric is fixed rather than only metrizability, which changes
  nothing for the statements (every metrizable space carries a compatible metric).
* **One-dimensional.** `CoveringDimLE n X`: Lebesgue covering dimension `≤ n`, i.e. every finite
  open cover has a finite open refinement of order `≤ n + 1` (every point lies in at most `n + 1`
  members). One-dimensional means `CoveringDimLE 1 X`. Mathlib has no covering dimension.
* **Infinite earring.** `earring ⊆ ℝ × ℝ` is the union over `k ∈ ℕ` of the circle `C k` of radius
  `r k = 1/(k+1)` centred at `(r k, 0)`, written by its equation (the product metric on `ℝ × ℝ`
  is the sup metric, so `Metric.sphere` would give squares). The paper indexes circles from `1`;
  here from `0`. `earringLoop k` traverses `C k` once from the base point `(0, 0)`.
* **Fully essential maps and the wild set** (Definitions 2.1–2.2): `f : earring → X` is fully
  essential if every loop `f ∘ ℓₖ` is not null-homotopic; `wildSet X` is the set of points at
  which a fully essential map is based.
* **Induced maps on homotopy groups.** Mathlib has `π_ n X x` (`HomotopyGroup.Pi`) and
  `ZerothHomotopy X` but no induced maps; `HomotopyGroup.map` and `ZerothHomotopy.map` are defined
  here by post-composition.
* **Weak homotopy equivalence** (Definition 2.4): bijective on `π₀` and on every `πₙ`, `n ≥ 1`, at
  every base point. Bijectivity of the induced function is stated; that it is a group
  homomorphism is automatic for post-composition and is not part of the definition.
* **Serre fibration.** Homotopy lifting for every cube `Iⁿ`, `n ≥ 0`.
* **Standard form** (Definition 4.1), encoded through parametrisations `h i : I → X` of the closures
  of the arcs; see `IsStandardForm` for the encoding and why it matches the paper.
-/

@[expose] public section

open Set Topology unitInterval
open scoped Topology.Homotopy

noncomputable section

namespace Peano

/-! ### Covering dimension -/

/-- Lebesgue covering dimension `≤ n`: every finite open cover of `X` has a finite open
refinement in which every point lies in at most `n + 1` members. -/
def CoveringDimLE (n : ℕ) (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (ι : Type) [Finite ι] (U : ι → Set X), (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
    ∃ (κ : Type) (_ : Finite κ) (V : κ → Set X), (∀ j, IsOpen (V j)) ∧ (⋃ j, V j) = univ ∧
      (∀ j, ∃ i, V j ⊆ U i) ∧ ∀ x, {j | x ∈ V j}.ncard ≤ n + 1

/-! ### The infinite earring -/

/-- Radius of the `k`-th circle of the earring, `1/(k+1)`. -/
def earringRadius (k : ℕ) : ℝ := 1 / (k + 1)

/-- The `k`-th circle of the earring: radius `earringRadius k`, centred at
`(earringRadius k, 0)`. -/
def earringCircle (k : ℕ) : Set (ℝ × ℝ) :=
  {p | (p.1 - earringRadius k) ^ 2 + p.2 ^ 2 = earringRadius k ^ 2}

/-- The infinite (Hawaiian) earring `𝔼 = ⋃ₖ Cₖ ⊆ ℝ²`. -/
def earring : Set (ℝ × ℝ) := ⋃ k, earringCircle k

/-- The base point `b₀ = (0, 0)` of the earring. -/
def earringBase : earring :=
  ⟨(0, 0), mem_iUnion.2 ⟨0, by simp [earringCircle]⟩⟩

/-- Parametrisation of the `k`-th circle starting at the origin, as a map `ℝ → ℝ²`. -/
def earringParam (k : ℕ) (t : ℝ) : ℝ × ℝ :=
  (earringRadius k - earringRadius k * Real.cos (2 * Real.pi * t),
    earringRadius k * Real.sin (2 * Real.pi * t))

/-- `earringParam k t` lies on the earring (on its `k`-th circle; the finer statement is
`earringParam_mem_earringCircle` in `Peano.Earring`). -/
lemma earringParam_mem (k : ℕ) (t : ℝ) : earringParam k t ∈ earring :=
  mem_iUnion.2 ⟨k, by
    simp only [earringCircle, earringParam, mem_ofPred_eq]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]⟩

/-- The loop `ℓₖ` traversing the `k`-th circle of the earring once, based at `b₀`. -/
def earringLoop (k : ℕ) : Path earringBase earringBase where
  toFun t := ⟨earringParam k t, earringParam_mem k t⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold earringParam
    fun_prop
  source' := by ext <;> simp [earringParam, earringBase]
  target' := by ext <;> simp [earringParam, earringBase]

/-! ### Wild sets -/

/-- Definition 2.1: a map `f : 𝔼 → X` is *fully essential* if every loop `f ∘ ℓₖ` is essential,
i.e. not homotopic rel endpoints to the constant loop.

Based versus free: the paper calls a loop essential if it is not null-homotopic, without saying
whether the homotopy fixes the base point. For loops the two notions agree: a loop is freely
homotopic to a constant loop iff it is null-homotopic rel endpoints (a free null-homotopy makes the
loop homotopic rel endpoints to a conjugate `p · const · p⁻¹`, which is trivial). So the based
version used here is no restriction. -/
def FullyEssential {X : Type*} [TopologicalSpace X] (f : C(earring, X)) : Prop :=
  ∀ k, ¬ ((earringLoop k).map f.continuous).Homotopic (Path.refl (f earringBase))

/-- Definition 2.2: the *wild set* `w(X)`, the points at which some fully essential map
`(𝔼, b₀) → (X, x)` is based. -/
def wildSet (X : Type*) [TopologicalSpace X] : Set X :=
  {x | ∃ f : C(earring, X), f earringBase = x ∧ FullyEssential f}

/-! ### Induced maps on homotopy groups -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Post-composition of a generalised loop with a map. -/
def GenLoop.map {N : Type*} (f : C(X, Y)) {x : X} (γ : Ω^ N X x) : Ω^ N Y (f x) :=
  ⟨f.comp γ.1, fun y hy => by simp [γ.2 y hy]⟩

/-- Post-composition with `f` preserves homotopy of generalised loops (rel `∂Iⁿ`). -/
lemma GenLoop.map_homotopic {N : Type*} (f : C(X, Y)) {x : X} {γ δ : Ω^ N X x}
    (h : GenLoop.Homotopic γ δ) : GenLoop.Homotopic (GenLoop.map f γ) (GenLoop.map f δ) := by
  obtain ⟨H⟩ := h
  exact ⟨H.compContinuousMap f⟩

/-- The map `f# : πₙ(X, x) → πₙ(Y, f x)` induced by `f`. -/
def HomotopyGroup.map (f : C(X, Y)) (n : ℕ) (x : X) : π_ n X x → π_ n Y (f x) :=
  Quotient.map (GenLoop.map f) fun _ _ h => GenLoop.map_homotopic f h

/-- The map `f# : π₀(X) → π₀(Y)` induced by `f` on path components. -/
def ZerothHomotopy.map (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  Quotient.map f fun _ _ h => h.map f.continuous

/-- Definition 2.4(2): `f` is a *weak homotopy equivalence* if it induces a bijection on path
components and a bijection (hence a group isomorphism) `πₙ(X, x) → πₙ(Y, f x)` for every
`n ≥ 1` and every `x`. -/
def IsWeakHomotopyEquivalence (f : C(X, Y)) : Prop :=
  Function.Bijective (ZerothHomotopy.map f) ∧
    ∀ n, 1 ≤ n → ∀ x, Function.Bijective (HomotopyGroup.map f n x)

/-- `p : E → B` is a *Serre fibration*: it has the homotopy lifting property for every cube
`Iⁿ`, `n ≥ 0`. -/
def IsSerreFibration (p : C(X, Y)) : Prop :=
  ∀ (n : ℕ) (F : C((Fin n → I) × I, Y)) (f₀ : C(Fin n → I, X)), (∀ y, p (f₀ y) = F (y, 0)) →
    ∃ G : C((Fin n → I) × I, X), (∀ y, G (y, 0) = f₀ y) ∧ ∀ z, p (G z) = F z

/-! ### Standard form -/

/-- The open unit interval `(0, 1)` inside `I`. -/
def openUnit : Set I := {t | (0 : ℝ) < t ∧ (t : ℝ) < 1}

/-- Definition 4.1, *standard form*: `X ∖ w(X)` is a disjoint union (as a space) of countably or
finitely many open arcs `Oᵢ`, the closure of each being an arc or a simple closed curve whose
end points lie in `w(X)`.

Encoding: each `Oᵢ` is given as `hᵢ((0, 1))` for a map `hᵢ : I → X`, injective on `(0, 1)`, with
`hᵢ 0, hᵢ 1 ∈ w(X)` (the paper fixes exactly such maps in the proofs of Lemma 4.3 and §5). Since
`I` is compact and `hᵢ(0), hᵢ(1) ∉ Oᵢ`, `hᵢ` restricts to a homeomorphism `(0, 1) ≃ Oᵢ` and
`closure Oᵢ = hᵢ(I)`, an arc if `hᵢ 0 ≠ hᵢ 1` and a simple closed curve otherwise. "Disjoint union"
is the topological sum: the `Oᵢ` are pairwise disjoint, cover `X ∖ w(X)`, and each is open in
`X ∖ w(X)`. -/
def IsStandardForm (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ (ι : Type) (h : ι → C(I, X)),
    (∀ i, InjOn (h i) openUnit) ∧
    (∀ i, h i 0 ∈ wildSet X ∧ h i 1 ∈ wildSet X) ∧
    Pairwise (fun i j => Disjoint (h i '' openUnit) (h j '' openUnit)) ∧
    (⋃ i, h i '' openUnit) = (wildSet X)ᶜ ∧
    ∀ i, IsOpen ((↑) ⁻¹' (h i '' openUnit) : Set ((wildSet X)ᶜ : Set X))

end Peano
