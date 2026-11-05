# Independent review of definitions and statements (Peano/*.lean)

Reviewed: `Peano/Defs.lean`, `Peano/StandardForm.lean`, `Peano/Coarsify.lean`,
`Peano/WeakEquiv.lean`, `Peano/Main.lean` against Brazas–Pavešić, arXiv:2610.35875 (closures
checked in the PDF, pp. 5–7). Axiom files not reviewed. All five files elaborate without errors
(checked with `lean_diagnostic_messages` on `Peano/Main.lean`).

## Verdict

No FATAL findings. Every definition matches the paper (or a standard equivalent), and every
theorem statement is, as far as I can determine, true as written and not vacuous. The arc-system
abstraction is sound: a standard-form continuum with closed wild set is an `ArcSystem` with
`W = w(X)`, and the arguments of §§4–5 use only the fields it has. The restriction
`(wildSet X).Nonempty` in the general layer of Theorem 1.1 is needed, because the paper's
Theorem 4.2 (Meilstrup) is false when `w(X) = ∅`. It is documented, but it leaves a case of
Theorem 1.1 unformalised (MINOR, scope). Two gaps in the paper's proof of Lemma 5.5 matter for
whoever proves it. The Lean Lemma 5.4, faithful to the paper, is too weak for the Lemma 5.5
proof as written in the paper. I propose a strengthened statement (MINOR). The rest are NOTEs.

## Defs.lean

### `CoveringDimLE` — correct
- NOTE. This is the standard finite-open-cover definition of Lebesgue covering dimension
  `≤ n` (order `≤ n + 1` = each point in at most `n + 1` members). `κ` is `Finite`, so
  `{j | x ∈ V j}` is a finite set and `ncard` is the true cardinality. The behaviour
  `Set.Infinite.ncard : s.ncard = 0` (confirmed in Lean) can never trigger, so there is no
  vacuity. The refinement condition `∀ j, ∃ i, V j ⊆ U i` is correct. The universe restriction
  `ι κ : Type` is harmless (finite index types). For compact metric spaces this agrees with every
  other usual definition of dimension.
- NOTE. "One-dimensional" in the paper means `dim X = 1`; `CoveringDimLE 1` also admits
  `dim 0`, i.e. the one-point continuum. Theorem 1.1 holds there trivially, so this weakening of
  the hypothesis is harmless.

### `earring`, `earringLoop` — correct
- NOTE. `(x − r)² + y² = r²` with `r = 1/(k+1)` is exactly the circle of radius `r` centred at
  `(r, 0)`. The circles meet pairwise only at `(0,0)`, and the subspace topology from the product
  topology on `ℝ × ℝ` is the Euclidean one. The docstring is right that `Metric.sphere` would give
  squares. Indexing from 0 instead of 1 is harmless.
- NOTE. `earringParam k t = (r − r cos 2πt, r sin 2πt)` leaves the origin with `y > 0`, i.e. it
  runs **clockwise** (angle about the centre is `π − 2πt`). The paper says counterclockwise.
  This does not matter, because essentiality is invariant under reversal. If desired, the
  docstring could say "once" without an orientation, or the sign of the second coordinate could
  be flipped.

### `FullyEssential`, `wildSet` (Definitions 2.1–2.2) — correct
- NOTE. The paper says `f ∘ ℓⱼ : S¹ → X` is essential (free homotopy). The Lean version uses
  "not path-homotopic rel endpoints to the constant loop". These agree: a based loop is freely
  null-homotopic iff its class in `π₁` is conjugate to, hence equal to, the identity.
  `wildSet` is literally Definition 2.2. Non-vacuity: the identity of the earring is fully
  essential, so `b₀ ∈ wildSet earring`.

### `GenLoop.map`, `HomotopyGroup.map`, `ZerothHomotopy.map`, `IsWeakHomotopyEquivalence` — correct
- NOTE. `π_ n X x = HomotopyGroup (Fin n) X x`, and the map is post-composition, well defined on
  homotopy classes (the proof is given). For `n ≥ 1`, `HomotopyGroup.group` provides the group
  structure on `π_ n` (`Fin n` is nonempty). The post-composition map is a homomorphism (this
  holds mathematically, though it is not proved in Lean), and a bijective homomorphism is an
  isomorphism. Bijectivity is therefore equivalent to Definition 2.4(2). It is quantified over
  all `n ≥ 1` and all base points, as in the paper. `ZerothHomotopy` is Mathlib's path-component
  quotient. Faithful.

### `IsSerreFibration` — correct
- NOTE. This is the standard homotopy lifting property for every cube `Iⁿ`, `n ≥ 0`.

### `IsStandardForm` (Definition 4.1) — correct for Hausdorff `X`
The PDF confirms that the paper says `Ōₙ` is an arc or simple closed curve with
`Ōₙ \ Oₙ ⊆ w(X)`.

- Lean ⇒ paper (for Hausdorff `X`). The docstring's argument is right. `h(0), h(1) ∈ w(X)`
  and `Oᵢ ⊆ w(X)ᶜ` give `hᵢ⁻¹(Oᵢ) = (0,1)`. The map `hᵢ : I → hᵢ(I)` is closed (compact to
  Hausdorff), and a closed map restricted to a full preimage is closed, so `(0,1) ≅ Oᵢ`. Also
  `closure Oᵢ = hᵢ(I)` (compact, hence closed, and contained in the closure of `hᵢ((0,1))`). This
  is an arc if `hᵢ 0 ≠ hᵢ 1` and a simple closed curve otherwise, and `Ōᵢ \ Oᵢ ⊆ {hᵢ 0, hᵢ 1}`.
- Paper ⇒ Lean. `X` is compact and `Oₙ ≅ (0,1)` is not, so `Ōₙ ≠ Oₙ`. A dense connected subset
  of an arc that is homeomorphic to `(0,1)` must be the arc minus both end points (minus one end
  point gives `[0,1)`). In a simple closed curve it must be the curve minus one point. So `hₙ`
  exists. "Disjoint union" is correctly read as the topological sum (pairwise disjoint, each
  relatively open).
- NOTE. Countability of the index set is not required. It is automatic: once `w(X)` is closed
  (Lemma 2.3), the `Oᵢ` are disjoint nonempty open sets of a separable space.
- NOTE. `IsStandardForm` takes only `[TopologicalSpace X]`, but the argument above needs
  Hausdorffness. It is only used under `[MetricSpace X]`, so this is harmless. Optionally add
  `[T2Space X]` to the docstring's claim.
- NOTE (consequence that matters). For nonempty `X` with `w(X) = ∅`, `IsStandardForm X` is
  false. No arc can have end points in `∅`, so `ι` is empty, so `X = ⋃ ∅ = ∅`. The paper's
  definition behaves the same way (`Ōₙ \ Oₙ ≠ ∅` by compactness). See Theorem 1.1 below.

## StandardForm.lean

### `ArcSystem` — sound abstraction
- Every standard-form `X` with `w(X)` closed (Lemma 2.3) gives an `ArcSystem` with
  `W = w(X)`: "open in `w(X)ᶜ`" plus "`w(X)ᶜ` open" gives `isOpen_arc`. All other fields are
  copied. I checked the proofs of Lemmas 4.3, 4.5, 5.2 and 5.5: they use only compactness, local
  path-connectedness, the metric, `W` closed, the arcs open and disjoint with end points in `W`,
  and the separation of `W` from `Oₙ` by `{aₙ, eₙ}`. All of these follow from the fields.
  One-dimensionality and connectedness are not used. Nothing is missing, and nothing is too
  strong.
- NOTE. `isClosed_W` is redundant. `iUnion_eq` and `isOpen_arc` already give
  `Wᶜ = ⋃ open sets`. Harmless.
- NOTE. `ι` need not be countable. It is countable automatically, because the arcs are disjoint,
  nonempty and open in a compact metric (hence separable) space. `countable_coarse` needs this
  fact, so prove it as a lemma.

### Lemma 4.3 `tendsto_diam_closedArc` — correct, true
- `Tendsto … cofinite (𝓝 0)` is exactly "`diam Ōₙ → 0`" for any enumeration, and it is trivial
  for finitely many arcs. The closure matches the PDF. `Metric.diam` of a compact set is the true
  diameter.
- NOTE (for the prover). The paper's proof has a gap. `zᵢ ∉ Uₓ ∪ U_y` does **not** give
  `z ∉ B̄(x, δ/2) ∪ B̄(y, δ/2)`, since `Uₓ` need not contain a ball. Also `aₙᵢ ∈ Uₓ ⊆ B(x, δ)`
  is not disjoint from `U_z` merely because `U_z` avoids `B̄(x, δ/2)`. Robust fix: pick
  `zᵢ ∈ Ōₙᵢ` with `d(zᵢ, x) = ρ` for a fixed `ρ` strictly between the distances to the end-point
  limits (intermediate value theorem on the connected `Ōₙᵢ`). Then `z ∈ W` has `d(z, x) = ρ`, and
  a small path-connected `U_z` must contain an end point, which is far away. If both end points
  converge to `x`, use `ρ = ε/4` instead. The statement itself is true.

### Corollary 4.4 `eventually_closedArc_subset` — correct, slightly more general, true
- An injective `u : ℕ → ι` tends to `cofinite`, so it replaces `n₁ < n₂ < ⋯` correctly. It is
  vacuous for finitely many arcs, matching the paper's hypothesis "infinite". The Lean version
  allows `e k` to be either end point of arc `u k`, where the paper uses a fixed `aₙ`. This is
  more general and still follows immediately from Lemma 4.3. `x ∈ W` is omitted but automatic
  (`W` closed, `e k ∈ W`). Closures match the PDF.

### Lemma 4.5 `isOpen_iff_localCondition` — correct, true
- The PDF confirms that (2) is `U ∩ Ōₙ` open in `Ōₙ` and (3) concludes `Ōₙᵢ ⊆ U`, with
  `xₙᵢ ∈ ∂Oₙᵢ` and `x ∈ U ∩ w(X)`. The Lean statement matches. `∂Oᵢ = Ōᵢ \ Oᵢ = {hᵢ 0, hᵢ 1}`
  because `Oᵢ` is open.
- Closures are essential. With open arcs in (2) the "if" direction is false. Example: a circle
  with `W = {p}`, one arc, and `U = {p}`. Here (1) holds, (2) for the open arc holds since
  `U ∩ O = ∅`, and (3) is vacuous, but `U` is not open. The Lean version with closures is true.
  Proof sketch for "if": take `x ∈ U ∩ W` and `yₖ → x` with `yₖ ∉ U`. By (1), eventually
  `yₖ ∈ O_{iₖ}`. If some `i` repeats infinitely often, then `x ∈ ∂Oᵢ` and (2) gives a
  contradiction. Otherwise pass to an injective subsequence and use Lemma 4.3 and (3). "Only if"
  is Corollary 4.4.

## Coarsify.lean

### `firstHalf`, `secondHalf`, `label`, `Coarse`, `q` — correct
- The `Bᵢ` and `Dᵢ` are pairwise disjoint across all `i` and both halves:
  `Bᵢ, Dᵢ ⊆ Oᵢ`, the `Oᵢ` are pairwise disjoint, and `Bᵢ ∩ Dᵢ = ∅` by injectivity on `(0,1)`.
  So `hb.choose` and `hd.choose` are determined uniquely, and the branch order is irrelevant. The
  fibres of `label` are exactly the `Bᵢ`, the `Dᵢ` and the singletons, which is the paper's
  identification (collapsing the singletons `Cₙ` is a no-op). The quotient topology is used.
  Faithful.

### Remark 5.1 `countable_coarse` — correct, true
- `Coarse = q(W) ∪ {bᵢ, cᵢ, dᵢ}`, since `iUnion_eq` puts every point in `W` or some `Oᵢ`.
  Countability of `ι` must be derived as noted above.

### Lemma 5.2 `isOpenMap_q` — correct, true (the paper's proof works for `ArcSystem`).

### Lemma 5.4 `exists_extension_preimage_eq` — faithful but insufficient for Lemma 5.5 (MINOR)
- The statement is true for metric `B` (perfectly normal), including the edge cases `A = ∅`
  (take `k ≡ ½`) and `A = B`. The restriction from perfectly normal to metric is harmless here,
  because every space it is applied to is a subspace of a metric `B`.
- MINOR. The paper's proof of Lemma 5.5 has a gap, and patching it needs a stronger extension
  lemma. The paper claims `g(∂U(bₙ)) ⊆ {aₙ, cₙ}`, but a boundary point `s` of
  `U(bₙ) = g⁻¹(bₙ) \ A` may lie in `A` with `g(s) = bₙ`. Counterexample: `B = I`, `A = {0}`,
  `g ≡ bₙ`, and `f(0) ∈ Bₙ`. Then `U(bₙ) = (0, 1]` and `∂U(bₙ) = {0}`, while
  `βₙ(0) = f(0) ∈ Bₙ` is not an end point. Lemma 5.4 therefore cannot be applied as written. The
  fix is to extend `βₙ : ∂U → Āₙ ≅ [0,1]` continuously to the closure of `U` with values in
  `(0,1)` on `U` itself: use Tietze, then pull towards `½` by a weight that is positive off `∂U`.
  Proposed replacement (the paper's 5.4 is the special case where `h` is `{0,1}`-valued):
  ```lean
  theorem exists_extension_interior {B : Type*} [MetricSpace B] {A : Set B} (hA : IsClosed A)
      (h : C(A, I)) :
      ∃ k : C(B, I), (∀ a : A, k a = h a) ∧ ∀ b ∉ A, (0 : ℝ) < k b ∧ (k b : ℝ) < 1 := by
    sorry
  ```
  Keep the current statement if you want fidelity, but plan to use this one in the proof of 5.5.
- NOTE (also for the Lemma 5.5 prover). The paper's continuity argument asserts
  `g(s) ∈ w(X) ∪ {cₙ}` for limits `s` of points in `⋃ (U(bₙ) ∪ U(dₙ))`. It misses the case
  `s ∈ A` with `g(s) ∈ {bₙ, dₙ}`. That case is easy (`{bₙ}` is open, so the sequence eventually
  lies in `U(bₙ)` and continuity of `hₙ` on the closure applies), but it must be handled. The
  extensions `hₙ`, `kₙ` must be defined on the closures of `U(bₙ)` and `U(dₙ)`, not on
  `U(bₙ)` and `U(dₙ)` themselves.

### Lemma 5.5 `exists_lift` — correct, true
- The hypotheses match the paper: `B` locally path-connected and metrizable (a metric is fixed,
  which is harmless), `A` closed, and `q ∘ f = g|_A`. The conclusion `G|_A = f`, `q ∘ G = g` is
  the commuting diagram. With the two patches above, the paper's proof goes through in the
  `ArcSystem` generality.

## WeakEquiv.lean

### `HasCubeLifting`, `isSerreFibration_of_hasCubeLifting`, `isWeakHomotopyEquivalence_of_hasCubeLifting`, `IsWeakHomotopyEquivalence.comp` — correct, true
- `n = 0`, `A = ∅` gives surjectivity (`Fin 0 → I` is a point), hence `π₀` surjectivity.
  `(I, {0,1})` gives `π₀` injectivity. `(Iⁿ, ∂Iⁿ)` gives `πₙ` surjectivity, and
  `(Iⁿ⁺¹, ∂Iⁿ⁺¹)` with the data "bottom/top lifts, constant on the sides" gives injectivity, at
  every base point. Serre: `(Iⁿ⁺¹, Iⁿ × {0})`, transported along
  `(Fin n → I) × I ≃ₜ (Fin (n+1) → I)`, which is a proof-only obligation. Composition is
  immediate (`HomotopyGroup.map` of a composite is the composite, definitionally on
  representatives).
- NOTE (proof obligation). Mathlib has **no** instance
  `LocallyPathConnectedSpace (Fin n → I)` (confirmed: instance synthesis fails). Applying
  `exists_lift` in `hasCubeLifting_q` requires proving it, e.g. from convexity (cubes are
  locally convex subsets of a normed space).

## Main.lean

### `hasCubeLifting_q`, `isSerreFibration_q`, `isWeakHomotopyEquivalence_q` (Corollary 5.6) — correct, true
- They are stated for an arbitrary `ArcSystem` on a compact, locally path-connected metric space.
  This is more general than the paper (no dimension or connectedness hypothesis), and still true
  by the reasoning above.

### `IsStandardForm.exists_arcSystem` — correct (given Lemma 2.3).

### `exists_countable_weq_of_standardForm` — correct, faithful, non-vacuous
- It is the "if" direction for standard-form `X`. `hdim` is unused but harmless. It is
  non-vacuous: the earring satisfies every hypothesis (`w = {b₀}`, and the arcs are the
  punctured circles). Restricting to `X Y : Type` is harmless, since Peano continua have
  cardinality at most the continuum.

### `exists_countable_weq` (general layer) — MINOR (scope)
- MINOR. The extra hypothesis `(wildSet X).Nonempty` is justified. Theorem 4.2 as stated in the
  paper is false when `w(X) = ∅`: no nonempty space with empty wild set is in standard form (see
  `IsStandardForm`), and a space homotopy equivalent to `X` also has empty wild set (Lemma 6.4).
  So the paper's own proof does not cover this case. Still, the Lean theorem is strictly weaker
  than Theorem 1.1 ("if") and should be reported as such. To close the gap: a one-dimensional
  Peano continuum with `w(X) = ∅` is homotopy equivalent to a finite graph, which is weakly
  equivalent to a finite space (McCord). Alternatively, state the full theorem with an explicit
  extra axiom for that case:
  ```lean
  theorem exists_countable_weq_full (X : Type) [MetricSpace X] [CompactSpace X]
      [ConnectedSpace X] [LocallyPathConnectedSpace X] (hdim : CoveringDimLE 1 X)
      (hw : (wildSet X).Countable) :
      ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
        ∃ f : C(X, Y), IsWeakHomotopyEquivalence f
  ```
  derived from `exists_countable_weq` plus a separate (cited or proved) result for
  `wildSet X = ∅`.
- Otherwise the hypotheses match Theorem 1.1: Peano continuum, `dim ≤ 1`, `w(X)` countable. The
  conclusion is "there is a countable `Y` and a weak homotopy equivalence `X → Y`". The statement
  is not trivially true: a weak homotopy equivalence must be bijective on all `πₙ`, so `Y` is
  not arbitrary.
