# Adversarial review of the axioms (Peano formalisation)

Reviewer: an independent agent, which did not read the project's own assessments under `notes/`.
Files reviewed: `Peano/Axioms/Cited.lean`, `Peano/Axioms/Standard.lean` and `Peano/Defs.lean`.
Sources were downloaded to `papers/dl_bm/`, `papers/dl_bf/` and `papers/dl_mp/` (gitignored).

## Verdict

**I found no FATAL problem.** Each of the four axioms is, as stated in Lean, a true theorem, given
its source. The earring, the wild set, the fully essential maps, covering dimension and weak
homotopy equivalence are encoded faithfully. I checked the Lean elaboration of the earring radius:
it is real division. I found no way to derive `False` from the axioms together with the
definitions.

- `isClosed_wildSet` and `nonempty_homeomorph_wildSet` were checked against their sources and are
  weaker than those sources.
- `HomotopyEquiv.isWeakHomotopyEquivalence` is a standard fact that holds for arbitrary spaces.
- `exists_homotopyEquiv_standardForm` (Meilstrup) is the weakest link in the trust boundary. Its
  primary source, the 2005 Master's thesis, could not be downloaded: the Brigham Young University
  (BYU) repository sits behind a Cloudflare challenge. I checked it against two other sources: the
  paper's own statement, and a restatement by the same authors in arXiv:2510.22901 (Theorem 3.10
  and the paragraph before it).
  - The added hypothesis `(wildSet X).Nonempty` is necessary. Without it the axiom is
    inconsistent; the reasoning is below.
  - With it, the axiom matches the restated source.
  - The Lean `IsStandardForm` is equivalent to Definition 4.1 for metric spaces, and slightly
    weaker, because countability is not required. So the axiom asks for no more than the source
    provides.

The remaining findings are MINOR or NOTE: citation precision, unverified primary source, and
scope remarks.

---

## 1. `isClosed_wildSet` (paper Lemma 2.3, Brazas–Mitra)

**Source comparison: verified.** I checked the statement against arXiv:2505.23665 (Brazas–Mitra,
*Higher homotopy wild sets*). The result is **Proposition 2.9** there: "If X is first countable
and locally path-connected, then wₙ(X) is closed in X." The case n = 1 is the paper's Lemma 2.3.
In that preprint, Brazas–Mitra's `w₁` is defined through fully essential maps 𝔼 → X, as in the
paper's Definition 2.2. Their proof of Proposition 2.9 shows a point is wild by producing "a
sequence of essential based maps … which converges to x". That shrinking-sequence criterion is
equivalent to the fully essential one in first-countable spaces.

The Lean statement requires `[MetricSpace X] [LocallyPathConnectedSpace X]`. Metric spaces are
first countable, so it is a special case of the source.

**Independent check that the statement is true.** The argument is elementary:
- In a first-countable space, x ∈ w(X) if and only if every neighbourhood of x contains an
  essential loop based at x.
  - (⇐) Pick essential loops αₙ in a decreasing countable neighbourhood base. Then define
    f ∘ ℓₙ = αₙ; the map is continuous at b₀ because the loops shrink.
  - (⇒) Given a neighbourhood U, f⁻¹(U) contains the circle Cₖ for all large k, so f ∘ ℓₖ is an
    essential loop at x inside U.
- If xₙ → x with xₙ wild, take a path-connected neighbourhood U of x. It contains some xₙ, and so
  an essential loop at xₙ inside U. Conjugating that loop by a path in U from x to xₙ gives an
  essential loop at x inside U.

Mathlib's `LocallyPathConnectedSpace` gives a basis of path-connected neighbourhoods, which is
enough for this argument.

**Degenerate cases.**
- X empty, or a point: the wild set is empty, which is closed.
- Circle, arc, finite graph: the wild set is empty, which is closed.
- The earring: the wild set is {b₀}, which is closed.

**Findings.**
- **MINOR (citation).** The docstring calls the result "Lemma 2.3 … from Brazas–Mitra" without
  the source numbering. The result is **Brazas–Mitra, arXiv:2505.23665, Proposition 2.9** (case
  n = 1), with Corollary 2.10 for Peano continua. The docstring should cite it that way. There is
  no change to the statement.
- **NOTE (strength).** The axiom is weaker than its source (metric instead of first countable),
  which is acceptable. It is also provable outright from the definitions, by the argument above.
  The only real work in Lean is building a continuous map on the earring from a null sequence of
  loops. That gluing lemma would also be reusable elsewhere. Keeping it as an axiom is a
  defensible cost/benefit choice, not a soundness issue.

---

## 2. `exists_homotopyEquiv_standardForm` (paper Theorem 4.2, Meilstrup)

**Source comparison: partly verified.**
- **Primary source not obtained.** The thesis PDF (BYU ScholarsArchive, `etd/550`) is behind a
  Cloudflare challenge and could not be downloaded. Its abstract mentions "reduced forms" only.
- **Paper's statement.** Read in the paper (lines 226–242 of the text extraction), and checked
  against Definition 4.1.
- **Same authors' restatement.** Brazas–Pavešić, *Motion planning on one-dimensional Peano
  continua*, arXiv:2510.22901, §3, restate it as follows.
  > "M. Meilstrup proved that every one-dimensional Peano continuum X is homotopy equivalent to a
  > one-dimensional Peano continuum Y, where w(X) = w(Y) and Y∖w(Y) is a disjoint union of a
  > sequence of open arcs O₁, O₂, …, where Ōₙ is a closed arc or simple closed curve, and
  > Ōₙ∖Oₙ ⊆ w(Y). A modified proof appears in [Eda, Fund. Math. 209 (2010)]. The homotopy
  > equivalence q : X → Y is a quotient map, which collapses to a point each member of a countable
  > collection of dendrites."

  Their Theorem 3.10, which refines this, explicitly assumes **w(X) ≠ ∅**.
- **From memory.** Eda's 2010 version is likewise stated for continua that are not homotopy
  equivalent to graphs, that is, with w(X) ≠ ∅.

**The added hypothesis `hw` is necessary.** I confirmed this independently. Take X a point, an arc,
a circle or any finite graph; then w(X) = ∅.
- The Lean `IsStandardForm Y` with Y nonempty forces w(Y) ≠ ∅. If the index type ι is empty, the
  union of the arcs equals w(Y)ᶜ = ∅, so Y = w(Y). Otherwise `h i 0 ∈ wildSet Y`.
- A homotopy equivalence is π₁-injective in both directions. By the paper's Lemma 2.5 it therefore
  maps w(Y) into w(X) = ∅.

So the version without `hw` proves `False`. The paper's Theorem 4.2, quoted literally with
Definition 4.1, is false for finite graphs: a graph minus the empty set is not a union of open arcs
with end points in ∅. The hypothesis is a correct repair. It costs nothing for the main theorem
only if the case w(X) = ∅ is handled separately; see the NOTE below.

**With `hw`, the Lean statement is no stronger than the restated source.** I checked each part of
the conclusion.
1. `X' : Type` with a metric, compact, connected and locally path-connected: Y is a Peano
   continuum, a metrizable space of cardinality at most continuum, so it can be modelled in
   `Type`.
2. `CoveringDimLE 1 X'`: Y is one-dimensional, by the source.
3. `IsStandardForm X'`: equivalent to Definition 4.1 for Hausdorff X', and slightly weaker, as
   argued in the Definitions section below.
4. `Nonempty (X ≃ₕ X')`: given by the source.

The source's extra content (w(X) = w(Y), a quotient map, countability) is dropped, which is fine.

**Elaboration check.** In `∃ (X' : Type) (_ : MetricSpace X'), CompactSpace X' ∧ …`, all later
instances (`CompactSpace`, `wildSet`, `HomotopyEquiv`) are resolved from the bound metric. No
other topology on `X'` exists, so elaboration could not have picked a different one.

**Hunting false instances with `hw`.**
- **The earring X = 𝔼.** Take X' = 𝔼 itself with hᵢ = ℓᵢ. Then 𝔼 ∖ {b₀} is the disjoint union
  of the open arcs Cᵢ ∖ {b₀}, each open in 𝔼 ∖ {b₀}. The statement is satisfiable.
- **w(X) = X** (Menger curve, Sierpiński carpet). Take ι empty; then the union is ∅ = w(X)ᶜ. The
  statement holds.
- **𝔼 with a circle hung on an arc at a non-wild point.** Collapsing the arc gives 𝔼 ∨ S¹ at b₀,
  which is in standard form. This is consistent.
- **Two earrings joined by an arc.** The arc is an open arc with both end points wild. This is
  consistent.

No counterexample found.

**Findings.**
- **MINOR (unverified primary source).** The axiom rests on the paper's citation plus the same
  authors' restatement. I could not compare it with the thesis text. Before publication, someone
  should obtain the thesis or Eda (2010) and check two things:
  - (a) the exact standard-form notion, in particular that every component of Y∖w(Y) is an open
    arc and not, say, an open arc together with dendrites;
  - (b) the precise hypothesis for the w = ∅ case.

  The Brazas–Pavešić restatement is consistent with the Lean statement on both points.
- **NOTE (scope).** Because of `hw`, the converse direction of Theorem 1.1 for w(X) = ∅ cannot
  use this axiom. In that case X is semi-locally simply connected and homotopy equivalent to a
  finite graph, which needs its own argument or another cited fact. The paper's proof silently
  covers this case through Theorem 4.2 as stated, which is false there. Whoever uses the axiom must
  supply that case. I have not checked how the formalisation does this.
- **NOTE (strength).** The axiom is no stronger than needed. If downstream proofs could use
  `wildSet X' = image of wildSet X` or countability of ι, the source would support adding them,
  but adding them is not necessary.

---

## 3. `nonempty_homeomorph_wildSet` (Brazas–Fischer, Theorem 9.15)

**Source comparison: verified.** I checked the statement against arXiv:1902.08887v2 (Brazas–Fischer,
Bull. London Math. Soc. 52 (2020)).
- **Theorem 9.15:** "Suppose both X and Y have the discrete monodromy property. If f : X → Y is a
  homotopy equivalence with homotopy inverse g : Y → X, then f maps w(X) homeomorphically onto
  w(Y), with inverse g|w(Y)."
- **Proposition 9.13:** "All one-dimensional metric spaces and all planar spaces have the discrete
  monodromy property."
- Section 9 assumes X is path connected, which holds for Peano continua.
- In Brazas–Fischer, w(X) is the set of points at which X is **not semilocally simply connected**.
  For first-countable spaces, this set equals the Definition 2.2 set used in Lean, by the argument
  in §1: "every neighbourhood U of x contains a loop at x that is essential in X".

**Lean vs source.** Lean assumes two Peano continua with `CoveringDimLE 1` and a homotopy
equivalence `e`. It concludes only `Nonempty (wildSet X ≃ₜ wildSet Y)`. That is strictly weaker
than the source in its conclusion (no link to `e`), and its hypotheses are stronger (compact and
locally path-connected, beyond one-dimensional metric and path-connected). The argument is
summarised in the proof given after Corollary 9.18:
- π₁-isomorphisms map w(X) into w(Y) and back;
- homotopic maps into a space with discrete monodromy agree on w(X) when they are π₁-injective;
- so g ∘ f = id on w(X) and f ∘ g = id on w(Y).

**Degenerate cases.**
- Point ≃ₕ arc ≃ₕ tree: both wild sets are empty, and the empty subtypes are homeomorphic.
- Circle ≃ₕ figure-eight is impossible, so there is nothing to check.
- 𝔼 ≃ₕ 𝔼 with a whisker: both wild sets are singletons.
- Remark 9.16's counterexample 𝔼 ≃ₕ 𝔼 × I is excluded because 𝔼 × I is two-dimensional, so
  `CoveringDimLE 1` fails for it. The Lean definition of `CoveringDimLE` is the genuine Lebesgue
  definition, so this exclusion is real.

**Findings.**
- **NOTE (dimension convention).** `CoveringDimLE 1` means dim ≤ 1. It also admits the point
  (dim 0), which is harmless. Brazas–Fischer's "one-dimensional" is the Curtis–Fort / Cannon–Conner
  usage, under which the reduced-path theory applies to all spaces of dim ≤ 1.
- **NOTE (strength).** The axiom is weaker than the source and adequate for its stated use (moving
  countability of w across the Meilstrup equivalence). Lemma 6.4 of the paper would also give
  injectivity of h|w(X′) without this axiom, but that route needs Eda's Theorem 6.1, so this choice
  is economical.
- **MINOR (bibliography).** The Bull. LMS volume is given as 52 in the paper and 50 on Brazas's web
  page. The paper's 52 is correct (2020, no. 6, 1072–1092). The docstring is fine.

---

## 4. `HomotopyEquiv.isWeakHomotopyEquivalence` (Hatcher)

**Source comparison: from memory.**
- Hatcher, *Algebraic Topology*, Proposition 1.18: a homotopy equivalence induces isomorphisms on
  π₁ at every base point.
- Hatcher §4.1 gives the analogous statement for πₙ, with the same proof: the change-of-basepoint
  isomorphism along the track of the homotopy g ∘ f ≃ id.
- On π₀ the induced map is bijective because homotopic maps induce the same map on path
  components.

The statement holds for **arbitrary** topological spaces, so the universe-polymorphic `Type*` with
only `[TopologicalSpace]` is sound.

**Lean vs definition.**
- `IsWeakHomotopyEquivalence` asks for a bijection on `ZerothHomotopy`, and for `n ≥ 1` and every
  x a bijection `π_ n X x → π_ n Y (f x)`.
- Mathlib's `π_ n X x = HomotopyGroup (Fin n) X x` is the set of homotopy classes, rel boundary,
  of maps Iⁿ → X sending ∂Iⁿ to x. That is the usual πₙ for n ≥ 1.
- `HomotopyGroup.map` is post-composition, which is well defined.

The statement is true.

**Degenerate cases.**
- Empty X and Y: both π₀ are empty, which is bijective, and there are no base points.
- n = 0 is excluded from the πₙ clause and handled by `ZerothHomotopy`; `π_ 0` would be a
  different object.
- X empty and Y nonempty admit no homotopy equivalence.

**Findings.**
- **NOTE.** The citation "§4.1, p. 342" should be checked against the edition. In the 2002 printing,
  the πₙ statement for homotopy equivalences is in §4.1 near Proposition 4.1 and the basepoint-change
  discussion. This is not a soundness issue.
- **NOTE.** This is the most provable of the four. π₀ is easy. π₁ follows from Mathlib's
  fundamental groupoid functor (`FundamentalGroupoid` and homotopy invariance). Only the case
  n ≥ 2 genuinely lacks Mathlib infrastructure.

---

## Definitions the axioms depend on

- **`earringRadius`: correct.** It elaborates to `fun k => 1 / (↑k + 1)` in ℝ, which I checked
  with `#print`. `earringRadius 1 = 1/2` is provable by `norm_num`, so the division is not natural
  number division. With ℕ division every circle except the first would have degenerated to a
  point, and every space would have empty wild set.
- **`earringCircle`, `earring`: correct.** Each circle is a genuine Euclidean circle
  (x−r)² + y² = r², centred at (r, 0) and passing through the origin. The space is the subspace of
  ℝ × ℝ with the product topology, which is the Euclidean topology (checked with `pp.explicit`).
  The union is the Hawaiian earring. The indexing from 0 (radii 1, 1/2, …) is the same set as the
  paper's 1/k, k ≥ 1. The earring is closed in ℝ², but closedness is never used: only the subspace
  topology enters `C(earring, X)`.
- **`earringLoop`: correct.** `earringParam k t = (r − r cos 2πt, r sin 2πt)` starts and ends at
  (0, 0) and traverses Cₖ exactly once.
  - **MINOR (docstring).** Near t = 0 the y-coordinate is positive while the point is the leftmost
    point of Cₖ, so the loop runs *clockwise*. The paper says counterclockwise. Orientation is
    irrelevant to essentiality, so there is no mathematical consequence; a module comment would
    avoid confusion.
- **`FullyEssential`: matches Definition 2.1.** "f ∘ ℓₖ is not path-homotopic to the constant
  loop" is equivalent to "f ∘ ℓₖ : S¹ → X is essential", because a loop is freely null-homotopic
  if and only if it is null-homotopic rel base point.
- **`wildSet`: matches Definition 2.2 exactly.** It is defined for arbitrary spaces, as in the
  paper.
- **`CoveringDimLE n`: the correct Čech–Lebesgue definition.**
  - Every finite open cover has a finite open refinement of order ≤ n + 1, and `ncard` is honest
    because κ is finite.
  - It agrees with the usual dimension for separable metric spaces.
  - "One-dimensional" is taken as dim ≤ 1. This differs from dim = 1 only at the one-point
    continuum, which has empty wild set and is harmless for every axiom. Axiom 2 excludes it via
    `hw`, and axioms 3 and 4 are true for it.
  - Satisfiable, and not too weak: the disc does not satisfy `CoveringDimLE 1`, by the Lebesgue
    covering theorem.
- **`IsStandardForm`: equivalent to Definition 4.1 for metric (indeed Hausdorff) X; slightly weaker
  in allowing uncountable ι.**
  - *Lean ⇒ paper.* From `InjOn (h i) (0,1)` and `h i 0, h i 1 ∈ w(X)`, while `h i '' (0,1) ⊆ w(X)ᶜ`,
    the end point values lie outside Oᵢ. For C closed in (0,1) with closure C̄ in I, h(C̄) is
    compact and therefore closed. Since h(0), h(1) ∉ Oᵢ, h(C̄) ∩ Oᵢ = h(C). So h restricts to a
    homeomorphism (0,1) ≅ Oᵢ. Then Ōᵢ = h(I) is an arc or a simple closed curve, and
    Ōᵢ ∖ Oᵢ = {h 0, h 1} ⊆ w(X). Pairwise disjointness, the union equal to X ∖ w(X), and each Oᵢ
    open in X ∖ w(X) together give the topological sum.
  - *Paper ⇒ Lean.* O ≅ (0,1) is a dense connected subset of an arc or simple closed curve Ō, so it
    is Ō minus its end points, or minus one point. A parametrisation h of Ō therefore exists. Every
    point of Ō ∖ O lies in w(X), which gives the end point conditions.
  - The equivalence uses Hausdorffness. The definition is stated for an arbitrary
    `TopologicalSpace`, but it is only used for metric X'.
  - **NOTE.** In a compact metric space countability is automatic: the Oᵢ are disjoint and open in
    X, since w(X) is closed, and X is separable. So the weakening loses nothing.
  - **Conclusion.** The axiom cannot demand more than Meilstrup provides.
- **`HomotopyGroup.map`, `ZerothHomotopy.map`, `IsWeakHomotopyEquivalence`: match Definition 2.4(2).**
  Bijectivity is stated in place of "isomorphism", which is equivalent because post-composition is
  a homomorphism.

## Summary of labelled findings

| Axiom | Label | Finding |
|---|---|---|
| `isClosed_wildSet` | MINOR | Cite Brazas–Mitra arXiv:2505.23665 **Prop. 2.9** (n = 1) explicitly |
| `isClosed_wildSet` | NOTE | Weaker than the source; elementary and provable with an earring gluing lemma |
| `exists_homotopyEquiv_standardForm` | MINOR | Primary source (thesis) not inspected; verified only against the paper and Brazas–Pavešić arXiv:2510.22901 §3 |
| `exists_homotopyEquiv_standardForm` | NOTE | `hw` is necessary (else `False`); the w(X) = ∅ case of Theorem 1.1 needs a separate argument |
| `exists_homotopyEquiv_standardForm` | NOTE | Conclusion no stronger than the source; `IsStandardForm` is equivalent to Definition 4.1, with countability dropped |
| `nonempty_homeomorph_wildSet` | NOTE | Verified against Theorem 9.15 and Proposition 9.13; Brazas–Fischer's w(X) (points that are not semilocally simply connected) equals Definition 2.2 in metric spaces; the Lean axiom is weaker |
| `nonempty_homeomorph_wildSet` | NOTE | dim ≤ 1 convention, which is harmless |
| `HomotopyEquiv.isWeakHomotopyEquivalence` | NOTE | True for all spaces; check the page reference; the π₀ and π₁ parts are provable from Mathlib |
| `earringLoop` (definition) | MINOR | Clockwise, not counterclockwise as in the paper; no mathematical effect |

No FATAL or MAJOR findings.
