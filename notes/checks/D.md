# Referee check D: Section 6 of Brazas–Pavešić, "Countable models of one-dimensional Peano continua" (arXiv:2610.35875)

Scope: Lemma 6.3, Lemma 6.4, Remark 6.5, proof of Theorem 1.1 (both directions), proof of Theorem 1.2, and the way the cited results (Theorem 6.1 = Eda 2002, Lemma 6.2 = Brazas–Fischer 2020 Prop. 9.13, Theorem 6.6 = Eda 2022, Brazas–Fischer 2020 Thm. 9.15, Meilstrup's Theorem 4.2) are quoted and applied. Sections 2–5 are taken as given.

Sources consulted: the paper's text and PDF (pp. 10–13); Brazas–Fischer, arXiv:1902.08887v2 (= ref. [5]), Section 9, read in full; the abstract of Eda 2022 (Fund. Math. 259) on the IMPAN site; a secondary quotation of Eda's 2002 theorem in C. Kent, arXiv:1305.4215. I could **not** access Eda 2002 (Topology Appl. 123) or Meilstrup's thesis. Statements about them marked "(memory)" rely on my recollection or on the secondary source.

## Verdict

Theorem 1.1 is correct, but the proof as written has fixable gaps. The "only if" direction (via Lemmas 6.3 and 6.4) holds after small repairs. These are: an unjustified "reduced" hypothesis when Lemma 3.4 is applied; a mis-cited Lemma 6.2; local path-connectedness, which Lemma 6.3 uses but does not assume; and Theorem 6.1, which is quoted only for Peano continua although Lemma 6.4 is stated for general path-connected, locally path-connected one-dimensional metric spaces. None of these touches the main theorems, because every use there is on a Peano continuum. The "if" direction overlooks the case w(X) = ∅, where no standard form in the sense of Definition 4.1 exists; the repair is easy (finite graphs). **Theorem 1.2 is false as stated.** The circle S¹ and a point are one-dimensional Peano continua with empty wild set. Each admits a weak homotopy equivalence to a finite (hence countable) space, but they are not homotopy equivalent. Neither is homotopy equivalent to any A_λ, because those have non-empty wild sets. In addition, Eda's Theorem 6.6 really requires **non-empty** zero-dimensional wild sets, and the paper omits that hypothesis. Restrict Theorem 1.2 to continua with non-empty wild set (equivalently, those that are not semilocally simply connected) and to non-zero compact countable ordinals; then the proof is correct up to minor details of the construction of A_λ. Alternatively, add a separate ℕ-indexed family of homotopy types, the wedges of n circles. There is also a long list of typos and label confusions, mostly in Lemma 6.4.

---

## Lemma 6.3

**Statement (paraphrase).** Let X be a one-dimensional metrizable space and x ∈ w(X). Then there is a map f : (𝔼, b₀) → (X, x) with [f∘ℓₙ]_h ≠ 0 in H₁(X) for every n. Here 𝔼 is the infinite earring and [·]_h is the first-homology class.

**Verdict: correct with minor gap.**

- **MINOR (hypothesis not available).** The proof starts from "a neighbourhood base U₁ ⊇ U₂ ⊇ … of *path-connected* open sets at x". This requires X to be locally path-connected at x, which is not assumed. The statement is still true. Repair, avoiding local path-connectedness: since X is metrizable (so first countable), x ∈ w(X) gives, for each n, a loop βₙ based at x with Im βₙ ⊆ B(x, 1/n) that is essential in X. (A fully essential map f : 𝔼 → X based at x yields such loops f∘ℓⱼ for large j, because f(Cⱼ) → x.) Then:
  - Pₙ = Im βₙ is a Peano continuum (Hahn–Mazurkiewicz). It has dimension at most 1, since dimension is monotone on subsets of metrizable spaces.
  - By Lemma 2.8, βₙ is essential in Pₙ.
  - So Pₙ contains a simple closed curve Cₙ (next bullet), and an arc ηₙ ⊆ Pₙ from x to Cₙ. Truncate ηₙ at its first hit of Cₙ.

  The rest of the proof is unchanged, with Uₙ replaced by B(x, 1/n). In Lemma 6.4, X is locally path-connected, so the gap is harmless there.
- **MINOR (the "well-known fact" is misstated).** "A one-dimensional metrizable space is simply connected iff it contains no simple closed curve" is false as written: a two-point discrete space contains no simple closed curve and is not simply connected, because it is not path-connected. The correct statement is: *every loop in a one-dimensional metrizable space is null-homotopic iff the space contains no simple closed curve.* Proof sketch:
  - (⇐) The image P of an essential loop α is a Peano continuum of dimension at most 1, and α is essential in P by Lemma 2.8. A Peano continuum with no simple closed curve is a dendrite. Dendrites are absolute retracts, hence contractible (Nadler, *Continuum Theory*, Ch. 10; Borsuk). This contradicts α being essential in P.
  - (⇒) A simple closed curve is π₁-injectively included, by Lemma 2.8.

  The paper should state the corrected version and cite it (Curtis–Fort 1959, or Cannon–Conner 2006).
- **MINOR (notation).** "cₙ = γ(0)" should read γₙ(0). The point cₙ is then redefined as ηₙ(1). Choose γₙ *after* ηₙ, based at ηₙ(1). Note also that the symbols cₙ and Cₙ already denote points and sets of the coarsification in Section 5.
- **NOTE (injective path).** A path-connected Hausdorff space is arc-connected. Take an arc in Uₙ from x to a point of the closed set Cₙ and truncate it at its first hitting time to get ηₙ with Im ηₙ ∩ Cₙ = {cₙ}. This is fine.
- **NOTE (continuity of f: checked).** f is defined circle by circle with f(b₀) = x and Im(f∘ℓₙ) ⊆ Uₙ. A function on 𝔼 that is continuous on each circle Cₙ is continuous on 𝔼 iff every neighbourhood of f(b₀) contains f(Cₙ) for all but finitely many n. That holds because (Uₙ) is a nested neighbourhood base. So the loops do shrink to x.
- **NOTE ("clearly homologous": checked).** For paths, a concatenation αβ is homologous as a 1-chain to α + β, and η̄ is homologous to −η. Hence [ηₙγₙη̄ₙ]_h = [γₙ]_h. Also, γₙ represents a generator of H₁(Cₙ) ≅ ℤ, being injective on [0, 1), so Lemma 3.3 applies.
- **NOTE (reducedness, needed later).** The loop ηₙγₙη̄ₙ is reduced: ηₙ is injective, γₙ is injective on [0, 1), and Im ηₙ ∩ Cₙ = {cₙ}. Any subloop with equal endpoints is therefore trivial, γₙ itself, or a conjugate of γₙ, and the last two are essential. The paper never says this, but Lemma 6.4 needs it (or the alternative repair below). The lemma also yields, implicitly, that f is fully essential: non-zero homology class implies essential loop.

## Lemma 6.2 (citation check)

**Statement as quoted.** X is a one-dimensional metric space; f₁, f₂ : 𝔼 → X are fully essential; α is a path from f₂(b₀) to f₁(b₀) with f₁∘ℓⱼ ≃ ᾱ(f₂∘ℓⱼ)α for all j. Then α(0) = α(1).

**Verdict: correct statement, wrong citation (MINOR).**

- **MINOR (mis-citation).** Brazas–Fischer Prop. 9.13 (arXiv:1902.08887v2) says only: "All one-dimensional metric spaces and all planar spaces have the discrete monodromy property." The quoted statement follows from Prop. 9.13 together with Lemma 9.5, by the argument of Lemma 9.17 of that paper. That argument has to be adapted, because Lemma 9.17 assumes ϕ_β∘f# = g# on the whole fundamental group, whereas here only the generators [ℓⱼ] are matched.

  The argument: suppose f₂(b₀) ≠ f₁(b₀). Lemma 9.5 with discrete monodromy gives neighbourhoods U of f₂(b₀) and V of f₁(b₀) with π(c, U) ∩ π(α, V) = {1}. For large j, the class [f₂∘ℓⱼ] = [α(f₁∘ℓⱼ)ᾱ] lies in both groups, so it is trivial. This contradicts f₂ being fully essential. So Lemma 6.2 is a valid consequence of the cited paper, but it is not its Prop. 9.13. Brazas–Fischer's Section 9 assumes X path-connected; in Lemma 6.4, X is path-connected.

## Lemma 6.4

**Statement (paraphrase).** Let X be a path-connected, locally path-connected, one-dimensional metric space, and Y a path-connected space. If f : X → Y induces an isomorphism on π₁, then f restricted to w(X) is an injective map w(X) → w(Y).

**Verdict: gap as stated. Correct, after minor repairs, when X is a one-dimensional Peano continuum, which covers every use in the paper.**

- **MAJOR, for the lemma as stated; harmless for the main theorems (Theorem 6.1 is applied outside its quoted hypotheses).** Theorem 6.1 is quoted for X a *one-dimensional Peano continuum*. Lemma 6.4 assumes only a path-connected, locally path-connected, one-dimensional metric X, and the proof applies Theorem 6.1 to that X.
  - Kent's arXiv:1305.4215 (Theorem A) attributes to Eda a version with domain a one-dimensional Peano continuum (such as 𝔼) and target *any* one-dimensional metric space. Dorfer–Thuswaldner–Winkler (Fund. Math. 223, 2013, Thm. 5.10) prove it for metrizable one-dimensional *continua*.
  - I could not check which hypotheses Eda 2002, Theorem 1.1 itself carries.

  Repair: either restrict Lemma 6.4 to one-dimensional Peano continua (all three uses — Theorem 1.1 "only if", Theorem 1.1 "if", and implicitly the introduction — concern Peano continua), or quote and cite the version of Eda's theorem for arbitrary one-dimensional metric targets.
- **MINOR (labels g₀/g₁/g₂).** The text introduces g₀, g₁ and then "construct[s] g₂ : (𝔼, b₀) → (X, x₀) as in the proof of Lemma 6.3". This must be g₀: Figure 5 and the definition of h use g₀ as the special map at x₀. Later, "g₂" is reused for a different map, g₂∘ℓⱼ = g∘ℓ₂ⱼ. Rename the second one, for instance g′. The special g₀ is fully essential, since non-zero homology classes are essential.
- **NOTE (h is well defined and continuous: checked).** h∘ℓ₂ⱼ₋₁ = f∘g₀∘ℓⱼ and h∘ℓ₂ⱼ = f∘g₁∘ℓⱼ.
  - All circles send b₀ to y₀, so h is well defined.
  - Let V be an open set containing y₀. Then (f∘gᵢ)⁻¹(V) is a neighbourhood of b₀ in 𝔼, so it contains Cⱼ for j ≥ Jᵢ. Hence h(Cₖ) ⊆ V for k ≥ 2·max(J₀, J₁).
  - Together with continuity on each circle, this gives continuity of h. The check is direct: preimages of open sets are open in 𝔼. No first countability or Hausdorffness of Y is needed.
  - The same argument shows that g′ = g∘(shift), with g′∘ℓⱼ = g∘ℓ₂ⱼ, and g₃ are continuous.
- **NOTE (Theorem 6.1 diagram).** φ_δ∘g# = f#⁻¹∘h# gives f#[δ̄(g∘ℓⱼ)δ] = [h∘ℓⱼ]. Checked. Typo: "f#([g₁∘ℓⱼ]) in π₁(X, x₁)" should be "in π₁(Y, y₀)".
- **MINOR (application of Lemma 6.2 needs g′ fully essential; not stated).** Apply Lemma 6.2 with f₁ = g₁, f₂ = g′ and α = δ. Since δ̄(g∘ℓ₂ⱼ)δ ≃ g₁∘ℓⱼ is essential, g∘ℓ₂ⱼ is essential, so g′ is fully essential. Conclusion: x₂ = x₁. Correct once this is stated. Note that δ is now a loop at x₁, not necessarily trivial; the proof correctly keeps it.
- **NOTE (choice of n with disjoint images: checked).**
  - Im(g₀∘ℓₙ) → x₀ because Im(g₀∘ℓₙ) ⊆ Uₙ.
  - Im(g₃∘ℓₙ) = Im(g∘ℓ₂ₙ₋₁) → g(b₀) = x₁ by continuity of g.
  - X is Hausdorff and x₀ ≠ x₁, so for large n the two images lie in disjoint neighbourhoods.

  This uses x₂ = x₁ in an essential way.
- **NOTE (commutator: checked).**
  - a = [h∘ℓ₂ₙ₋₁] = [f∘g₀∘ℓₙ].
  - b = [f∘α] is a loop at y₀, since f(x₀) = f(x₁).
  - L = α·(δ̄(g₃∘ℓₙ)δ)·ᾱ·(g₀∘ℓₙ)‾ is a loop at x₀, and [f∘L] = bab⁻¹a⁻¹.
- **NOTE (Hurewicz: checked).** X and Y are path-connected by hypothesis, so H₁ ≅ π₁^ab naturally. The abelianisation of an isomorphism is an isomorphism, so f_* is injective on H₁. Surjectivity of f# is genuinely used here: injectivity of f# alone would not give injectivity on H₁. Typo: "[L] = 0" should be "[L]_h = 0".
- **MINOR (typo in the cancellation).** "[L]_h = [g₃∘ℓₙ]_h − [g₃∘ℓₙ]_h" should be "[g₃∘ℓₙ]_h − [g₀∘ℓₙ]_h". The chain-level cancellation is correct: α and ᾱ cancel, and δ̄ and δ cancel.
- **MINOR (Lemma 3.4 requires reduced loops; g₃∘ℓₙ need not be reduced).** Lemma 3.4 needs both loops reduced, with disjoint images, in a path-connected one-dimensional metrizable space.
  - Path-connected: yes.
  - g₀∘ℓₙ is reduced by the construction of Lemma 6.3, though the paper does not argue this; see the note there.
  - g₃∘ℓₙ = g∘ℓ₂ₙ₋₁ comes from Eda's theorem and is arbitrary.

  Repair: replace both loops by their reduced representatives (Remark 2.7). Each has image inside the original loop's image, so the images stay disjoint. Path-homotopic loops are homologous, so the homology classes are unchanged. The contradiction then follows. Also "[g₀∘ℓₙ] ≠ 0" should read "[g₀∘ℓₙ]_h ≠ 0".
- **NOTE.** "f|w(X) is a well-defined continuous function" is fine. The intro's phrase "|w(X)| ≤ |w(Y)|" for weak homotopy equivalences follows, since weak equivalences between path-connected spaces are π₁-isomorphisms. Lemma 2.5 uses Definition 2.2 for w(Y) with Y arbitrary; this is consistent.

## Remark 6.5

**Statement.** f|w(X) need not be bijective. Example: f : 𝔼 → 𝔼 × [0, 1], x ↦ (x, 0).

**Verdict: correct.**

- **NOTE.** f is a homotopy equivalence. The point (b₀, t) is wild, via the fully essential map x ↦ (x, t); the loops are essential in 𝔼 × I because the projection to 𝔼 is a retraction. Every other point has a contractible neighbourhood (arc × interval). So w(𝔼 × [0, 1]) = {b₀} × [0, 1] and f|w(𝔼) is not surjective.
- The sentence "…but w(𝔼 × [0, 1]) … is uncountable" reads as a non sequitur. The point is that w(𝔼) = {b₀} is a single point while the target wild set is larger. The example is Brazas–Fischer's Remark 9.16 and could be credited. The target is two-dimensional, which is necessary: for a homotopy equivalence between one-dimensional metric spaces, the restriction *is* a bijection (Brazas–Fischer Thm. 9.15).

## Theorem 1.1, proof

**Statement.** For a one-dimensional Peano continuum X: there is a weak homotopy equivalence X → Y with Y countable iff w(X) is countable.

**"Only if": correct with minor gap.**

- **NOTE.** Lemma 6.4 needs Y path-connected. This follows because a weak homotopy equivalence is bijective on π₀ and X is path-connected. Say so. X is a one-dimensional Peano continuum, so Theorem 6.1 applies within its quoted hypotheses. Then w(Y) ⊆ Y is countable. Correct.

**"If": correct for w(X) ≠ ∅, with a gap for w(X) = ∅.**

- **MINOR (Meilstrup's theorem does not cover w(X) = ∅).**
  - Definition 4.1 requires X ∖ w(X) to be a disjoint union of open arcs Oₙ with closure(Oₙ) ∖ Oₙ ⊆ w(X).
  - If w(X) = ∅, each Oₙ is clopen, so X is a single non-compact open arc: impossible.
  - Hence no one-dimensional Peano continuum with empty wild set (a point, S¹, a dendrite, a finite graph) is in standard form, and Theorem 4.2 as quoted is false in that case.

  Meilstrup's actual definition presumably treats this case separately (memory; thesis not consulted). Since ∅ is countable, the "if" direction must handle it. Repair:
  - w(X) = ∅ means X is semilocally simply connected.
  - A semilocally simply connected one-dimensional Peano continuum is homotopy equivalent to a finite graph (memory: Curtis–Fort, Cannon–Conner).
  - A finite graph is weakly equivalent to a finite space (McCord, ref. [17]).
- **NOTE (Lemma 6.4 applied to h : X′ → X: hypotheses satisfied).** X′ is a one-dimensional Peano continuum, hence path-connected, locally path-connected and metrizable. X is path-connected. A homotopy equivalence induces isomorphisms on π₁ at every basepoint. So w(X′) injects into w(X) and is countable. Brazas–Fischer Thm. 9.15 would give this directly, as a homeomorphism.
- **NOTE.** "Replacing X with X′" uses that the composite q∘g : X → X′ → C X′ is a weak homotopy equivalence, since homotopy equivalences and weak equivalences compose. Implicit, fine.
- **MINOR (typo).** "C X is a countable set whenever X is countable" should be "whenever w(X) is countable" (Remark 5.1). Remark 5.1 also silently uses that the index set N is countable. It is: the Oₙ are pairwise disjoint open sets in a separable space.

## Theorem 6.6 (citation check)

- **MAJOR (missing hypothesis).** Eda 2022's abstract (IMPAN) reads: "for a one-dimensional Peano continuum X such that X^w is zero-dimensional **and non-empty**, the homeomorphism type of X^w determines the homotopy type of X." The paper omits "non-empty". This hypothesis is genuinely needed, since a point and S¹ both have w = ∅. (Under the convention dim ∅ = −1, "zero-dimensional" already excludes ∅, but the paper does not use it that way in Theorem 1.2.) This omission is what breaks Theorem 1.2; see below.

## Theorem 1.2, proof

**Statement.** There is a canonical bijection between homeomorphism types of compact countable ordinals and homotopy types of one-dimensional Peano continua admitting a weak homotopy equivalence to a countable space.

**Verdict: error in the statement (MAJOR). Correct after restricting to non-empty wild sets and non-zero ordinals, with minor gaps in the construction.**

- **MAJOR (the statement is false at w = ∅).**
  - The point and S¹ are one-dimensional Peano continua (if "one-dimensional" means dim ≤ 1; otherwise take S¹ and S¹ ∨ S¹). They admit weak homotopy equivalences to finite spaces (McCord), are pairwise non-homotopy-equivalent, and have w = ∅.
  - w is a homotopy invariant among one-dimensional metric spaces (Brazas–Fischer Thm. 9.15). Each A_λ (λ ≥ 1) has non-empty wild set, so none of these spaces is in the image: surjectivity fails.
  - If λ = 0 (the empty ordinal, which is compact) is counted, A₀ is undefined: f(max λ) makes no sense. Even with any definition, the single class [0] cannot match the infinitely many homotopy types with w = ∅ (wedges of n circles, n ≥ 0).
  - The surjectivity step "w(X) ≅ λ … hence Ho(X) = Ho(A_λ) by Theorem 6.6" fails exactly here.

  Repair: state Theorem 1.2 for continua that are not semilocally simply connected (w(X) ≠ ∅) and non-zero compact countable ordinals. Or add the countable family {homotopy types of ⋁ⁿ S¹ : n ≥ 0} as a separate summand of the classification.
- **MINOR (ordinal conventions).**
  - "Compact countable ordinal λ" with "f : λ → [0, 1], f(max λ) = 1" treats λ as the set {κ : κ < λ}, which is compact iff λ is a successor (or 0).
  - "For each ordinal κ ≤ λ" treats λ as the space [0, λ] = λ + 1.

  Fix one convention, for example "λ = μ + 1 a countable successor ordinal, κ ranging over κ ≤ μ".
- **MINOR (λ = 1).** For the one-point ordinal, f(0) = 0 and f(max λ) = 1 contradict each other. Treat it separately: A₁ = 𝔼, or 𝔼 with a whisker, which is still a Peano continuum with w = {pt}. Standard form is not needed for Theorem 1.2 in any case.
- **NOTE (existence of f).** A continuous order-preserving embedding exists. Enumerate λ = {κ₁, κ₂, …} and put F(κ) = Σ_{κᵢ < κ} 2^{−i}.
  - F is strictly increasing.
  - At a limit κ, F(κ) = sup_{ξ<κ} F(ξ), by monotone convergence, since any finitely many κᵢ < κ lie below some ξ < κ. So F is continuous in the order topology.
  - A continuous injection from a compact space to a Hausdorff space is an embedding. Normalise by F(max λ) when λ ≥ 2.

  The paper asserts this without proof; one sentence would do.
- **MINOR (construction of the E_κ: unstated conditions).** The proof also needs E_κ ∩ ([0, 1] × {0}) = {(f(κ), 0)}. Otherwise the circles may cross the base segment, and both the wild-set computation and standard form can fail.
  - Round circles through (0, 0) cannot lie in [0, 1] × [0, ∞). So use non-round loops ("teardrops" inside a narrow cone with apex (f(κ), 0)), or allow ℝ × [0, ∞).
  - Pairwise disjointness can be arranged inductively. For example, with round circles tangent to the x-axis from above, earrings of radii r, r′ at abscissae x ≠ x′ are disjoint when 4rr′ < (x − x′)². Enumerate the κ's and choose each rⱼ small with respect to the finitely many earlier ones, and less than 2^{−g(κⱼ)}.

  The paper just says "we choose"; a sentence on why this is possible is warranted.
- **NOTE (A_λ is a one-dimensional Peano continuum with w(A_λ) = f(λ) × {0} ≅ λ: checked).**
  - *Compact.* diam E_κ < 2^{−g(κ)} with g injective, so any sequence from distinct E_κ approaches the base segment; A_λ is closed and bounded.
  - *Locally connected.* A null family of Peano continua attached to an arc, plus compactness, gives local connectedness (standard; Nadler, Ch. 8).
  - *One-dimensional.* Countable sum theorem for closed sets.
  - *Wild points.* Each (f(κ), 0) is wild, via the circles of E_κ, essential by Lemma 2.8. Any other point p has an arc neighbourhood. Only finitely many E_κ have diameter at least dist(p, f(λ) × {0})/2 or at least the height of p, and these are closed and miss p. This includes the endpoint 1 = f(max λ) and limit ordinals, since f(λ) is closed.
  - *Standard form (λ ≥ 2).* The complementary intervals of f(λ) in [0, 1] are exactly (f(κ), f(κ + 1)); together with the punctured circles they give the open arcs.
  - *Zero-dimensional.* A countable metric space is zero-dimensional: around each point, all but countably many radii give clopen balls.
- **NOTE (well-definedness: correct, given non-emptiness).** Independence from λ's representative and from the choices of f, g and E_κ both follow from Theorem 6.6, since every choice gives w(A_λ) ≅ λ. The paper only states the first.
- **NOTE (injectivity: correct).** Brazas–Fischer Thm. 9.15 (checked in arXiv:1902.08887v2) requires both spaces to have the discrete monodromy property. Their Prop. 9.13 provides it for all one-dimensional metric spaces, and their Section 9 assumes path-connectedness; A_λ satisfies both. The theorem gives that a homotopy equivalence maps w homeomorphically onto w. Brazas–Fischer define w by failure of semilocal simple connectivity, which agrees with Definition 2.2 for first countable spaces. Typo: "w(A_λ′) = λ" should be λ′. Alternatively, injectivity follows from the "only if" part of Theorem 6.6.
- **NOTE (surjectivity: correct for w(X) ≠ ∅).**
  - w(X) is compact metrizable (Lemma 2.3) and countable (Theorem 1.1).
  - The "well-known" fact is the Mazurkiewicz–Sierpiński theorem (Fund. Math. 1, 1920; memory for the citation): every non-empty countable compact metric space is homeomorphic to ω^α·n + 1 for a countable α and 1 ≤ n < ω. It should be cited. It also yields the classification of the left-hand side by pairs (α, n).
  - Zero-dimensionality of w(X), needed for Theorem 6.6, is not justified in the paper; see the countable-metric argument above.
- **NOTE ("canonical" and the identification of the target: justified).** The inverse of [λ] ↦ Ho(A_λ) is Ho(X) ↦ [w(X)], which is choice-free and well defined by Brazas–Fischer Thm. 9.15; this justifies "canonical". By Theorem 1.1, "admits a weak homotopy equivalence to a countable space" is equivalent to "w(X) countable". This property is invariant under homotopy equivalence: compose, or use the invariance of w. So the target set is correctly identified, apart from the w = ∅ issue.

## Summary of labelled findings

| # | Location | Label | Finding |
|---|---|---|---|
| 1 | Thm 1.2 / Thm 6.6 | MAJOR | Statement false for w = ∅ (point, S¹, finite graphs); Eda 2022 needs non-empty wild sets; restrict, or add the finite-graph family |
| 2 | Lemma 6.4 / Thm 6.1 | MAJOR (scope only) | Theorem 6.1 is quoted for Peano continua but applied to a general locally path-connected one-dimensional metric X; restrict Lemma 6.4 or cite the general version |
| 3 | Lemma 6.4 end | MINOR | Lemma 3.4 needs reduced loops; g₃∘ℓₙ is not shown reduced; replace both loops by their reduced representatives |
| 4 | Lemma 6.2 | MINOR | Mis-cited: Brazas–Fischer Prop. 9.13 is only "discrete monodromy"; the quoted statement needs Lemma 9.5 and the argument of Lemma 9.17 |
| 5 | Thm 1.1 "if" / Thm 4.2 | MINOR | No standard form when w(X) = ∅; handle via finite graphs and McCord |
| 6 | Lemma 6.3 | MINOR | Uses local path-connectedness, which is not assumed; the "well-known fact" is misstated; repair via images of essential loops and dendrites |
| 7 | Lemma 6.4 | MINOR | g₀/g₂ label mix-up; "g₂" reused; fully-essentialness of g′ not stated; typos in π₁(Y, y₀), [L]_h, [g₀∘ℓₙ]_h |
| 8 | Thm 1.2 | MINOR | Ordinal conventions (λ vs λ+1); λ = 1 contradicts f(0) = 0, f(max) = 1; E_κ must meet the base only at its wild point, and disjoint placement needs a sentence |
| 9 | Thm 1.1 "if" | MINOR | "C X countable whenever X countable" should read "whenever w(X) countable" |
| 10 | various | NOTE | Continuity of f and h, choice of n, the commutator, the Hurewicz step, the A_λ wild-set computation, injectivity via Brazas–Fischer Thm. 9.15, and "canonical" all check out; zero-dimensionality of countable compacta and Mazurkiewicz–Sierpiński should be stated and cited |
