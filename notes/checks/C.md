# Part C referee check: Section 5 of Brazas–Pavešić, "Countable models of one-dimensional Peano continua" (arXiv:2610.35875)

> **Correction (2026-11-05).** This check read the text extraction, which drops the closure bars in
> Lemma 4.5. With the closures of the PDF (`Ōₙ`) the lemma is true; it is proved in Lean as
> `Peano.ArcSystem.isOpen_iff_localCondition`. The statements below that Lemma 4.5 is false, and its
> counterexample, apply only to the misread version.

Scope: the coarsification construction 𝒞X and q : X → 𝒞X, Remark 5.1, Lemma 5.2, Remark 5.3,
Lemma 5.4, Lemma 5.5, Corollary 5.6. Section 4 was taken as given except where its application
had to be checked. Notation used below: W = w(X) (the wild set), F = W ∪ {cₙ : n ∈ N},
B̄ₙ = {aₙ} ∪ Bₙ ∪ {cₙ} = hₙ([0,1/2]), D̄ₙ = {cₙ} ∪ Dₙ ∪ {eₙ} = hₙ([1/2,1]),
∂Oₙ = Ōₙ ∖ Oₙ = {aₙ, eₙ}.

## Verdict

The statements of Section 5 are all true, and Corollary 5.6 (q is a Serre fibration and a weak
homotopy equivalence) follows. The proofs, however, contain one genuine error and several gaps.
The error (MAJOR, Lemma 5.5): the proof asserts g(∂U(bₙ)) ⊆ {aₙ, cₙ}, which fails whenever the
closed set A meets g⁻¹(bₙ). This is exactly the situation in the homotopy-lifting and
basepoint cases that Corollary 5.6 needs, and the proof as written breaks down there. It is fixed
by replacing Lemma 5.4 with a "Tietze extension that keeps the complement in the open interval"
(given below). Lemma 5.2 rests on Lemma 4.5, which is **false as stated**: a set can satisfy its
conditions (1)–(3) without being open. Lemma 5.2 itself is nevertheless true, with a one-line
direct proof. The remaining problems are local. The convergence step in Lemma 5.5 (case
g(s) ∈ w(X)) invokes condition (3) of Lemma 4.5 without the convergent sequence of endpoints that
(3) requires. The case g(s) = cₘ is vacuous but is argued confusedly. Several facts are true
but argued with the wrong reasons ("discrete subspace", Remark 5.3), and there are typos
(A₁ ∪ A₂, "Aₙ", q⁻¹ for q, q_𝔼, the clash of kₙ with k). Section 5 never uses
one-dimensionality, wildness, or the earring-based definition of w(X), and it does not use local
path-connectedness of the domain B in Lemma 5.5. The construction works for any Hausdorff X with
a closed set W whose complement is a null family of open arcs or loops with ends in W.

---

## Construction of 𝒞X and q

**Statement (paraphrased).** X is in standard form, and X ∖ W = ⨆_{n∈N} Oₙ. Each Oₙ comes with
hₙ : [0,1] → Ōₙ restricting to a homeomorphism (0,1) → Oₙ, with aₙ = hₙ(0) and eₙ = hₙ(1)
(aₙ = eₙ for a simple closed curve). Bₙ = hₙ(0,1/2), Cₙ = {hₙ(1/2)}, Dₙ = hₙ(1/2,1). 𝒞X is the
quotient that collapses each Bₙ, Cₙ, Dₙ to a point. F is closed and saturated, and q maps F
homeomorphically onto a closed subset of 𝒞X.

**Verdict: correct (minor unstated justifications).**

- NOTE (closed and saturated). The fibres of q are the singletons of F, together with the sets
  Bₙ and Dₙ. So F is a union of fibres, which means it is saturated. Its complement is
  ⋃ₙ (Bₙ ∪ Dₙ). Each Bₙ, Dₙ is open in Oₙ, and Oₙ is open in X (it is a component of the open set
  X ∖ W in a locally connected space, or part of the standard-form hypothesis). Hence the
  complement is open and F is closed.
- NOTE (homeomorphism onto a closed image). For a quotient map, the restriction to a closed
  saturated subset is a quotient map onto its image (Munkres, Theorem 22.1). Here it is also
  injective, so q|_F is a homeomorphism onto q(F). Moreover q⁻¹(q(F)) = F is closed, so q(F) is
  closed. The paper states all this without the reference. The argument is correct.
- NOTE (existence of hₙ, endpoints). Definition 4.1 says "Oₙ is an arc or simple closed curve"
  where Ōₙ is meant. Ōₙ is an arc or a circle, and Oₙ is a dense connected open subset of it that
  is homeomorphic to ℝ. So Oₙ is the arc minus both endpoints, or the circle minus one point.
  Hence hₙ exists, aₙ and eₙ lie in Ōₙ ∖ Oₙ ⊆ W, and hₙ|[0,1/2] is a homeomorphism onto B̄ₙ. In
  the circle case aₙ = eₙ, but aₙ ≠ cₙ ≠ eₙ, so B̄ₙ and D̄ₙ are still arcs and nothing in
  Section 5 changes.
- NOTE (topology of 𝒞X). q⁻¹{bₙ} = Bₙ is open, so **{bₙ} is open** in 𝒞X, and likewise {dₙ}.
  Every subset of {bₙ, dₙ : n ∈ N} is therefore open in 𝒞X. The set is open and discrete as a
  subspace, and its points are isolated in 𝒞X itself, which is stronger than being a discrete
  subspace. {cₙ} and the points of W are closed but not open. The smallest open neighbourhood of cₙ
  is {bₙ, cₙ, dₙ} = q(Oₙ). Every open neighbourhood of aₙ (respectively eₙ) contains bₙ
  (respectively dₙ).
- NOTE (finitely many arcs). Nothing in the construction needs N to be infinite. If N = ∅, then
  X = W and q = id. The finite case is consistent throughout. Lemma 4.3 is vacuous when N is
  finite, and Lemma 5.5 handles it by the pasting lemma.
- MINOR (empty wild set, outside Part C proper). If W = ∅, the open arcs Oₙ would cover the
  compact space X, which is impossible. So no nonempty X with w(X) = ∅ is in standard form in the
  sense of Definition 4.1 (for example S¹, or a finite graph). Section 6 nonetheless applies
  "replace X by its standard form" to every X with countable w(X). Section 5 offers a clean
  repair, because it never uses that W consists of wild points (see "Hypotheses actually used").
  Take W to be any closed set containing w(X), for example w(X) together with the vertices of a
  graph, such that X ∖ W is a null family of open arcs. Alternatively, treat the graph case
  separately through finite models (McCord).

## Remark 5.1 (countability)

**Statement.** If w(X) is countable, then 𝒞X = W ∪ ⋃_{n∈N} {bₙ, cₙ, dₙ} is countable.

**Verdict: correct (the countability of N is implicit).**

- NOTE. The remark needs N to be countable. Definition 4.1 builds this in by enumerating the arcs
  O₁, O₂, …, but it is also automatic. The Oₙ are pairwise disjoint nonempty open subsets of the
  compact metric (hence separable, second-countable) space X, so there are at most countably many
  of them. The identity 𝒞X = W ⊔ ⋃{bₙ, cₙ, dₙ} holds because q is the identity on F, and the only
  other points are the bₙ and dₙ.

## Lemma 5.2 (q is open)

**Statement.** For V open in X, q(V) is open in 𝒞X.

**Verdict: the statement is correct. The proof cites a false lemma, but it can be replaced by a
one-line proof.**

- MAJOR (Lemma 4.5 is false as stated; this belongs to Section 4 but is applied here). Here is
  a counterexample. Take X = 𝔼, the infinite earring, with W = {b₀}, Oₙ = Cₙ ∖ {b₀}, and
  U = {b₀} ∪ ⋃_{n≥2} Oₙ. U satisfies the three conditions:
  - (1): U ∩ W = W.
  - (2): U ∩ O₁ = ∅ and U ∩ Oₙ = Oₙ for n ≥ 2.
  - (3): every Ō_{nᵢ} with nᵢ ≥ 2 lies in U.

  But U is not open, since every neighbourhood of b₀ meets O₁. In the proof, the claimed
  compactness of X′ fails. "The sets Ōₙ are compact" holds in X but not in X′. Separately, the
  step "yᵢ ∈ V for sufficiently large i" treats an X′-open set V as X-open.

  *Repair of Lemma 4.5:* replace (2) by (2′), "U ∩ Ōₙ is open in Ōₙ". The "if" direction then has
  a direct sequential proof. Suppose x ∈ U and xₖ → x with xₖ ∉ U. Pass to a subsequence such
  that one of the following holds, each of which gives a contradiction:
  - all xₖ ∈ W, which contradicts (1);
  - all xₖ lie in one Ōₙ, which contradicts (2′);
  - the xₖ lie in arcs O_{nₖ} with strictly increasing nₖ. Then by Lemma 4.3, a_{nₖ} → x, and
    (3) contradicts xₖ ∉ U.

  The compactness proof in the paper can also be repaired by the same use of Lemma 4.3.
- NOTE (consequence for Lemma 5.2). Lemma 5.2's proof does in fact establish (2′) for
  q⁻¹(q(V)). If aₙ ∈ V, then V ⊇ hₙ[0,ε), so V meets Bₙ and hence q⁻¹(q(V)) ⊇ hₙ[0,1/2).
  Lemma 5.2 therefore survives the corrected Lemma 4.5. More simply, Lemma 4.5 is not needed at
  all:

  q⁻¹(q(V)) = V ∪ ⋃{Bₙ : V ∩ Bₙ ≠ ∅} ∪ ⋃{Dₙ : V ∩ Dₙ ≠ ∅},

  because the fibres over F are singletons. This is a union of open subsets of X, so it is open.
  **Recommended replacement proof** (it needs only that each Bₙ and Dₙ is open in X).
- NOTE (the case analysis on V ∩ Oₙ). This is correct. If cₙ ∈ V, then V meets both Bₙ and Dₙ
  near cₙ, so the saturation contains all of Oₙ. Otherwise V ∩ Oₙ ⊆ Bₙ ∪ Dₙ, and the saturation
  meets Oₙ in ∅, Bₙ, Dₙ or Bₙ ∪ Dₙ. In the circle case aₙ = eₙ nothing changes.
- NOTE (condition (3) for q⁻¹(q(V))). The worry was that the arcs O_{nᵢ} might lie only partly
  in V. This does not arise. The limit point x lies in W, and q⁻¹(q(V)) ∩ W = V ∩ W, so x ∈ V.
  The true direction of Lemma 4.5 (open ⇒ (3), which is Corollary 4.4) applied to the open set V
  gives Ō_{nᵢ} ⊆ V ⊆ q⁻¹(q(V)) for all but finitely many i. That is exactly (3) for
  q⁻¹(q(V)). The wording "q is bijective on w(X)" should read "the fibres over points of W are
  singletons", but the step is valid.

## Remark 5.3 (closures and boundaries)

**Statement.** In 𝒞X: cl{bₙ} = {aₙ, bₙ, cₙ}, {bₙ} is open, and ∂{bₙ} = {aₙ, cₙ}. Similarly
cl{dₙ} = {cₙ, dₙ, eₙ} and ∂{dₙ} = {cₙ, eₙ}.

**Verdict: correct with minor gaps in the justification.**

- MINOR. "{aₙ, bₙ, cₙ} = q⁻¹(B̄ₙ)" should read q(B̄ₙ). The stated argument ("{aₙ, bₙ} and
  {bₙ, cₙ} are not closed, so …") also omits two facts: that {aₙ, bₙ, cₙ} is closed, and that
  {bₙ} is not closed. A clean argument goes as follows. q⁻¹{aₙ, bₙ, cₙ} = B̄ₙ is closed, so the
  set is closed. Conversely, any closed S ∋ bₙ has a closed preimage containing Bₙ, hence
  containing aₙ and cₙ. Openness of {bₙ} (q⁻¹{bₙ} = Bₙ is open) is used but not justified here.
  With it, ∂{bₙ} = cl ∖ int = {aₙ, cₙ}.
- MINOR (notation). Lemma 5.5 writes "Āₙ is an arc in X with endpoints aₙ and cₙ". This must be
  B̄ₙ = hₙ([0,1/2]). The letter A is moreover already taken by the subspace A ⊆ B.

## Lemma 5.4 (extension with prescribed level sets)

**Statement.** B is perfectly normal, A ⊆ B is closed, and h : A → {0,1} is continuous. Then there
is k : B → [0,1] with k|_A = h and k⁻¹{0,1} = A.

**Verdict: correct (typo; the empty cases rely on the definition as stated).**

- MINOR (typo). "A₁ ∪ A₂" should be A₀ ∪ A₁.
- NOTE (empty cases). If A₀ = ∅ or A₁ = ∅ (including A = ∅), the paper's definition of perfect
  normality still applies, since it quantifies over all pairs of disjoint closed sets. The
  "well-known" fact for metrizable spaces does cover these cases, but the usual formula
  d(x,A₀)/(d(x,A₀) + d(x,A₁)) does not. Here are explicit choices:
  - A = ∅: k ≡ 1/2.
  - A₀ = ∅ ≠ A₁: k = 1 − d(x,A₁)/(2(1 + d(x,A₁))). This takes values in (1/2, 1], and equals 1
    exactly on A₁.
  - A₁ = ∅ ≠ A₀: symmetric to the previous case.

  So Lemma 5.4 gives the right boundary behaviour when ∂U(bₙ) is empty or maps entirely to one
  endpoint.
- NOTE. The lemma is correct but **too weak for its use in Lemma 5.5** (next section). What is
  needed there is the following.

  **Lemma 5.4′.** Let B be perfectly normal, S ⊆ B closed and φ : S → [0,1] continuous. Then there
  is Φ : B → [0,1] extending φ with Φ(B ∖ S) ⊆ (0,1).

  *Proof.* Take a Tietze extension ψ : B → [0,1] and a function ρ : B → [0,1] with ρ⁻¹(0) = S
  (ρ ≡ 1 if S = ∅). Put Φ = (1 − ρ)ψ + ρ/2. On B ∖ S we have ρ > 0, so 0 < ρ/2 ≤ Φ ≤ 1 − ρ/2 < 1.
  On S, Φ = ψ = φ. □

## Lemma 5.5 (lifting)

**Statement.** Let B be locally path-connected and metrizable, A ⊆ B closed, f : A → X and
g : B → 𝒞X with q ∘ f = g|_A. Then there is g̃ : B → X with g̃|_A = f and q ∘ g̃ = g.

**Verdict: the statement is correct. The proof has an error (MAJOR) at the boundary-value step
and gaps in the continuity argument. All are repairable as below.**

- NOTE (B₀ and k). This part is correct. B₀ = g⁻¹(F) is closed. On A ∩ B₀ we have f(z) ∈ q⁻¹(F) = F,
  so f(z) = (q|_F)⁻¹(g(z)). Hence k is well defined, and it is continuous by pasting on the two
  closed sets A and B₀.
- MINOR (openness of U(bₙ)). The conclusion is true but the reason given is not sufficient.
  "{bₙ, dₙ} is a discrete subspace" does not make g⁻¹(bₙ) open. What is needed is that {bₙ} is
  open in 𝒞X, which holds because Bₙ is open in X (see the construction section). Then
  U(bₙ) = g⁻¹(bₙ) ∖ A is open. The decomposition of B ∖ (A ∪ B₀) into the disjoint open sets
  U(bₙ), U(dₙ) is correct, and so is ∂U(bₙ) ⊆ A ∪ B₀. A boundary point outside A ∪ B₀ would lie in
  some other open set U(·), disjoint from U(bₙ).
- **MAJOR (the claim g(∂U(bₙ)) ⊆ {aₙ, cₙ} is false).** Continuity gives only
  g(∂U(bₙ)) ⊆ cl{bₙ} = {aₙ, bₙ, cₙ}. A boundary point p ∈ A with g(p) = bₙ is possible. In that
  case k(p) = f(p) ∈ Bₙ, so βₙ does not map into {aₙ, cₙ}. Lemma 5.4 is then inapplicable, and
  the requirement hₙ⁻¹{aₙ, cₙ} = ∂U(bₙ) is inconsistent with hₙ|_∂ = βₙ.

  *Counterexample to the step:* B = [0,1], A = {0}, g ≡ b₁, f(0) = h₁(1/4). Then U(b₁) = (0,1],
  ∂U(b₁) = {0}, and β₁(0) ∉ {a₁, c₁}. (The lemma's conclusion holds here, with the constant lift.)

  This is not an exotic case. It is precisely the homotopy-lifting square for
  (Iⁿ⁺¹, Iⁿ × {0}) when the initial lift meets some Bₙ. It is also the (Iⁿ⁺¹, ∂Iⁿ⁺¹) square at
  basepoints x ∈ Bₙ ∪ Dₙ, which Corollary 5.6's "all basepoints" requires.

  *Repair:* note that k(∂U(bₙ)) ⊆ q⁻¹{aₙ, bₙ, cₙ} = B̄ₙ. Let θₙ : [0,1] → B̄ₙ, t ↦ hₙ(t/2). Apply
  Lemma 5.4′ on cl U(bₙ) (metrizable, hence perfectly normal) with S = ∂U(bₙ) and
  φ = θₙ⁻¹ ∘ k|_S, and set Hₙ = θₙ ∘ Φ. Then Hₙ = k on ∂U(bₙ) and Hₙ(U(bₙ)) ⊆ Bₙ, so
  q ∘ Hₙ = g on U(bₙ). Treat Dₙ in the same way, with t ↦ hₙ((1+t)/2). The rest of the proof uses
  only these two properties of Hₙ.
- MINOR (notation). The extension on cl U(dₙ) is called kₙ, which clashes with k. In addition,
  "U(bₙ) is perfectly normal" should refer to its closure.
- NOTE (finite N). Correct. B is the union of finitely many closed sets A ∪ B₀, cl U(bₙ) and
  cl U(dₙ). The pieces agree on overlaps, since every overlap lies in A ∪ B₀, where every piece
  equals k. So the pasting lemma applies.
- MINOR (the reduction to strictly increasing nₖ is incomplete as written, but correct). B is
  metrizable, so continuity is sequential. It suffices that every sequence sₖ → s has a
  subsequence along which g̃(sₖ) → g̃(s) (the subsequence principle, which the paper leaves
  unstated). Given any sequence, pass to a subsequence such that one of the following holds:
  - (i) all sₖ ∈ A ∪ B₀. This set is closed and k is continuous, so the case is done.
  - (ii) all sₖ lie in U(bₘ) ∪ U(dₘ) for one fixed m, or after a further subsequence in one of
    them. Then s lies in its closure, and g̃ = Hₘ is continuous there.
  - (iii) sₖ ∈ U(b_{nₖ}) ∪ U(d_{nₖ}) with nₖ strictly increasing.

  This covers sequences that mix A ∪ B₀ with finitely many U's, and unbounded but non-monotone
  nₖ (which have a strictly increasing subsequence). The paper treats only (iii) explicitly and
  invokes pasting implicitly for (ii).
- MINOR (in case (iii), "s ∈ A ∪ B₀ ⇒ g(s) ∈ F" is a non sequitur). If s ∈ A, then g(s) could a
  priori be some bₘ or dₘ. This is excluded because {bₘ} and {dₘ} are open in 𝒞X: g(sₖ) would
  then eventually equal bₘ or dₘ, which contradicts the distinctness of the nₖ. Also, if
  g(s) ∈ W, then s ∈ B₀ automatically, so g̃(s) = x.
- MINOR (the case g(s) = cₘ is vacuous and is argued confusedly). {bₘ, cₘ, dₘ} = q(Oₘ) is an
  open neighbourhood of cₘ. So g(sₖ) ∈ {bₘ, dₘ} eventually, which forces nₖ = m eventually and
  contradicts strict monotonicity. The paper instead concludes "nₖ is eventually constant" and
  then argues convergence. That conclusion is true, but it contradicts the paper's own standing
  assumption, and the openness that justifies it is not mentioned.
- MINOR (the case g(s) = x ∈ W misuses condition (3)). The separation claim is correct.
  {bₙ, cₙ, dₙ} is clopen in 𝒞X ∖ {aₙ, eₙ}: its preimage Oₙ is open, and the complementary
  preimage X ∖ Ōₙ is open and saturated. So any path in 𝒞X from x to {bₙ, dₙ} meets {aₙ, eₙ}.
  The step "V ∩ ∂O_{nₖ} ≠ ∅ for all k, hence by condition (3) Ō_{nₖ} ⊆ V for almost all k"
  does not follow. Condition (3) needs endpoints x_{nₖ} → x, and points that merely lie in a
  possibly large V need not converge to x. The conclusion is in fact false for large V.

  *Repair (path-connectedness not needed):* fix ε > 0. q(B(x, ε/2)) is open by Lemma 5.2, so
  g(sₖ) ∈ q(B(x, ε/2)) eventually. Since q⁻¹{b_{nₖ}} = B_{nₖ}, the ball B(x, ε/2) meets O_{nₖ}.
  By Lemma 4.3, diam O_{nₖ} < ε/2 eventually, so g̃(sₖ) ∈ O_{nₖ} ⊆ B(x, ε) eventually. If one
  prefers the paper's path-connected V ⊆ B(x, ε/2), the separation argument yields endpoints within
  ε/2 of x, and Lemma 4.3 finishes the argument in the same way.
- NOTE (where the hypotheses on B are used). *B locally path-connected is never used.* It can be
  dropped from the statement. *B metrizable* is used in two places. The first is perfect
  normality of the closed subspaces cl U(bₙ), cl U(dₙ) in Lemma 5.4/5.4′; the repair also uses
  Tietze, which needs only normality. The second is the reduction of continuity to sequences
  (first countability of B suffices for that). A closed is used for the openness of U(bₙ) and
  for pasting.

## Corollary 5.6

**Statement.** For X in standard form, q : X → 𝒞X is a Serre fibration and a weak homotopy
equivalence.

**Verdict: correct given Lemma 5.5 (repaired). The derivation is omitted in the paper but is
straightforward, and is spelled out here. Typo: "q_𝔼" should read q.**

- NOTE (Serre fibration). Under I^{n+1} ≅ Iⁿ × I, a homotopy-lifting square for Iⁿ, n ≥ 0, is
  exactly a lifting square for (I^{n+1}, Iⁿ × {0}). Lemma 5.5 solves it. (Lemma 5.5 actually gives
  much more: right lifting against every closed embedding of metrizable spaces.) This relies on
  the MAJOR repair above, because the initial lift on Iⁿ × {0} may meet Bₙ ∪ Dₙ.
- NOTE (weak equivalence, direct argument). The paper does not argue via "Serre fibration with
  weakly contractible fibres". Lemma 5.5 for the pairs (I^{m+1}, ∂I^{m+1}) gives the result
  directly:
  - *π₀ surjective:* q is surjective, being a quotient map. This is not among the listed pairs;
    it would be the pair (I⁰, ∅), but it is trivial.
  - *π₀ injective:* if q(x) and q(y) are joined by a path γ, lift γ relative to ∂I = {0,1} with
    f(0) = x and f(1) = y. (In fact X is path-connected anyway.)
  - *πₙ surjective at any x ∈ X, n ≥ 1:* α : (Iⁿ, ∂Iⁿ) → (𝒞X, q(x)) lifts relative to ∂Iⁿ, with
    f ≡ x there. This is the pair (I^{m+1}, ∂I^{m+1}) with m = n − 1.
  - *πₙ injective, n ≥ 1:* let β : (Iⁿ, ∂Iⁿ) → (X, x), and let G : Iⁿ × I → 𝒞X be a null-homotopy
    of q ∘ β rel ∂Iⁿ. Lift G relative to ∂I^{n+1}, with f = β on the bottom face and f ≡ x on the
    other faces; q ∘ f = G holds there. The lift is a null-homotopy of β rel ∂Iⁿ.

  All of this is at arbitrary basepoints, including x ∈ Bₙ ∪ Dₙ, which again needs the repair.
- NOTE (fibres). The fibres of q are points (over F) and the open arcs Bₙ and Dₙ, all
  contractible. So the alternative route also works: a surjective Serre fibration with
  contractible fibres, plus the long exact sequence at every basepoint, gives a weak equivalence.
  The paper does not need it.

---

## Hypotheses actually used

Section 5, with the repairs above, uses only the following data and properties.

1. X is a **Hausdorff** space and W ⊆ X is **closed**. Hausdorffness is used for the arcs B̄ₙ
   and D̄ₙ and for the two-point sets {aₙ, cₙ}.
2. X ∖ W = ⨆_{n∈N} Oₙ, where the Oₙ are **pairwise disjoint and open in X**. N is countable,
   but this is used only for Remark 5.1, and it is automatic for separable X.
3. For each n, a map hₙ : [0,1] → X restricts to a **homeomorphism (0,1) → Oₙ**, with
   **hₙ(0), hₙ(1) ∈ W**. These endpoints may coincide.
4. **Null family**: diam Oₙ → 0 for a compatible metric. A metric-free version suffices: for
   x ∈ W and every neighbourhood U of x there is a neighbourhood V of x such that all but finitely
   many of the Oₙ meeting V lie in U. Used only in Lemma 5.5, case g(s) ∈ W, and nowhere when N is
   finite.

In the paper, (4) is derived as Lemma 4.3 from **compactness, metrizability and local
path-connectedness of X**. This is the only place in Section 5 where those properties are needed,
once the path-connected V in Lemma 5.5 is replaced as above. Lemma 4.3's printed proof also has a
gap: "z ∉ B(x, δ/2) ∪ B(y, δ/2)" does not follow, because U_x and U_y are only known to lie in
the δ-balls. It is repaired as follows. Choose zᵢ on the subarc from xᵢ to yᵢ with
d(zᵢ, x) = d(zᵢ, y), so that d(z, x) = d(z, y) ≥ δ. Take U_x, U_y, U_z inside the δ/2-balls. Then
U_z is disjoint from U_x ∪ U_y, which contains both endpoints of the arc O_{nᵢ} once zᵢ ∈ U_z,
and this is a contradiction. Lemma 4.3 uses the standard-form structure but not
one-dimensionality.

**Not used anywhere in Section 5:**
- one-dimensionality of X;
- the definition of w(X) through fully essential earring maps, or any property of wild points.
  W can be any closed set with (2)–(4). In particular one may enlarge W by finitely many vertices
  to handle graphs, which removes the w(X) = ∅ problem;
- connectedness of X;
- Lemma 4.5, which is false as stated and can be replaced by the direct proof of Lemma 5.2;
- local path-connectedness of the domain B in Lemma 5.5.

**Used in Lemma 5.5 and Corollary 5.6:**
- B metrizable: perfect normality and Tietze on closed subspaces, and sequential continuity;
- A ⊆ B closed;
- for Corollary 5.6, only the cubes Iⁿ⁺¹ with A = Iⁿ × {0} or ∂Iⁿ⁺¹, together with the
  surjectivity of q.

For a Lean formalisation, the natural abstraction is therefore a structure "Hausdorff X, closed W,
a null family of open arcs or loops parametrised by hₙ with ends in W, covering X ∖ W", with no
reference to dimension or wildness. The Peano and standard-form input enters only through
Lemma 4.3, or the nullness assumption can be taken as a field of the structure.
