# Referee check, Part A: Sections 2 and 3 of Brazas–Pavešić, arXiv:2610.35875

Scope: Definitions 2.1, 2.2, 2.4, 2.6 and 3.1; Lemma 2.5; the proof of Lemma 2.8 from Remark 2.7;
Lemmas 3.3 and 3.4. The formulas were checked against the PDF (page 5 rendered at 300 dpi), because
the text extraction drops the overlines.

Sources: I could not get the cited papers. Cannon–Conner 2006 [8] and Eda 2016 [13] are not on
arXiv, and Eda's home page refused the connection. Everything below about what [8, Theorem 3.9],
[8, Corollary 3.3] and [13, Lemma 3.6] actually say comes **from memory or is inferred**, and is
marked as such.

## Verdict

Part A is sound in substance. Every result that later parts of the paper use is true, and each can
be proved with tools already in Sections 2–3. There is one real gap and some local defects.

- **The gap (Lemma 3.3).** The lemma is stated for all of H₁(A), where A is an arbitrary subset.
  The proof only handles a class represented by a single loop at a basepoint x₀. That covers
  path-connected A (by the Hurewicz theorem) but not A with several path components. Two loops in
  different path components of A could a priori become homologous in X, and excluding this is
  precisely the content of Lemma 3.4. The paper only uses Lemma 3.3 for A a simple closed curve
  (Lemma 6.3), so nothing downstream breaks. The general statement can be repaired: join the loops
  by a "tree" of arcs and apply retractions; the argument is given below.
- **Lemma 3.4.** The proof reaches a true conclusion, but:
  - the displayed loop L is ill-formed as typeset;
  - the claim that α₁γβ₁γ̄ is reduced is justified by an insufficient reason;
  - the case where β₁ is constant is not handled;
  - the closure of the pairing on {1,…,m} uses, without saying so, that 0-form pieces are
    non-constant.

  There is a much shorter proof from the path-connected case of Lemma 3.3 and a retraction. That
  proof also shows the hypothesis "reduced" is unnecessary, which matters because Lemma 6.4 applies
  Lemma 3.4 to loops that need not be reduced.
- **The rest.** Lemma 2.5 and the derivation of Lemma 2.8 from Remark 2.7 are correct. Definition 2.6
  needs "a < b". The cited inputs are applied within their hypotheses as the paper states them; I
  could not verify those statements against the originals.

No finding is FATAL. There is one MAJOR finding (A-3.3-1); the rest are MINOR or NOTE.

---

## Definition 2.1 (fully essential map)

**Statement.** A map f : 𝔼 → X from the infinite earring is fully essential if each loop f∘ℓ_j is
essential, that is, not null-homotopic.

**Verdict.** Well posed.

- **NOTE.** ℓ_j is defined as a path [0,1] → C_j "traversing the j-th circle once". The paper never
  says it is based at b₀, but that is evidently intended. Either way essentiality is unaffected: a
  loop is freely null-homotopic iff it is based-null-homotopic, so treating f∘ℓ_j as a map S¹ → X
  is harmless.

## Definition 2.2 (wild set) and its equivalence with the introduction

**Statement.** w(X) is the set of x at which there is a fully essential based map (𝔼, b₀) → (X, x).

**Verdict.** Well posed for every space, and used consistently.

- **NOTE.** I re-derived the equivalence with the introduction's definition ("every neighbourhood of
  x contains the image of an essential loop based at x").
  - A fully essential map gives such loops in every space: by continuity at b₀ we have f(C_k) ⊆ U
    for large k.
  - The converse needs a countable nested neighbourhood base. Choose an essential loop αₙ in Uₙ and
    set f∘ℓₙ = αₙ; the map is continuous at b₀ because the images shrink into Uₙ.

  So the paper's remark is correct.
- **NOTE.** The paper says "we do not consider non-first-countable spaces". But Lemma 6.4 and the
  "only if" half of Theorem 1.1 take Y arbitrary. This is harmless, because those arguments only use
  Definition 2.2, and Lemma 2.5 holds for arbitrary Y.

## Definition 2.4 (π₁-injective; weak homotopy equivalence)

**Verdict.** Standard and well posed. "π₁-injective" quantifies over every basepoint. That is what
Lemma 2.5 needs (injectivity at x ∈ w(X)), and it is what the proof of Lemma 2.8 gives, since x₀ ∈ A
is arbitrary.

## Lemma 2.5

**Statement.** If f : X → Y is π₁-injective, then f(w(X)) ⊆ w(Y).

**Verdict.** Correct.

**Re-derivation.**
1. Let g be fully essential at x. Then f∘g is continuous and based at f(x).
2. If (f∘g)∘ℓ_j were null-homotopic in Y, injectivity of f_# : π₁(X, x) → π₁(Y, f(x)) would make
   g∘ℓ_j null-homotopic in X, a contradiction.

No further hypotheses are used: no metrizability and no dimension assumption.

## Definition 2.6 (reduced path)

**Statement.** β is reduced if it is constant, or if no subinterval [a,b] has β(a) = β(b) with β|[a,b]
null-homotopic rel {a,b}.

**Verdict.** Well posed after one fix.

- **MINOR (A-2.6-1).** The interval must be non-degenerate (a < b). With a = b, β|[a,a] is constant
  and hence null-homotopic, so no non-constant path would be reduced. Repair: write "[a,b] with
  a < b".
- **NOTE.** With a < b, a non-constant reduced path is constant on no non-degenerate interval. This
  fact is needed silently later:
  - pieces of a subdivided 0-form stay non-constant (Lemma 3.4);
  - uniqueness "up to an increasing homeomorphism" in Remark 2.7 makes sense.

  Subpaths of reduced paths are reduced, and injective paths are reduced. Both are used in Lemma 3.4
  and both are immediate.

## Remark 2.7 (Cannon–Conner reduction) — cited input

**As quoted.** Let X be a one-dimensional metrizable space.
- Every loop α is path-homotopic to a reduced loop by a homotopy H with Im(H) ⊆ Im(α).
- Reduced loops that are path-homotopic differ by an increasing reparametrisation.

**Verdict.** Plausible and consistent with my memory of [8]; not verified against the source.

- **NOTE (memory, unverified).** I recall the Cannon–Conner reduced-path theorem as stated for paths
  rel endpoints, in one-dimensional (separable) metric spaces, with the homotopy inside the image. I
  cannot confirm the theorem number or whether "separable" appears.
  - If "separable" appears, it costs nothing. Im(α) is a Peano continuum (Hahn–Mazurkiewicz), so it
    is separable. By the subset theorem for covering dimension in metrizable spaces, dim Im(α) ≤ 1.
    Since H lives in Im(α), one may apply the theorem to Im(α) and transfer reducedness back to X
    using Lemma 2.8.
  - The paper should say this, or quote [8] with its exact hypotheses.
- **NOTE.** [8, Corollary 3.3] (Lemma 2.8) is numbered before [8, Theorem 3.9]. If Corollary 3.3
  really is the π₁-injectivity statement in [8], the paper's derivation of it from Theorem 3.9 is
  presumably a different route from Cannon–Conner's. Worth confirming the numbering against the
  source.

## Lemma 2.8, proof from Remark 2.7

**Statement.** If X is one-dimensional metrizable and A ⊆ X, then the inclusion A → X is
π₁-injective.

**Verdict.** Correct.

**Re-derivation.**
1. Let α be a loop in A at x₀ that is null-homotopic in X.
2. The constant loop c is reduced and path-homotopic to α.
3. Remark 2.7 gives a reduced β with α ≃ β via H, where Im(H) ⊆ Im(α) ⊆ A.
4. By uniqueness, β = c∘h = c.
5. So H is a null-homotopy rel endpoints inside A.

Both halves of Remark 2.7 are needed, and the proof uses both. A need not be closed, metrizable in any
special way, or path-connected, because everything happens in Im(α). The basepoint x₀ is arbitrary,
so injectivity holds at every basepoint, as Definition 2.4 requires.

- **MINOR.** Typo: "it's" should be "its".

## Definition 3.1 (0-form)

**Statement.** Non-constant reduced paths β₁, …, β₂ₙ whose concatenation is a loop, paired so that
β_{i_k} = β̄_{j_k}.

**Verdict.** Well posed, with small imprecisions.

- **MINOR (A-3.1-1).** The paper uses three notions of equality, and they should be reconciled:
  - Definition 3.1 asks for exact equality β_{i_k} = β̄_{j_k};
  - Lemma 3.2 asks that the concatenation be "a reduced representative", which is unique only up to
    reparametrisation;
  - Lemma 3.4 uses an undefined "≡".

  With exact equality, subdivision (Lemma 3.4) works only if one splits partners at corresponding
  parameters and rescales linearly. This is fine, but it should be said. Repair: define ≡ as
  "equal up to an increasing reparametrisation", and use it both in the pairing condition and for
  the concatenation of 2n paths (whose parametrisation the paper never fixes).
- **NOTE.** n ≥ 1 is implicit. Lemma 3.2 only concerns essential loops, so the empty 0-form is never
  needed.
- **NOTE.** The direction "0-form ⇒ null-homologous" holds in every space. At chain level,
  β₁⋯β₂ₙ ∼ Σ βᵢ, and β + β̄ is a boundary.

## Lemma 3.2 (zero-form lemma, Eda 2016 Lemma 3.6) — cited input

**As quoted.** X one-dimensional metrizable, α an essential loop. Then [α]_h = 0 iff some 0-form
concatenates to a reduced representative of α.

**Verdict.** Not verified against the source.

- **NOTE (memory/inference, unverified).** Eda's paper concerns one-dimensional Peano continua, and I
  cannot confirm whether Lemma 3.6 there is stated for Peano continua or for general one-dimensional
  metrizable spaces. If it is only for Peano continua, the extension needs care, because the naive
  extension is circular.
  - Transferring "[α]_h = 0 in H₁(X)" to H₁(Im α) would need Lemma 3.3 itself.
  - A non-circular extension: a bounding 2-chain lies in the union K of Im(α) and finitely many
    singular-simplex images. This is a finite union of Peano continua. Its component containing
    Im(α) is a connected compactum with Whyburn's property S, hence a Peano continuum. It has
    dimension ≤ 1 by the subset theorem.
  - Apply Eda in K. Reducedness in K and in X agree by Lemma 2.8, and the reduced representative
    in X lies in Im(α) ⊆ K by Remark 2.7.

  The paper should either quote the hypotheses of [13] exactly or add this sentence.

## Lemma 3.3

**Statement.** For X one-dimensional metrizable and A ⊆ X, H₁(A) → H₁(X) is injective.

**Verdict.** Gap. The proof is correct for path-connected A, which is the only case used in the
paper (Lemma 6.3, A = Cₙ). It is incomplete for general A.

**Re-derivation of what is proved.**
1. Let α be a loop in A at x₀ with [α]_h = 0 in H₁(X). If α is inessential in A, then [α]_h = 0 in
   H₁(A) trivially. Otherwise α is essential in X by Lemma 2.8, so Lemma 3.2 applies.
2. Lemma 3.2 gives a 0-form β₁…β₂ₙ concatenating to a reduced representative of α.
3. Remark 2.7 gives a reduced β′ ≃ α inside Im(α). By uniqueness, β₁⋯β₂ₙ is a reparametrisation of
   β′, so every βᵢ lies in Im(α) ⊆ A, and α ≃ β₁⋯β₂ₙ in A.
4. The 0-form is null-homologous in A at chain level.

**Findings.**

- **MAJOR (A-3.3-1): the stated generality is not proved.**
  - **Path-connected A: no gap.** Hurewicz (π₁(A,x₀)^ab ≅ H₁(A)) makes every class equal to [α]_h
    for one loop at x₀. Even this should be cited.
  - **A with several path components: gap.** A class is Σ_c [α_c]_h with α_c in distinct path
    components A_c ⊆ A. Several A_c may lie in one path component of X. Then Σ_c [α_c]_h = 0 in
    H₁(X) does not reduce to a single-loop statement.
    - With two components this is exactly Lemma 3.4 (with β reversed).
    - With m ≥ 3 components nothing in the paper covers it.
  - **Is this a gap for one-dimensional spaces?** Yes. The statement is still true, as the repair
    shows.
  - **Repair.**
    1. Split by path components P of X, using H₁(X) = ⊕_P H₁(P).
    2. Inside one P, let K_c = Im(α_c). These are disjoint path-connected compacta.
    3. Build a tree of arcs. Start with Y = K₁. While some K_d is unattached, use the first-exit and
       first-entry argument (spelled out in Lemma 3.4 below) to find an arc from Y to the union of
       the unattached K_d's. Choose it to meet Y ∪ (that union) only at its two ends. Add the arc
       and the K_d it reaches.
    4. The final Y is path-connected and compact, so the path-connected case gives
       H₁(Y) ↪ H₁(X).
    5. For each c, the closure of Y ∖ K_c is a finite union of closed "branches", each meeting K_c
       in a single point. Collapsing each branch to its attaching point is a retraction
       r_c : Y → K_c, continuous by the pasting lemma.
    6. Now Σ_d [α_d]_h = 0 in H₁(Y) gives [α_c]_h = (r_c)_* Σ_d [α_d]_h = 0 in H₁(K_c), hence in
       H₁(A_c) ⊆ H₁(A).
  - **Alternative.** Restrict the statement to path-connected A, which suffices for the paper.

- **MINOR (A-3.3-2): typo in the closing formula.** As printed (PDF), the sum is
  Σ_k [β_{i_k} β̄_{j_k}]_h. Since β_{i_k} = β̄_{j_k}, this is β_{i_k}β_{i_k}, which is not even a loop
  in general. It should be [β_{i_k} β_{j_k}]_h, a loop of the form ββ̄. Better: work with chains,
  β₁⋯β₂ₙ ∼ Σ βᵢ and β_{i_k} + β_{j_k} ∼ 0. The paper defines [·]_h only for loops, so the chain
  formulation is cleaner.

- **MINOR (A-3.3-3): unstated steps.**
  - Lemma 3.2 requires α essential **in X**. This follows from essential in A via Lemma 2.8, which
    the proof does not say.
  - "There exists a homotopy H from α to β₁⋯β₂ₙ with Im(H) ⊆ Im(α)" combines the existence clause
    with the uniqueness clause of Remark 2.7. The reparametrisation homotopy also stays inside
    Im(α).
  - "β₁⋯β₂ₙ is a reduced representative of α" should say "of i∘α", as in the line before.

## Lemma 3.4

**Statement.** In a one-dimensional path-connected metrizable X, let α and β be reduced loops with
disjoint images. If one of them is not null-homologous, they are not homologous.

**Verdict.** Correct with minor gaps. The conclusion is true, and the proof can be completed. A much
shorter proof exists and also removes an unnecessary hypothesis.

**Line-by-line check.**

1. **Existence of γ.** This is fine, but takes more work than the paper indicates.
   - Take any path p from a point of Im α to a point of Im β.
   - Let t₁ = min p⁻¹(Im β) and s₀ = max(p⁻¹(Im α) ∩ [0,t₁]). These exist because the images are
     compact, hence closed. Then s₀ < t₁ by disjointness, and p((s₀,t₁)) avoids Im α ∪ Im β.
   - Pick an arc from p(s₀) to p(t₁) inside the Peano continuum p([s₀,t₁]). This uses arcwise
     connectedness of Peano continua, a real but standard input.
   - This arc meets Im α ∪ Im β only at {x₀, x₁}.

   η and ζ exist for the same reason.
   - **MINOR.** If x₀ = α(0) (or x₁ = β(0)), η (or ζ) is constant rather than injective. This is
     harmless, but the statement should allow it.

2. **MINOR (A-3.4-1): the loop L is mis-typeset.**
   - **What the PDF shows.** L = η α η̄ γ ζ \overline{βζ} γ̄ = η α η̄ γ ζ ζ̄ β̄ γ̄. Here ζζ̄ ends at x₁
     but β̄ starts at β(0), so the concatenation is undefined unless x₁ = β(0).
   - **The version in the task brief.** η α η̄ γ ζ β ζ̄ γ̄ is well defined, but has
     [L]_h = [α]_h + [β]_h, so "homologous ⇒ L null-homologous" would be false.
   - **The intended loop.** L = η α η̄ · γ · ζ β̄ ζ̄ · γ̄, with [L]_h = [α]_h − [β]_h.
   - **Consequence.** β₁ must be the reduced representative of ζβ̄ζ̄, not of ζβζ̄ or ζ\overline{βζ}.

3. **MINOR (A-3.4-2): "the reduced representative of L has the form L′ = α₁γβ₁γ̄" is under-justified.**
   - **The reason given is not sufficient.** The paper says "since α, β, γ, η, ζ are all reduced". A
     concatenation of reduced paths is not reduced in general; the need for α₁ already shows this.
   - **The claim is true when α₁ and β₁ are non-constant.** Let Y = Im α₁ ∪ Im γ ∪ Im β₁, and let
     [a,b] (a < b) be a subinterval with L′(a) = L′(b) and L′|[a,b] null-homotopic. By Lemma 2.8 it
     is null-homotopic in Y.
     - If L′(a) is interior to the arc, then b is at the matching point of γ̄, and the subloop is a
       conjugate of β₁. It is essential because a non-constant reduced loop is essential.
     - If L′(a) ∈ Im α₁, then L′(b) ∈ Im α₁ ∩ (…) ⊆ Im α₁ ∪ {x₀}. In this case apply the retraction
       r : Y → Im α₁ that sends Im γ ∪ Im β₁ to x₀. It turns the subloop into a subloop of α₁
       (possibly followed by constants), which contradicts reducedness of α₁.
     - The case L′(a) ∈ Im β₁ is symmetric.
   - **Repair.** Insert this argument.

4. **MINOR (A-3.4-3): degenerate case.**
   - α₁ is non-constant, because α is not null-homologous, so it is essential.
   - β₁ may be constant, if β is null-homotopic. Then L′ = α₁γγ̄ is not reduced; the reduced
     representative of L is α₁, and the form claimed for it is wrong.
   - In that case [α]_h = [β]_h = 0 gives the contradiction at once, but the proof should say so.

5. **The subdivision step is correct.**
   - Lemma 3.2 applies to L because L′ is non-constant and reduced, hence L is essential.
   - Splitting δ₁⋯δ₂ₙ at the junction between α₁ and γ divides at most one δ_p at an interior
     parameter. Its partner δ_q = δ̄_p (q ≠ p) is split at the corresponding parameter, and the two
     new pairs are formed.
   - The pieces are reduced (subpaths) and non-constant, by NOTE under Definition 2.6.
   - Other breakpoints are unaffected.

6. **MINOR (A-3.4-4): the pairing must close on {1,…,m}, and the proof leaves this implicit.**
   - The paper concludes "both Im δ_{i_k} and Im δ_{j_k} ⊆ Im α₁, therefore δ₁…δ_m is a 0-form".
   - The point actually needed is that j_k ≤ m whenever i_k ≤ m. Suppose j_k > m. Then Im δ_{j_k} is
     contained in Im(γβ₁γ̄) ∩ Im α₁ = {x₀}, so δ_{j_k} is constant. This contradicts the
     non-constancy built into Definition 3.1.
   - The step is fine, but this is the actual reason and should be written.
   - The final steps are also fine: δ₁⋯δ_m ≡ α₁ is reduced, so the "if" direction of Lemma 3.2,
     which holds in any space, gives [α₁]_h = 0. Then α₁ ≃ ηαη̄ is freely homotopic to α. The
     paper's "α ≃ α₁" relates loops with different basepoints and should say "freely homotopic" or
     "homologous".

7. **NOTE (A-3.4-5): a shorter proof, which also removes the "reduced" hypothesis.**
   1. Let Y = Im α ∪ Im γ ∪ Im β. It is path-connected and compact.
   2. Define r : Y → Im α by r = id on Im α and r ≡ x₀ on Im γ ∪ Im β. This is continuous by the
      pasting lemma: Im α ∩ (Im γ ∪ Im β) = {x₀}, and both sets are closed.
   3. If [α]_h = [β]_h in H₁(X), then [α]_h − [β]_h ∈ H₁(Y) vanishes in H₁(X). By the path-connected
      case of Lemma 3.3 it vanishes in H₁(Y).
   4. Applying r_* gives [α]_h = 0 in H₁(Im α), hence in H₁(X).

   This uses neither reducedness of α and β, nor L, nor a second appeal to Lemma 3.2. It shows that
   Lemma 3.4 is just the two-component case of Lemma 3.3.

8. **NOTE (cross-reference to Part D).** Lemma 6.4 applies Lemma 3.4 to g₀∘ℓₙ and g₃∘ℓₙ. The second
   is an arbitrary loop and need not be reduced, so as stated Lemma 3.4 does not apply.
   - This is harmless. The repair in item 7 removes the hypothesis. Alternatively, pass to reduced
     representatives: their images are contained in the originals by Remark 2.7, so they are still
     disjoint, and they are homologous to the originals.
   - Part D's referee should record this.
   - Lemma 6.4 also writes [g₀∘ℓₙ] ≠ 0 where [·]_h is meant.

---

## Summary of findings

| ID | Result | Label | One line |
|---|---|---|---|
| A-3.3-1 | Lemma 3.3 | MAJOR | Proof covers only classes represented by one loop, i.e. path-connected A; multi-component A unproved (true; repair via arc-tree + retractions, or restrict statement — the paper only uses path-connected A) |
| A-3.4-1 | Lemma 3.4 | MINOR | Displayed L is ill-formed (ζ\overline{βζ}); intended ηαη̄·γ·ζβ̄ζ̄·γ̄ (and β₁ = reduced rep. of ζβ̄ζ̄) |
| A-3.4-2 | Lemma 3.4 | MINOR | Reducedness of α₁γβ₁γ̄ asserted "since the paths are reduced" — insufficient; true via disjointness + retraction + Lemma 2.8 |
| A-3.4-3 | Lemma 3.4 | MINOR | Case β₁ constant (β null-homotopic) not handled (trivial, but L′ form is then wrong) |
| A-3.4-4 | Lemma 3.4 | MINOR | Closure of pairing on {1..m} needs non-constancy of 0-form pieces; not stated |
| A-3.4-1′ | Lemma 3.4 | MINOR | η, ζ may be constant, not injective |
| A-3.4-5 | Lemma 3.4 | NOTE | Two-line proof via Lemma 3.3 (path-connected case) + retraction; "reduced" hypothesis unnecessary |
| A-3.4-6 | Lemma 3.4 / 6.4 | NOTE | Lemma 6.4 applies 3.4 to non-reduced g₃∘ℓₙ; harmless given A-3.4-5 or by passing to reduced reps |
| A-3.3-2 | Lemma 3.3 | MINOR | Typo Σ[β_{i_k}β̄_{j_k}]_h should be Σ[β_{i_k}β_{j_k}]_h (or chain-level) |
| A-3.3-3 | Lemma 3.3 | MINOR | Unstated: α essential in X via Lemma 2.8; uniqueness used to land H on β₁⋯β₂ₙ; "of i∘α"; Hurewicz for path-connected A |
| A-2.6-1 | Def 2.6 | MINOR | Require a < b, else no non-constant path is reduced |
| A-3.1-1 | Def 3.1 | MINOR | Exact "=" vs "up to reparametrisation" vs undefined "≡"; fix one convention |
| A-2.7 | Remark 2.7 | NOTE | Hypotheses of [8, Thm 3.9] not verified (memory: separable metric; harmless, since Im α is a Peano continuum); Cor 3.3 numbered before Thm 3.9 |
| A-3.2 | Lemma 3.2 | NOTE | Hypotheses of [13, Lemma 3.6] not verified; if only for Peano continua, extension to metrizable X needs a short non-circular compactness argument |
| A-2.1 | Def 2.1 | NOTE | Basepoint of ℓ_j unstated; irrelevant for essentiality |
| A-2.2 | Def 2.2 | NOTE | Equivalence with intro definition verified (needs first countability in one direction); Lemma 2.5/6.4 use it for arbitrary Y, which is fine |
| A-2.5 | Lemma 2.5 | — | Correct |
| A-2.8 | Lemma 2.8 proof | — | Correct (uses both halves of Remark 2.7); typo "it's" |
