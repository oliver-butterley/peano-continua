# Referee check, Part B: Section 4 of Brazas–Pavešić, "Countable models of one-dimensional Peano continua" (arXiv:2610.35875)

Scope: Definition 4.1 and the paragraph after it, Lemma 4.3, Corollary 4.4, Lemma 4.5.
Notation: W = w(X) is the wild set; ∂O = closure(O) \ O for open O (the frontier).

## Verdict

All four results are true, and Corollary 4.4 is correct as proved, but two proofs have real gaps. In Lemma 4.3, the step "z ∉ B̄(x,δ/2) ∪ B̄(y,δ/2)" does not follow, because U_x is only known to lie inside B(x,δ), not to contain B̄(x,δ/2). The final contradiction is also invalid as written, because a_{n_i} ∈ U_x can lie outside B̄(x,δ/2). A three-neighbourhood pigeonhole argument repairs it. In Lemma 4.5, the compactness proof concludes "y_i ∈ V for large i" from y_i → x in the metric topology of X. But V is only open in X′, so that step assumes what is being proved. Condition (3) is never used there, and without it the claim is false. The repair uses Lemma 4.3 together with condition (3). Definition 4.1 is well posed once w(X) is known to be closed (Lemma 2.3). It forces w(X) ≠ ∅ for every non-empty X, so a space with empty wild set, such as a finite graph or a point, is never in standard form. As a result, Theorem 4.2 (cited from Meilstrup) is false as stated for those spaces, and the proof of Theorem 1.1 misses the case w(X) = ∅. The paragraph after Definition 4.1 contains a false sentence: "if w(X) is infinite then X∖w(X) has infinitely many components" fails for the Sierpiński carpet and the Menger curve. It becomes true if "infinite" is replaced by "countably infinite", and nothing in the paper seems to use it. None of the results in Part B use one-dimensionality or the definition of w(X) through the earring. Lemmas 4.3–4.5 need only: a compact metric space that is locally connected, and a family of pairwise disjoint, open, connected sets, each with at most two frontier points (Lemma 4.5 also needs these sets to cover X \ W).

---

## Definition 4.1 (standard form) and the paragraph after it

**Statement (paraphrased).** A one-dimensional Peano continuum X is in standard form if X \ w(X) is a (possibly finite) disjoint union of open arcs O₁, O₂, … such that each closure Ō_n is an arc or a simple closed curve with Ō_n \ O_n ⊆ w(X). Claim after the definition: if X is in standard form, w(X) ≠ ∅ and X \ w(X) has finitely many components, then w(X) is a finite disjoint union of Peano continua P_j, each with w(P_j) = P_j. "Hence" if w(X) is infinite then X \ w(X) has infinitely many components.

**Verdict.** The definition is well posed, given Lemma 2.3; this should be said. The first claim is correct, with the proof left to the reader. The "Hence" sentence is **false** as stated.

**Findings.**

- **MINOR (well-posedness, the meaning of "disjoint union").** The text never says that the O_n are the connected components of X \ W, or that they are open in X. Section 5 assumes both ("Enumerate the connected components of X\w(X) as O₁, O₂, …"), and so do Lemmas 4.3 and 4.5 ("since the sets O_n are open"). Both facts follow from the definition as stated, but only after an argument:
  1. Ō_n \ O_n ⊆ W gives Ō_n ∩ (X \ W) = O_n, so each O_n is closed in X \ W.
  2. W is closed by Lemma 2.3 (X is locally path-connected and first countable), so X \ W is open in X.
  3. Suppose O_n were not open. Take p ∈ O_n that is a limit of points q_k ∈ O_{m_k} with m_k ≠ n. Choose a path-connected open set U ∋ p with U ⊆ X \ W, and a path γ in U from p to some q_k. Then [0,1] = ⊔_m γ⁻¹(O_m) is a partition of [0,1] into countably many (at least two) disjoint non-empty closed sets. This contradicts Sierpiński's theorem; for finitely many pieces, plain connectedness suffices. So each O_n is open, and being connected and clopen in X \ W, it is a component of X \ W.

  *Repair:* state in the definition that the O_n are the components of X \ W (equivalently, that they are open in X). For a formalisation, take "O_n open" as a hypothesis rather than going through Sierpiński's theorem.
- **NOTE (frontier).** If Ō_n is an arc, then O_n is a dense connected subset of the arc that is homeomorphic to ℝ. It must therefore be the interior of the arc, so ∂O_n = Ō_n \ O_n is exactly the two (distinct) endpoints. If Ō_n is a simple closed curve, O_n is the circle minus one point, so ∂O_n is a single point (a_n = e_n). The frontier is never empty, because O_n is not compact. So |∂O_n| ∈ {1, 2} and ∂O_n ⊆ W. This is the only feature of "arc" that Section 4 uses.
- **NOTE (degenerate cases).** If X \ W = ∅ the definition is satisfied with the empty family ("possibly finite" should read "possibly finite or empty"). Then X = W, and Lemma 4.5 holds trivially. The case "X \ W finite" is allowed and causes no problems (see Lemma 4.5 below).
- **MAJOR (outside Part B, but forced by this definition: spaces with empty wild set).** Let X be non-empty and in standard form. If W = ∅, then each Ō_n \ O_n = ∅, so O_n is compact, which is impossible for an open arc; hence X = ∅. So **a non-empty X in standard form has w(X) ≠ ∅**. A homotopy equivalence f is π₁-injective (π₁ is the fundamental group) in both directions, so by Lemma 2.5 it preserves whether the wild set is empty. Therefore a point, an arc, a circle, or any finite graph (more generally, any one-dimensional Peano continuum with w(X) = ∅) is **not** homotopy equivalent to any space in standard form, and Theorem 4.2 as quoted is false for these spaces. The proof of Theorem 1.1 ("By Meilstrup's result (Theorem 4.2) we may find … X′ in standard form") therefore misses the case w(X) = ∅.
  *Repair:* add "with w(X) ≠ ∅" to Theorem 4.2, and handle w(X) = ∅ separately: such an X is homotopy equivalent to a finite graph, which has a finite model by McCord. Alternatively, change Definition 4.1 so that a finite graph counts as being in standard form.
- **MINOR (first claim: the proof is omitted, but the claim is correct).** Here is a proof that uses only: W closed, X locally path-connected, finitely many O_n, ∂O_n ⊆ W.
  - Let r > 0 be smaller than ½·min_n diam Ō_n; there are finitely many n, and each diameter is positive.
  - Let γ be a path inside a path-connected open set U of diameter < r, with both ends in W. Each excursion of γ into some O_n is a component interval (c,d) of γ⁻¹(O_n), with γ(c), γ(d) ∈ ∂O_n. Its image is a connected subset of Ō_n of diameter < r, so it is not all of Ō_n. Hence γ(c) = γ(d), and the image lies in a sub-arc of Ō_n.
  - Replace γ on every excursion interval by the constant at γ(c). The result is continuous, because the endpoints of the excursion intervals converge to the limit times. It is also homotopic to γ rel endpoints, by contracting each excursion inside its sub-arc.
  - Consequence 1: every x ∈ W has arbitrarily small neighbourhoods U ∩ W that are path-connected in W. So W is a compact, locally path-connected metric space, and it has finitely many components P_j, each of them a Peano continuum.
  - Consequence 2: every small essential loop at x ∈ W is homotopic in X to a loop in W, which stays essential in W and hence in P_j. So x ∈ w(P_j), using the paper's assertion that Definition 2.2 agrees with the "small essential loops" definition for first-countable spaces.

  One-dimensionality is not used.
- **MAJOR (the "Hence" sentence is false; no downstream use found).** Counterexample: the Sierpiński carpet S, or the Menger curve, which the paper itself lists as having uncountable wild sets. In both, every point is wild, so w(S) = S. Then S is in standard form with zero arcs, w(S) is infinite, and X \ w(X) has 0 components. A version with one arc: attach an arc to S between two of its points. S is a retract of the result, so the wild set is still S, and the complement is a single open arc. The step from the first claim to the "Hence" silently assumes that a Peano continuum P with w(P) = P must be a point.
  *Repair:* replace "infinite" by "countably infinite", which is the only case the paper needs. A non-degenerate Peano continuum is uncountable, so if W is countable and the components are finitely many, each P_j is a point and W is finite. Section 5 (Lemma 5.5) treats the case of finitely many arcs separately anyway, so nothing appears to depend on this sentence.

---

## Lemma 4.3 (null family)

**Statement (paraphrased).** If X is in standard form, X \ W = ⊔_{n∈ℕ} O_n is an infinite family, and d is a compatible metric, then diam(Ō_n) → 0.

**Verdict.** The statement is true, but the proof has a **gap** at the end. The repair is easy.

**Findings.**

- **MINOR ("{a_n, e_n} separates w(X) and Ō_n").** The PDF writes Ō_n, which is sloppy since a_n ∈ W ∩ Ō_n; it should say O_n. The correct and sufficient statement is: any path γ from a point outside O_n to a point of O_n meets ∂O_n. Proof: take the component (s,1] of γ⁻¹(O_n) that contains 1. This set is open because O_n is open in X. Then γ(s) ∈ Ō_n \ O_n ⊆ {a_n, e_n}. This uses only that O_n is open and that ∂O_n ⊆ {a_n, e_n}. It does not need the starting point to lie in W.
- **NOTE (choice of x_i, y_i).** diam(Ō_{n_i}) ≥ ε gives points with d(x_i, y_i) ≥ ε, because the closure is compact and so the diameter is attained. Choosing points with d ≥ ε/2 would avoid this point. The x_i, y_i may be endpoints, which lie in W.
- **MINOR ("Since the sets O_n are open, we must have x, y ∈ w(X)").** This is correct but needs a line. Suppose x ∈ O_m. Then O_m is a neighbourhood of x, so it meets Ō_{n_i} for large i, and therefore (being open) meets O_{n_i}, which forces n_i = m by disjointness. This contradicts n_i being strictly increasing. Also, X = W ∪ ⋃O_m. The same argument works for y and z.
- **NOTE (x ≠ y).** Correct: d(y_i, x) ≥ ε − d(x_i, x) > ε/2 for large i, so d(x, y) ≥ ε/2. The text repeats "for sufficiently large i" twice.
- **NOTE (relabelling).** This step is correct, but the reason is unstated. Each of U_x and U_y contains a frontier point of O_{n_i}: a path in U_x from x ∉ O_{n_i} to x_i meets ∂O_{n_i}, or x_i is itself a frontier point. U_x and U_y are disjoint, because they lie in the disjoint balls B(x,δ) and B(y,δ) with δ = d(x,y)/2. So the two frontier points are **distinct**, U_x contains exactly one of them, and U_y contains the other. In particular Ō_{n_i} cannot be a simple closed curve (a_n = e_n), and "both endpoints in one set" cannot happen. The paper should say this.
- **NOTE (existence of z_i).** This is correct. a_{n_i} ∈ U_x ∩ Ō_{n_i} and U_x is open, so U_x ∩ O_{n_i} ≠ ∅. Likewise U_y ∩ O_{n_i} ≠ ∅. Since O_{n_i} is connected and U_x, U_y are disjoint open sets, O_{n_i} ⊄ U_x ∪ U_y.
- **MAJOR (the last step).** The proof asserts "it must be that z ∉ B̄(x,δ/2) ∪ B̄(y,δ/2)". The only information available is z_i ∉ U_x ∪ U_y with U_x ⊆ B(x,δ). U_x may be a thin neighbourhood that does not contain B̄(x,δ/2), so z can lie close to x while being outside U_x. What does follow is z ∉ U_x ∪ U_y, since X \ (U_x ∪ U_y) is closed; in particular z ≠ x and z ≠ y. The final contradiction is also invalid as written. U_z is chosen disjoint from B̄(x,δ/2) ∪ B̄(y,δ/2), but a_{n_i} ∈ U_x ⊆ B(x,δ) may lie at distance between δ/2 and δ from x, and so may lie in U_z. So "U_z contains a_{n_i} or e_{n_i}" contradicts nothing.

  *Repair:*
  1. Once x, y, z ∈ W are found, pairwise distinct, set η = ½·min{d(x,y), d(y,z), d(x,z)} > 0.
  2. Choose path-connected (or merely connected) open sets V_x, V_y, V_z inside the η-balls around x, y, z. These sets are pairwise disjoint.
  3. For large i we have x_i ∈ V_x, y_i ∈ V_y and z_i ∈ V_z. By the separation fact, each of V_x, V_y, V_z meets ∂O_{n_i}, which has at most two points. This is a contradiction, by pigeonhole.

  The relabelling step then becomes unnecessary. A cleaner variant avoids x_i, y_i altogether: Ō_{n_i} is connected and meets both U_x and the complement of U_x ∪ U_y, which directly gives three separated limit points.

---

## Corollary 4.4

**Statement (paraphrased).** With infinitely many arcs, a_n ∈ Ō_n \ O_n, n₁ < n₂ < ⋯ and a_{n_i} → x ∈ W: for every neighbourhood U of x, Ō_{n_i} ⊆ U for all but finitely many i.

**Verdict.** Correct, apart from a minor index slip.

**Findings.**

- **MINOR (index).** "there exists i₁ ≥ i₀ such that diam(Ō_n) < ε/2" should read "such that diam(Ō_{n_i}) < ε/2 for all i ≥ i₁". This follows from Lemma 4.3 because n_i → ∞; injectivity of i ↦ n_i is enough. The final estimate is fine: for p ∈ Ō_{n_i}, d(p,x) ≤ diam(Ō_{n_i}) + d(a_{n_i}, x) < ε. Closures are used consistently, and the open arcs O_{n_i} are of course covered too.
- **NOTE.** The hypothesis x ∈ w(X) is redundant, since a_n ∈ W and W is closed. Strict monotonicity can be weakened to injectivity. The proof uses only Lemma 4.3 and the metric.

---

## Lemma 4.5 (characterisation of the topology)

**Statement (paraphrased).** Let X be in standard form with X \ W = ⊔_{n∈N} O_n, where N is italic in the PDF; Section 5 defines N as "the set of n for which O_n is defined", so N may be finite. A set U ⊆ X is open if and only if:

1. U ∩ W is open in W;
2. U ∩ Ō_n is open in Ō_n for every n;
3. whenever n₁ < n₂ < ⋯ and x_{n_i} ∈ ∂O_{n_i} with x_{n_i} → x ∈ U ∩ W, then Ō_{n_i} ⊆ U for all but finitely many i.

**Verdict.** The statement is true, including for finite N, but the compactness part of the proof has a **gap**. The repair is short.

**Findings.**

- **NOTE (topology).** This checks out. ∅ satisfies (3) vacuously, and X satisfies (1)–(3). Arbitrary unions: if x ∈ U_α ∩ W, then (3) for U_α gives Ō_{n_i} ⊆ U_α ⊆ ⋃U_β eventually. Finite intersections: if x ∈ U ∩ V ∩ W, the two "eventually" statements combine. Conditions (1) and (2) are clearly stable under both operations.
- **NOTE ("open ⇒ (1)–(3)").** Correct. (1) and (2) hold by restriction. For (3), apply Corollary 4.4 with the choice a_{n_i} := x_{n_i} (and an arbitrary frontier point for the other n), using U as a neighbourhood of x. This gives τ_X ⊆ τ_{X′}, so id: X′ → X is continuous.
- **NOTE (homeomorphism).** Correct. A continuous bijection from a compact space onto a Hausdorff space (X is metric) is a homeomorphism. X′ does not need to be shown Hausdorff.
- **NOTE (W and Ō_n compact in X′).** The argument for W is correct: by (1) and τ_X ⊆ τ_{X′}, the two subspace topologies on W coincide. W is compact because it is closed in X, which follows from Lemma 2.3, or directly from W = X \ ⋃O_n with every O_n open. The proof then uses "the sets Ō_n are compact" in X′ without comment. This is true by the same argument applied to (2), and should be said.
- **MINOR (typos in the compactness paragraph).** The PDF reads: "there exists V₁, V₂, …, V_m ∈ 𝒰 such that w(X) ⊆ V = ⋃_{i=1}^m V_i". Here 𝒰 should be 𝒱, the cover. "as a a subspace" should read "as a subspace". The reduction "it suffices to show Ō_n ⊆ V for all but finitely many n" is valid, because X = W ∪ ⋃_n Ō_n and each remaining Ō_n is compact in X′.
- **MAJOR (circular step in the finite-subcover argument).** The proof takes y_i ∈ Ō_{n_i} \ V and y_i → x in X, notes x ∈ W ⊆ V, and concludes "y_i ∈ V for sufficiently large i". But V is a union of X′-open sets, and it is not yet known to be open in X; that is exactly what is being proved. Convergence in X says nothing about V. Condition (3) is never invoked in the compactness argument, and without (3) the conclusion is false. For example, in the earring take one point p_n ∈ O_n with p_n → b₀. Under (1) and (2) alone, {p_n} is closed and discrete, so the topology defined by (1)–(2) is not compact.

  *Repair:*
  1. y_i ∉ V ⊇ W, so y_i ∈ O_{n_i}.
  2. Pick a_{n_i} ∈ ∂O_{n_i}. By Lemma 4.3, d(a_{n_i}, y_i) ≤ diam Ō_{n_i} → 0, so a_{n_i} → x. This convergence holds in X, and hence in W, where the two topologies agree.
  3. Since x ∈ W ⊆ V, we have x ∈ V_j for some j. Condition (3) for V_j gives Ō_{n_i} ⊆ V_j ⊆ V for all but finitely many i, which contradicts y_i ∉ V.
- **NOTE (index set; finitely many arcs).** The lemma also holds for finite N. Then (3) is vacuous, since there are no strictly increasing sequences in a finite set. The statement reduces to the fact that X is the union of finitely many closed sets W, Ō₁, …, Ō_k and carries the coherent topology with respect to them, which is true for any finite closed cover. The paper's proof also goes through: Corollary 4.4 is only invoked vacuously, and the "all but finitely many n" step is trivial. The statement mixes italic N (in "{O_n | n ∈ N}") with blackboard ℕ (in (2)); it should use N throughout, matching Section 5.
- **NOTE (Section 5 uses both directions).** Lemma 5.2 uses "(1)–(3) ⇒ open", and Lemma 5.5 uses "open ⇒ (3)". Both are valid once the gap above is repaired.

---

## Hypotheses actually used

None of Definition 4.1's consequences, Lemma 4.3, Corollary 4.4 or Lemma 4.5 uses **one-dimensionality**, the **earring-based definition of w(X)**, or the fact that the O_n are **arcs** (beyond the frontier count). The precise requirements are as follows.

**Lemma 4.3** (in the repaired form). It needs:
- (X, d) is a compact metric space; only sequential compactness is used.
- X is **locally connected**. The paper uses path-connected neighbourhoods, but connected open neighbourhoods suffice: a connected open V that meets both O and its complement meets ∂O.
- (O_i)_{i∈ι} is a family of pairwise disjoint, non-empty, open, connected subsets of X.
- |∂O_i| ≤ 2 for every i. The argument generalises to |∂O_i| ≤ k, using k + 1 separated limit points.

It needs neither a set W nor X = W ∪ ⋃O_i, because a limit of points from distinct members of a disjoint open family automatically lies outside every member. **Formalisation-friendly conclusion:** for every ε > 0, the set {i | diam(closure O_i) ≥ ε} is finite. Equivalently, diam ∘ closure ∘ O tends to 0 along the cofinite filter. This form covers finite ι for free and does not need an enumeration by ℕ.

**Corollary 4.4.** Lemma 4.3 and the metric. The hypothesis x ∈ W is not needed.

**Lemma 4.5.** It needs:
- The hypotheses of Lemma 4.3.
- W := X \ ⋃_i O_i; this set is automatically closed, hence compact.
- X Hausdorff and compact, for the "continuous bijection from a compact space" step.
- Each closure(O_i) compact, which is automatic in a compact space.

It uses Corollary 4.4 for "open ⇒ (3)", and Lemma 4.3 together with (3) for compactness of X′ (as repaired). A convenient formal version of (3): for every x ∈ U ∩ W, there is a neighbourhood N of x such that closure(O_i) ⊆ U for all but finitely many i with ∂O_i ∩ N ≠ ∅. This is equivalent, by the compactness and metric arguments above, and avoids sequences.

**Definition 4.1 well-posedness.** Here the specific choice W = w(X) does matter, through **Lemma 2.3** (w(X) is closed for locally path-connected, first-countable X), which makes X \ W open. From that, X locally path-connected, and Sierpiński's theorem (or finitely many O_n), the O_n are open and are exactly the components of X \ W. For a formalisation, simply assume "each O_n is open in X", or define the O_n as the components of X \ W with W closed.

**The paragraph after Definition 4.1.** The first claim needs: W closed, X locally path-connected, finitely many O_n with ∂O_n ⊆ W, each closure an arc or a circle (for the sub-arc contraction), and, for "w(P_j) = P_j", the actual definition of w together with the paper's equivalence between Definition 2.2 and the small-essential-loop definition for first-countable spaces. The "Hence" clause additionally needs w(X) **countable**; it is false otherwise.

**Abstract setting sufficient for Section 4, as needed downstream.** X is a compact metric space that is locally connected (locally path-connected for Section 5). W ⊆ X is closed. X \ W is the disjoint union of open, connected sets O_i (i ∈ N, with N countable, possibly finite or empty), and ∂O_i ⊆ W with 1 ≤ |∂O_i| ≤ 2. The homeomorphisms h_n with [0,1] are needed only in Section 5.
