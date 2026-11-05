# Novelty assessment: Brazas–Pavešić, "Countable models of one-dimensional Peano continua"

arXiv:2610.35875v1 [math.GN], 10 Aug 2026, 14 pages
([abstract](https://arxiv.org/abs/2610.35875)). Local copy: `papers/2610.35875.{pdf,txt}`.
Assessment date: 2026-10-28.

Conventions. A *Peano continuum* is a connected, locally path-connected, compact metrizable space.
The *wild set* `w(X)` is the set of points at which `X` is not semilocally simply connected
(equivalently, for first-countable spaces, the points at which there is a *fully essential* map from
the infinite (Hawaiian) earring `𝔼`). A *weak homotopy equivalence* induces a bijection on `π₀` and
isomorphisms on all homotopy groups `πₙ` at every basepoint. An *A-space* (Alexandroff space) is a
space in which arbitrary intersections of open sets are open. "Bull. LMS" means *Bulletin of the
London Mathematical Society*. Paper numbering (L = Lemma, T = Theorem, C = Corollary) follows
`notes/structure.md`.

**Evidence levels used below.**
- **[opened]**: I read the statement in a source I downloaded or fetched in this session (link given).
- **[abstract]**: I saw only the publisher's abstract, not the full text.
- **[recalled]**: from memory; not checked against a source in this session.
- **[inferred]**: my own mathematical argument; it needs the adversarial review that `CLAUDE.md`
  requires before anything depends on it.

## Summary table

| # | Item | Classification | Evidence (links) | Confidence |
|---|---|---|---|---|
| 1a | T1.1 "only if" (a weak homotopy equivalence `X → Y` with `Y` countable forces `w(X)` countable) | **New as a statement**. The proof is a **routine adaptation** of Eda's spatial-homomorphism theorem (2002) and the discrete-monodromy argument of Brazas–Fischer 2020, §9. All the content is in L6.4. | Brazas–Fischer [arXiv:1902.08887](https://arxiv.org/abs/1902.08887) Lemma 9.17, Prop. 9.13, Thm 9.15, Cor. 9.19 [opened]; Eda 2002 Theorem A, as quoted in Kent [arXiv:1305.4215](https://arxiv.org/abs/1305.4215) [opened] | Medium–high |
| 1b | T1.1 "if" (countable `w(X)` gives a countable model) | **New.** It generalises the coarse earring of Brazas–Matos 2019, which never compared that space with `𝔼`. Two inputs are cited: Meilstrup's standard form and the coarsification. Small gap: the case `w(X)=∅` is not covered by the standard form as defined (it is trivial by McCord). | Brazas–Matos, [Involve 12 (2019) 381–394](https://msp.org/involve/2019/12-3/involve-v12-n3-p02-s.pdf) [opened] | High |
| 2 | T1.2 (classification by compact countable ordinals) | **Direct combination of known results**: Eda 2022, Brazas–Fischer Thm 9.15 and Mazurkiewicz–Sierpiński. The only new input is T1.1, which renames the class. **As stated it is false when `w(X)=∅`**, because Eda 2022 assumes a non-empty wild set. | Eda 2022 [abstract](https://www.impan.pl/en/publishing-house/journals-and-series/fundamenta-mathematicae/all/259/3/114610/one-dimensional-peano-continua-with-zero-dimensional-wild-part) ("zero-dimensional and non-empty") [abstract]; Brazas–Fischer Thm 9.15 [opened]; Mazurkiewicz–Sierpiński 1920 [recalled] | High for "combination"; high for the `w=∅` defect |
| 3 | Coarsification `𝒞X`, L5.5 (lifting lemma) and C5.6 (Serre fibration, weak equivalence) | **New.** Brazas–Matos define only the coarse earring and prove that its `π₁` is uncountable, by a surjection onto the Baer–Specker group. They have **no map `𝔼 → 𝒞𝔼`, no lifting lemma and no weak-equivalence statement**. The lifting technique itself is elementary (Urysohn functions on perfectly normal spaces). | Brazas–Matos, [author preprint](https://health-sciences.wcupa.edu/sciences-mathematics/mathematics/jBrazas/documents/A%20countable%20space%20with%20an%20uncountable%20fundamental%20group.pdf) and the published Involve text [opened] | High |
| 4 | L6.4 (a `π₁`-isomorphism out of a one-dimensional space is injective on wild sets, for an **arbitrary** target `Y`) | **New in its generality** (arbitrary `Y`; earlier results need both spaces to be one-dimensional or planar, or a homotopy inverse). It is a **routine adaptation** of Brazas–Fischer Lemma 9.17 / Cor. 9.19 combined with Eda 2002. I also found a shorter proof [inferred] that **does not need §3 (`H₁`), L6.3 or the special choice of `g₀`**. | Brazas–Fischer §9 [opened]; Brazas–Mitra [arXiv:2505.23665](https://arxiv.org/abs/2505.23665) Lemma 4.2 and Example 4.9 [opened]; Brazas–Pavešić [arXiv:2510.22901](https://arxiv.org/abs/2510.22901) Thm 4.11, Lemma 4.14, Cor. 4.15 [opened] | Medium–high (the alternative proof is [inferred]) |
| 5a | L3.3 (`H₁(A) → H₁(X)` injective for `A ⊆ X` one-dimensional) | **Not located in the literature.** It is probably new as stated for arbitrary subsets, but it is a routine consequence of Eda's zero-form lemma. The special cases the paper actually uses are classical: a simple closed curve or a Peano subcontinuum is a retract. | Extension of maps into `S¹` over one-dimensional spaces (Engelking Thm 3.2.10; Burillo 1999 Cor. 20, quoted in Velut [arXiv:2608.30767](https://arxiv.org/abs/2608.30767) Cor. 2.5.8) [opened in Velut]; Cannon–Conner 2006 Lemma 3.1, quoted in arXiv:2510.22901 Lemma 3.4 [opened] | Medium |
| 5b | L3.4 (disjoint reduced loops, one not null-homologous, are not homologous) | **Not located.** It is an `H₁` analogue of the known `π₁` fact that freely homotopic essential loops in a one-dimensional space cannot have disjoint images. Probably new as stated; **not needed** for the main theorem (see item 4). | Brazas–Fischer Prop. 9.13(b) [opened]; arXiv:2510.22901 Lemma 4.14 [opened] | Medium–low |
| 5c | L4.3 (`diam Oₙ → 0`) | **Not located.** It is a standard continuum-theory argument that uses the two-point boundaries; probably implicit in Meilstrup 2005 or Eda 2010. Routine. | Meilstrup's thesis could not be downloaded (Cloudflare block); Eda 2010 is paywalled | Low (not verified either way) |
| 5d | L4.5 (topology of a standard-form continuum by conditions (1)–(3)) | **Routine adaptation** of the "shrinking point-attachment space" topology in Brazas–Mitra 2025. Conditions (1)–(3) have the same form there, and the compactness proof follows the same pattern. | arXiv:2505.23665 Def. 5.5, Prop. 5.9 [opened] | High |
| 5e | L2.5 (`π₁`-injective maps preserve wild points) | **Known**, and given without citation. | Brazas–Mitra 2025 Lemma 4.2 (n = 1) [opened]; arXiv:2510.22901 Lemma 3.7 [opened]; first step of the proof of Brazas–Fischer Thm 9.15 [opened] | High |
| 5f | L2.3, R2.7, L2.8, L3.2, T4.2, T6.1, L6.2, T6.6 | **Cited** results. Three citation issues: T6.6 omits "non-empty"; L6.2 is cited to Brazas–Fischer Prop. 9.13, but the statement is really Lemma 9.17 + Prop. 9.13; T4.2 omits `w(X) ≠ ∅`. | see §5 | High |
| 6 | The question "which Peano continua are weakly homotopy equivalent to countable spaces?" | **No earlier formulation found.** Context: McCord/Stong (finite and A-space models) answer it for spaces with countable homotopy groups. Brazas–Matos give the first countable non-A-space with uncountable `π₁`. Karimov–Repovš give a non-contractible Peano continuum that is weakly contractible, so it trivially has a one-point model. | McCord 1966, Stong 1966, Barmak 2011 [recalled; cited in the paper]; Brazas–Matos [opened]; Karimov–Repovš [PAMS 138 (2010)](https://www.ams.org/journals/proc/2010-138-04/S0002-9939-09-10217-4) [abstract via search]; [wildtopology.com problem list](https://wildtopology.com/problemlist/) [opened] | Medium |
| 7 | Later versions, errata, citing papers | Only v1 exists. No errata. No citing paper found. The authors' later preprint arXiv:2608.16780 (Conner–Herfort–Kent–Pavešić, 17 Aug 2026) does not cite it. | [arXiv abstract page](https://arxiv.org/abs/2610.35875) [opened]; arXiv API author listings [opened] | Medium (Google Scholar not directly queryable) |

## Item 1: Theorem 1.1

### 1a. "Only if": a weak equivalence to a countable `Y` forces `w(X)` to be countable

**Proof in the paper.** L6.4 gives an injection `w(X) ↪ w(Y) ⊆ Y`. So the direction is exactly as
strong as L6.4, and the analysis is in item 4.

**Prior literature.**
- **Brazas–Fischer 2020, Thm 9.15 [opened].** If `X` and `Y` both have the discrete monodromy
  property (all one-dimensional metric spaces do, by Prop. 9.13) and `f` is a **homotopy
  equivalence**, then `f` maps `w(X)` homeomorphically onto `w(Y)`.
- **Brazas–Fischer 2020, Cor. 9.19 [opened].** The same conclusion holds for a `π₁`-isomorphism
  that is realised by maps in both directions.
- **Brazas–Pavešić, arXiv:2510.22901, Cor. 4.15 [opened].** The same conclusion for homotopy
  equivalences between one-dimensional Hausdorff spaces.

All of these need either a homotopy inverse or a target with the discrete monodromy property.
Remark 6.5 of the paper (`𝔼 → 𝔼 × [0,1]`) shows that such a hypothesis cannot simply be dropped if
one wants a bijection. I found no earlier result about weak equivalences or `π₁`-isomorphisms into
an **arbitrary** target. Brazas–Mitra 2025, Example 4.9 [opened], discusses the `n`-dimensional
analogue heuristically: if a weak equivalence identified two wild points, "one should be able to
use infinite products of Whitehead products" to contradict surjectivity, and they call this
"conjectural". L6.4 settles the case `n = 1`.

**Verdict.** The statement is new. The method is a routine adaptation (see item 4).

### 1b. "If": a countable wild set gives a countable model

**Proof in the paper.** Meilstrup's standard form (T4.2), then the coarsification `q : X → 𝒞X`,
which is countable when `w(X)` is countable (R5.1) and is a weak equivalence (C5.6).

**Prior literature.** Brazas–Matos built only the coarse earring and showed only that its `π₁` is
uncountable (see item 3). The paper itself says the coarse earring "appears to be a model (of weak
homotopy type) for `𝔼`". C5.6 applied to `X = 𝔼` is the first proof of that claim that I could find.
Nothing for general one-dimensional Peano continua was found.

**Gaps found while reading.**
- Definition 4.1 requires `\bar{Oₙ} \ Oₙ ⊆ w(X)`. So a finite graph (`w(X) = ∅`, not a tree) is
  never in standard form.
- T4.2 as quoted omits the hypothesis `w(X) ≠ ∅`, which the same authors state explicitly in
  arXiv:2510.22901, Thm 3.10 [opened].
- The case `w(X) = ∅` is easy: `X` is homotopy equivalent to a finite graph (arXiv:2510.22901,
  Thm 3.9, from Conner–Meilstrup's deforestation), and a finite graph is weakly equivalent to a
  finite space by McCord. But the paper never treats it.
- The step "by L6.4, `h` maps `w(X′)` injectively into `w(X)`" is heavier than needed. Meilstrup's
  homotopy equivalence already preserves the wild set (arXiv:2510.22901, §3: "`w(X) = w(Y)`"), and
  Brazas–Fischer Thm 9.15 would also do.

**Verdict.** New. Small presentation gap for `w(X) = ∅`.

## Item 2: Theorem 1.2 (classification by compact countable ordinals)

**Ingredients of the proof.**
1. Eda 2022 (paper T6.6): for one-dimensional Peano continua with zero-dimensional wild sets,
   `X ≃ Y` if and only if `w(X) ≅ w(Y)`.
2. Brazas–Fischer Thm 9.15: a homotopy equivalence restricts to a homeomorphism of wild sets.
3. Mazurkiewicz–Sierpiński (Fund. Math. 1, 1920) [recalled]: every countable compact metrizable
   space is homeomorphic to a countable successor ordinal `ω^α·n + 1`.
4. An explicit realisation `A_λ` of every compact countable ordinal as a wild set. This is a special
   case of Brazas–Mitra 2025, Thm 1.2 [opened], which realises any compact metric space as a wild
   set with complement a countable union of open 1-cells.
5. T1.1, used only to identify "countable wild set" with "has a countable model".

**How much is new.** Ingredients 1–4 already classify one-dimensional Peano continua with
**non-empty countable** wild sets by `ω^α·n + 1`, with `α < ω₁` and `1 ≤ n < ω`. A countable
compact metric space is zero-dimensional, so Eda 2022 applies directly. I could not open Eda 2022
(paywalled), so I cannot say whether Eda states the countable or ordinal case himself. What T1.2
adds is the rewording through T1.1. Classification: **direct combination of known results plus
T1.1.**

**Defect (high confidence).** Eda 2022's abstract [abstract] states the hypothesis as "`X^w` is
zero-dimensional **and non-empty**". The paper's T6.6 drops "non-empty". Consider the continua with
`w(X) = ∅`:
- they are homotopy equivalent to finite graphs, that is, wedges of `k ≥ 0` circles;
- they have countable (empty) wild set;
- they are weakly equivalent to finite spaces (McCord);
- they form **countably many** distinct homotopy types, all with the same wild set `∅`.

Two readings of "compact countable ordinal" are possible, and T1.2 fails under both:
- If the empty ordinal is included, `[0] ↦ Ho(A_0)` is not surjective onto these types.
- If it is excluded, the finite graphs are outside the image.

The surjectivity step "`Ho(X) = Ho(A_λ)` by T6.6" fails for `w(X) = ∅`. Fix: restrict to
`w(X) ≠ ∅` (equivalently, `X` not homotopy equivalent to a finite graph). Two smaller points:
- "for each ordinal `κ ≤ λ`" should be `κ < λ` if `λ` denotes the space `[0, β]`.
- The intro says the homotopy groups of a polyhedron must be "countably presented"; countability
  of the groups is what matters.

## Item 3: Coarsification and the lifting lemma vs Brazas–Matos's coarse earring

**What Brazas–Matos do [opened: 2017 author preprint and the 2019 Involve text from msp.org].**
- They define the coarse interval `I` (3 points), the coarse circle `S` (4 points) and the coarse
  line `L`.
- They show that `L → S` is a covering map, so `π₁(S) ≅ ℤ`, and they give a map `S¹ → S` that is
  an isomorphism on `π₁`.
- They define the coarse earring `H = {w₀} ∪ ⋃{xₙ, yₙ, zₙ}`. Its basis is `{xₙ}`, `{zₙ}`,
  `{xₙ, yₙ, zₙ}` and `Vₙ = H \ {y₁, …, yₙ₋₁}`. They prove that it is compact, `T₀`,
  path-connected and locally path-connected, and that it retracts onto each coarse circle.
- Their Thm 29: `π₁(H)` surjects onto the Baer–Specker group `ℤ^ℕ`, so it is uncountable.
- The published version adds: "countable spaces need not be weakly homotopy equivalent to
  countable simplicial complexes."
- **There is no map `𝔼 → H`, no comparison of `π₁(H)` with `π₁(𝔼)`, no higher homotopy groups, no
  lifting property, and no fibration.**

**What Brazas–Pavešić generalise.**
1. Construction. `𝒞𝔼` (paper §5) is exactly Brazas–Matos's `H`, under the renaming
   `(aₙ, bₙ, cₙ) ↔ (xₙ, yₙ, zₙ)`. For a general standard-form `X`, each open arc `Oₙ` of
   `X \ w(X)` becomes a 3-point coarse open arc `{bₙ, cₙ, dₙ}`. The wild set keeps its own
   topology, and the topology near `w(X)` comes from the quotient. Brazas–Matos give the topology by
   an explicit basis; Brazas–Pavešić define `𝒞X` as a quotient of `X`. That choice is what makes a
   comparison map available.
2. Comparison. L5.2 (`q` is open) and L5.5 (relative lifting for any closed `A ⊆ B` with `B`
   locally path-connected and metrizable) are new; nothing like them is in Brazas–Matos. C5.6 (`q`
   is a Serre fibration and a weak equivalence) is new, and for `X = 𝔼` it upgrades Brazas–Matos's
   "uncountable `π₁`" to "weakly equivalent to `𝔼`".
3. Technique. The lifting uses Urysohn functions on perfectly normal spaces (L5.4) to extend maps
   into the arcs `\bar{Bₙ}`, `\bar{Dₙ}` with prescribed preimages of the endpoints. It also uses the
   "shrinking" condition (3) of L4.5 for continuity at wild points. This is elementary, and close in
   spirit to the classical proof that `[0,1] →` coarse interval is a weak equivalence.
   - McCord's 1966 method (basis-like open covers) does not apply directly, because `𝒞X` has no
     minimal neighbourhoods at wild points.
   - I found no earlier paper that proves a quotient onto a countable non-A-space is a Serre
     fibration. One search ("McCord map Serre fibration quasifibration") found nothing relevant.

**Verdict.** New. It generalises the coarse earring as a space; the Serre-fibration and
weak-equivalence argument is **not** in Brazas–Matos.

## Item 4: Lemma 6.4 vs Brazas–Fischer, Eda, Cannon–Conner, Conner–Kent, Brazas–Mitra

**Statement.** Let `X` be a path-connected, locally path-connected, one-dimensional metric space
and `Y` any path-connected space. If `f : X → Y` induces `π₁`-isomorphisms, then `f|w(X)` is
injective.

**Closest prior results [opened unless marked].**
- **Brazas–Fischer 2020, §9.**
  - Prop. 9.13: one-dimensional metric spaces have the discrete monodromy property.
  - Lemma 9.17: if `Y` has that property, `ϕ_β ∘ f_# = g_#` at `x`, and `f(x) ≠ g(x)`, then
    `f_#` kills `π₁(W, x)` for some neighbourhood `W` of `x`.
  - Thm 9.15 (homotopy equivalences) and Cor. 9.19 (isomorphisms realised by maps both ways): wild
    sets correspond homeomorphically.
  - All of these need the *target* to have discrete monodromy.
- **Eda 2002**, Theorem A as quoted in Kent arXiv:1305.4215 [opened]: every homomorphism
  `π₁(X) → π₁(Y)`, with `X` a one-dimensional Peano continuum and `Y` a one-dimensional metric
  space, is induced by a map up to change of basepoint. The basepoint path is unique up to homotopy
  when the image is uncountable.
- **Eda 2010** (Fund. Math. 209) [abstract]: isomorphic `π₁` implies homotopy equivalent, for
  one-dimensional Peano continua.
- **Conner–Eda 2005** [recalled; cited in Kent]: the wild set of a one-dimensional Peano continuum
  can be reconstructed from `π₁`.
- **Conner–Kent** [recalled; cited in Kent]: the analogous planar results.
- **Cannon–Conner 2006**: reduced paths. Its Cor. 3.3 (subspaces are `π₁`-injective) is quoted
  as arXiv:2510.22901 Cor. 3.2 [opened].
- **Brazas–Mitra 2025**: Lemma 4.2 (`π₁`-injective maps preserve wild sets and homotopies between
  them); Thm 4.6 (the homotopy type of `w` is a homotopy invariant); Example 4.9 (the `n`-dimensional
  question for weak equivalences, left conjectural).

**What is new.** The target `Y` is arbitrary: not metric, not one-dimensional, possibly countable
and non-`T₁`. The proof transfers everything back into `X` through `f_#⁻¹` and applies Eda's theorem
inside `X`. I found this generalisation nowhere earlier.

**Classification: routine adaptation.** The skeleton is the proof of Brazas–Fischer Cor. 9.19,
with Eda's theorem (applied to `f_#⁻¹ ∘ h_#`) in place of the backward map `g`. Lemma 6.2 is
itself Brazas–Fischer Lemma 9.17 applied to the even half of `h`.

**A shorter proof exists [inferred; needs adversarial review].** Keep the paper's notation:
- `h : 𝔼 → Y` interleaves `f∘g₀` (odd circles) and `f∘g₁` (even circles);
- `g, δ` come from Eda's theorem;
- `g₃ = g ∘ σ_odd`, where `σ_odd(ℓ_j) = ℓ_{2j−1}`.

The argument:
1. Pick a path `α` from `x₀` to `x₁`. By surjectivity of `f_#` at `x₁`, pick a loop `β` at `x₁`
   with `f_#[β] = [f∘α]`.
2. A direct computation gives `f_{#,x₁}⁻¹ ∘ f_{#,x₀} = ϕ_{α·β⁻}`, a change of basepoint in `X`.
3. Hence `(g₃)_#` and `(g₀)_#` differ by a change of basepoint along a path in `X` from `x₀` to
   `g(b₀)`.
4. Brazas–Fischer Lemma 9.17, applied with target `X` (discrete monodromy by Prop. 9.13) and
   source `𝔼`, gives `g(b₀) = g₀(b₀) = x₀`. Otherwise `g₀` would be trivial on `π₁` of a
   neighbourhood of `b₀`, contradicting that it is fully essential.
5. The same lemma applied to the even half (the paper's L6.2) gives `g(b₀) = x₁`. So `x₀ = x₁`.

This argument uses neither `H₁`, nor L3.3, L3.4 or L6.3, nor the special choice of `g₀`. Like the
paper's argument, it uses both injectivity and surjectivity of `f_#`.

Surjectivity really is needed. Collapse the arc joining two earrings: the map is
`π₁`-injective, not surjective, and identifies two wild points. That `π₁(X)` is the free product
`π₁(𝔼) * π₁(𝔼)`, which is not all of `π₁(𝔼 ∨ 𝔼)`, I worked out myself [inferred].

**Consequence for the paper.** §3 (homology of one-dimensional spaces) and L6.3 are a detour. They
are not wrong as far as I checked, but the main theorem does not need them.

## Item 5: Lemmas 3.3, 3.4, 4.3, 4.5 (and L2.5)

- **L3.3** (`H₁` injectivity for arbitrary subspaces).
  - Not found in any source I could open. Eda 2016 (Fund. Math. 232) is paywalled. Its abstract
    [via search] is about the isomorphism type of `H₁` (free of finite rank or `H₁(𝔼)`), not about
    subspace injectivity.
  - Curtis–Fort, Ann. of Math. 69 (1959), "Singular homology of one-dimensional spaces": I could
    not open it. I recall [recalled] it proves vanishing of `Hₙ` for `n ≥ 2` and structure results
    for `H₁`, and I do not know that it contains subspace injectivity.
  - The only use in the paper (L6.3, `A` a simple closed curve) is classical: a map from a closed
    subset of a one-dimensional normal space into `S¹` extends (Engelking, Thm 3.2.10), so a simple
    closed curve is a retract and `H₁` injects. This is stated with proof, after Burillo 1999
    Cor. 20, in Velut arXiv:2608.30767 Cor. 2.5.8 [opened].
  - For Peano subcontinua, Cannon–Conner Lemma 3.1 already gives a retraction.
  - Verdict: probably new in full generality; a routine consequence of Eda's zero-form lemma.
- **L3.4** (homologous disjoint loops). Not found. It is the `H₁` analogue of the known `π₁` fact
  (Brazas–Fischer Prop. 9.13(b); arXiv:2510.22901 Lemma 4.14) that essential, freely homotopic loops
  in a one-dimensional metric space cannot have disjoint images. Probably new as stated; not
  needed (item 4).
- **L4.3** (`diam Oₙ → 0`). Not found. I could not access Meilstrup's thesis (BYU ScholarsArchive
  blocks automated download) or Eda 2010. The argument is standard continuum theory and depends on
  each `Oₙ` having a two-point boundary. The general statement "components of `X \ K` form a null
  family" is **false** in Peano continua: take strips in a square. So the lemma is not a direct
  quotation of a textbook fact. Probably implicit in the standard-form literature. Routine.
- **L4.5** (topology by conditions (1)–(3)).
  - The conditions copy Brazas–Mitra 2025 Def. 5.5 [opened], where `U` is open iff `X ∩ U` is open
    in `X`, `Bⱼ ∩ U` is open in each `Bⱼ`, and attachment points converging to `x ∈ U` force
    `Bⱼᵢ ⊆ U` eventually.
  - The compactness half of the proof follows Brazas–Mitra Prop. 5.9.
  - The shrinking-wedge topology (arXiv:2510.22901 Def. 4.4) is the one-point case.
  - Routine adaptation.
- **L2.5.** Known: Brazas–Mitra Lemma 4.2; Brazas–Pavešić arXiv:2510.22901 Lemma 3.7; the first
  line of the proof of Brazas–Fischer Thm 9.15. Presented without citation.
- **Cited results checked.**
  - L2.3 = Brazas–Mitra Prop. 2.9 [opened].
  - L6.2: the cited "[5, Prop. 9.13]" is the discrete-monodromy proposition. The statement used is
    Lemma 9.17 combined with Prop. 9.13. The numbering is the same in arXiv v2 and in the
    paper's other citations.
  - T6.6 omits "non-empty" (item 2).
  - T4.2 omits `w(X) ≠ ∅` (item 1b).

## Item 6: Earlier answers to "which spaces are weakly equivalent to countable spaces?"

- **McCord 1966; Stong 1966** [recalled; cited by the paper and by Brazas–Matos]:
  - every finite space has the weak homotopy type of a finite polyhedron, and conversely;
  - more generally, every simplicial complex `K` is weakly equivalent to the A-space of its
    simplices, which is countable when `K` is.
  - Combined with CW approximation [recalled], every space with countably many path components and
    countable homotopy groups has a countable A-space model. Countable A-spaces have countable
    homotopy groups (the paper says this).
  - So the question is open only for spaces with an uncountable homotopy group.
- **Barmak 2011 (LNM 2032); Barmak–Minian, minimal finite models** ([arXiv:math/0611156](https://arxiv.org/abs/math/0611156)) [search snippet]: minimal *finite* models. They do not address countable models of non-polyhedra.
- **Brazas–Matos 2019** [opened]: the first countable, compact, `T₀`, locally path-connected space
  with uncountable `π₁`. Their remark that "countable spaces need not be weakly homotopy equivalent
  to countable simplicial complexes" is the closest earlier statement. They do not ask which
  continua admit countable models.
- **Karimov–Repovš** ([PAMS 138 (2010)](https://www.ams.org/journals/proc/2010-138-04/S0002-9939-09-10217-4)) [search snippet]:
  - a non-contractible Peano continuum (one-point compactification of a polyhedron) with all
    homotopy groups trivial;
  - it is weakly equivalent to a point, so it trivially has a countable model.
  - So "countable model" does not detect homotopy type in general. This is consistent with the
    open Whitehead-theorem question for finite-dimensional Peano continua (Brazas–Mitra 2025,
    Problem 1.1; [wildtopology.com](https://wildtopology.com/problemlist/)).
- **Inverse limits of finite spaces.**
  - Clader, Homology Homotopy Appl. 11 (2009) [search snippet]: finite simplicial complexes are
    homotopy equivalent to inverse limits of finite spaces.
  - Mondéjar–Morón ([arXiv:1802.04331](https://arxiv.org/abs/1802.04331)) [search snippet]:
    compacta reconstructed from finite approximations.
  - These are non-Hausdorff models of compacta, but uncountable ones, so they do not bear on the
    question.
- **Problem lists.** The wildtopology.com problem list [opened] has no problem about countable
  models. The authors' own earlier preprints (arXiv:2505.23665, 2510.22901, 2604.14929) [opened] do
  not pose it.
- **Verdict.** The question appears to be first posed in this paper. Its one-dimensional answer is
  new. Medium confidence, because the full-text search is limited to accessible sources.

## Item 7: Later versions, errata and citations

- arXiv abstract page: only v1 (10 Aug 2026, 299 KB, "14 pages, 5 figures"), with no journal
  reference.
- Brazas's research page lists it as a "preprint (2026)".
- arXiv API listings for Brazas and Pavešić up to 28 Oct 2026 show no later version and no
  erratum.
- The two later papers by these authors that I checked do not cite it:
  - arXiv:2608.16780 (Conner–Herfort–Kent–Pavešić, 17 Aug 2026);
  - arXiv:2604.14929 (Brazas–Mitra, which is earlier).
- A web search for the identifier found nothing else.

## Searches performed

| Query / action | Result |
|---|---|
| WebFetch `arxiv.org/abs/2610.35875` | v1 only, 10 Aug 2026; no journal reference |
| WebSearch "Brazas Pavešić countable models one-dimensional Peano continua" | Found the companion arXiv:2510.22901 (motion planning); downloaded it. It contains the standard-form theorem with `w(X)≠∅`, Lemma 3.7 (= L2.5) and Cor. 4.15 (wild sets preserved by homotopy equivalence) |
| WebSearch Brazas–Fischer title | arXiv:1902.08887; downloaded v2; read §9 (Lemma 9.5, Prop. 9.13, Thm 9.15, Lemma 9.17, Cor. 9.18–9.19) |
| WebSearch Brazas–Matos title | Author preprint (2017) and msp.org Involve PDFs; read in full. No weak-equivalence statement |
| WebSearch / WebFetch Eda 2022 (impan.pl) | Abstract: "zero-dimensional and non-empty". Full text paywalled |
| WebFetch Eda 2010 (impan.pl) | Abstract: isomorphic `π₁` implies homotopy equivalent; homomorphisms are induced by maps up to basepoint change |
| WebSearch Eda 2002 spatial homomorphisms | Full text not found. Statement obtained from Kent arXiv:1305.4215 Theorem A (opened) |
| WebSearch Eda 2016 singular homology | Abstract only (`H₁` is free of finite rank or `H₁(𝔼)`); no subspace-injectivity statement visible |
| WebSearch Curtis–Fort 1959 | Citation only; content not accessible |
| WebSearch "`H₁` injective subspace one-dimensional 0-form" | Velut arXiv:2608.30767 Cor. 2.5.8 (after Burillo 1999): closed subsets homotopy equivalent to `S¹`, finite wedges or `𝔼` are homotopy retracts of one-dimensional spaces |
| Eda's homepage (waseda.ac.jp) | Connection refused |
| arXiv API, author Eda | No arXiv versions of his one-dimensional Peano continuum papers |
| BYU ScholarsArchive, Meilstrup thesis (etd/550) | Abstract seen; PDF blocked by a Cloudflare challenge |
| arXiv API, authors Meilstrup, Conner, Brazas, Pavešić | Full listings; found arXiv:2604.14929 and 2608.16780, checked both for citations and overlap |
| Downloaded arXiv:2505.23665 (Brazas–Mitra) | Prop. 2.9 (= L2.3), Lemma 4.2 (= L2.5), Example 4.9 (`n`-dimensional analogue of L6.4 left conjectural), Def. 5.5 / Prop. 5.9 (pattern of L4.5), Thm 1.2 (realisation of wild sets) |
| WebSearch "countable topological space weakly homotopy equivalent … non-Hausdorff model Peano continuum inverse limit finite spaces" | Brazas–Matos; Barmak–Minian; Karimov–Repovš |
| WebSearch Clader inverse limits | Clader 2009 and Mondéjar–Morón; uncountable models only |
| WebSearch "McCord map Serre fibration quasifibration" | Nothing relevant |
| WebFetch wildtopology.com/problemlist | No countable-model problem; Whitehead problem for finite-dimensional Peano continua listed |
| WebFetch Brazas research page | Paper listed as a 2026 preprint; Matos's 2014–15 Georgia State University thesis "The coarse earring" |
| WebSearch "2610.35875" | Nothing relevant (no citing pages) |

## Open questions about novelty

1. Does Eda 2022 (Fund. Math. 259) state the countable or ordinal case of his classification? If
   so, T1.2 minus the T1.1 rewording is in Eda. This needs the full text.
2. Does Meilstrup's thesis or Eda 2010 contain L4.3 or an equivalent null-sequence statement for
   the arcs of a standard form? This needs the thesis PDF (manual download).
3. Is L3.3 (subspace injectivity of `H₁` for one-dimensional metric spaces) in Eda 2016 or in
   Curtis–Fort 1959? This needs the full texts.
4. Is the alternative proof of L6.4 in item 4 correct? It needs an adversarial check, in particular
   the computation `f_{#,x₁}⁻¹ ∘ f_{#,x₀} = ϕ_{α·β⁻}` and the application of Brazas–Fischer
   Lemma 9.17 with source `𝔼`. If it is correct, §3 and L6.3 can be removed from the critical path,
   including from any formalisation plan.
5. Does the uniqueness clause of Eda's 2002 theorem ("α unique up to homotopy when the image is
   uncountable") give L6.4 directly, as the paper itself hints ("there is a uniqueness part to
   Theorem 6.1")?
6. Has anyone shown that a quotient map onto a countable non-A-space is a Serre fibration, for
   instance in the finite-space literature on McCord maps as quasifibrations? One search found
   nothing.
7. Theorem 1.1 uses maps `X → Y` only. Is the same characterisation true for weak homotopy type in
   the zig-zag sense (`X ← Z → Y` with `Y` countable)? The "only if" proof does not cover a
   weak equivalence *into* `X`.
