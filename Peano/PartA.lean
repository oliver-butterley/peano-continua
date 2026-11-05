module

public import Peano.Homology
public import Peano.Earring
public import Peano.WildSet
public import Peano.HomotopyEquiv
public import Peano.Axioms.Cited
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Part A: π₁- and H₁-injectivity of subspaces, Lemmas 2.8, 3.3, 3.4 and 6.3

Brazas–Pavešić (arXiv:2610.35875), §2–3 and Lemma 6.3, with the repairs of `notes/checks/A.md`
and `notes/checks/D.md`. Homology is modelled as in `Peano.Homology`: `[α]_h = 0` means
`FundamentalGroup.fromPath ⟦α⟧ ∈ commutator (FundamentalGroup X x)`, and `H₁(A) → H₁(X)` is the map
`Abelianization (π₁(A, a)) → Abelianization (π₁(X, a))` induced by the inclusion.

**Scope.** The paper states Lemmas 3.3 and 6.3 for one-dimensional metrizable spaces and Lemma 3.4
for one-dimensional path-connected metrizable spaces. Here they are proved for one-dimensional
**Peano continua** (compact, connected, locally path-connected metric spaces of covering dimension
`≤ 1`) only: the cited axiom `eda_zeroForm` (Eda's Lemma 3.2), on which all three depend, is
assumed only in that generality, and this is all the paper's applications (§6, where `X` is a
one-dimensional Peano continuum) need. Lemma 2.8 keeps the paper's generality (any one-dimensional
metric space). The spaces are `X : Type` rather than `X : Type*` because the cited axioms are
stated for `Type`.

* **Closed subspaces.** `CoveringDimLE n X → IsClosed s → CoveringDimLE n s`
  (`CoveringDimLE.subtype_of_isClosed`): extend a finite open cover of `s` by `sᶜ`, refine in
  `X`, restrict.
* **Lemma 2.8** (`homotopic_refl_of_map_val`, `fundamentalGroup_map_val_injective`): for a
  one-dimensional metric space `X` and any `A ⊆ X`, the inclusion is injective on `π₁` at every
  base point. The cited Remark 2.7 (`exists_reduced_homotopy`, `isReparam_of_reduced_homotopic`) is
  assumed only for compact path-connected spaces, so it is applied in the image `K` of the
  null-homotopy, which is compact, path-connected and closed, hence one-dimensional: the reduced
  representative of the loop is homotopic in `K` to the constant loop, which is reduced, so by
  uniqueness it is constant; the homotopy from the loop to it lies in the image of the loop, inside
  `A`.
* **Lemma 3.3** (`fromPath_mem_commutator_of_map_val`, `abelianization_map_val_injective`): for a
  one-dimensional Peano continuum `X` and any `A ⊆ X`, the map
  `π₁(A, a)^ab → π₁(X, a)^ab` is injective. For path-connected `A` this is the paper's
  `H₁(A) → H₁(X)` (Hurewicz). For `A` with several path components `H₁(A)` is a direct sum over the
  components and the statement here covers one summand at a time; the general case (finding
  A-3.3-1 of `notes/checks/A.md`) is `fromPath_mem_commutator_of_sum_eq_zero` in
  `Peano.Lemma3_3General`, which builds on this file. Proof as in the paper with the repairs of
  A-3.3-3: an inessential loop in `A` is trivial; otherwise it is essential in `X` (Lemma 2.8),
  `eda_zeroForm` gives a reduced 0-form `ρ` homotopic to it, `ρ` is a reparametrisation of the
  reduced representative of Remark 2.7, whose image lies in the image of the loop, so `ρ` lies in
  `A`, is homotopic to the loop in `A` (Lemma 2.8 again), and is null-homologous in `A`
  (`fromPath_mem_commutator_of_isZeroFormCut`, any space).
* **Lemma 3.4** (`not_isHomologous_of_disjoint`), by the two-line proof of `notes/checks/A.md`,
  item 7 (A-3.4-5), with no reducedness hypothesis: if `α`, `β` are loops with disjoint images and
  `[α]_h ≠ 0`, then `α`, `β` are not homologous. A connecting path `q` from `x₀` to `x₁` is cut at
  its last parameter `s₀` in `range α`; `Y = range α ∪ q([s₀, 1]) ∪ range β` retracts onto
  `range α` by the map that is the identity on `range α` and constant `q(s₀)` on the rest
  (pasting lemma on two closed sets meeting in `{q(s₀)}`); Lemma 3.3 for `Y` and functoriality of
  the abelianisation finish. The retraction is taken with values in `X` (it need not land in
  a subtype). No arc (injective path) is needed. The paper's symmetric form ("if at least one of
  them is not null-homologous") is `not_isHomologous_of_disjoint_of_or`.
* **Lemma 6.3** (`exists_earringMap_not_mem_commutator`), corrected per `notes/checks/D.md`:
  for `x ∈ w(X)` there is `f : 𝔼 → X` based at `x` with `[f ∘ ℓₙ]_h ≠ 0` for all `n`. Instead of
  path-connected neighbourhoods (which the paper's proof uses), each essential loop `δ` at `x` in
  the ball `B(x, 1/(n+1))` is replaced inside its own image `K` (compact, path-connected, closed,
  one-dimensional) by a conjugate `η γ η⁻¹` of a loop `γ` once around a simple closed curve
  `c : ℝ/ℤ → K` (`exists_simpleClosedCurve`), `η` a path in `K`; the loops are glued with
  `earringMap`. `[γ]_h ≠ 0` because `γ` lives in `range c ≅ ℝ/ℤ` (a continuous injection of a
  compact space into a Hausdorff space is an embedding), where its class has winding number `1`
  and the winding number kills commutators; Lemma 3.3 transports this to `X`, and conjugation does
  not change membership in the commutator subgroup (`conj_mem_commutator_iff`). Neither
  `ηₙ` being injective nor the truncation at the first hit of the curve is needed. The map is
  fully essential (`exists_earringMap_not_mem_commutator_fullyEssential`). Local
  path-connectedness is not used in this construction (only through `eda_zeroForm`, whose
  hypotheses are those of a Peano continuum).

Cited axioms used: `exists_reduced_homotopy` and `isReparam_of_reduced_homotopic` (Lemma 2.8 and
everything after it), `eda_zeroForm` (Lemma 3.3 onwards), `exists_simpleClosedCurve` (Lemma 6.3).
-/

@[expose] public section

open Set Filter Topology unitInterval

noncomputable section

namespace Peano

/-! ### Covering dimension of closed subspaces -/

/-- Covering dimension does not increase on closed subspaces. -/
theorem CoveringDimLE.subtype_of_isClosed {n : ℕ} {X : Type*} [TopologicalSpace X]
    (hX : CoveringDimLE n X) {s : Set X} (hs : IsClosed s) : CoveringDimLE n s := by
  intro ι _ U hU hcov
  rcases isEmpty_or_nonempty s with hse | hsne
  · refine ⟨Empty, inferInstance, fun _ => ∅, fun j => j.elim, ?_, fun j => j.elim,
      fun x => (IsEmpty.false x).elim⟩
    ext x
    exact (IsEmpty.false x).elim
  have hι : Nonempty ι := by
    obtain ⟨x⟩ := hsne
    obtain ⟨i, -⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ x : x ∈ ⋃ i, U i)
    exact ⟨i⟩
  choose U' hU'o hU' using fun i => isOpen_induced_iff.1 (hU i)
  let V : Option ι → Set X := fun o => o.elim sᶜ U'
  have hVo : ∀ o, IsOpen (V o) := by
    rintro (_ | i)
    exacts [hs.isOpen_compl, hU'o i]
  have hVcov : (⋃ o, V o) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    by_cases hx : x ∈ s
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov.symm ▸ mem_univ (⟨x, hx⟩ : s) :
        (⟨x, hx⟩ : s) ∈ ⋃ i, U i)
      rw [← hU' i] at hi
      exact ⟨some i, hi⟩
    · exact ⟨none, hx⟩
  obtain ⟨κ, hκ, W, hWo, hWcov, hWref, hWord⟩ := hX (Option ι) V hVo hVcov
  refine ⟨κ, hκ, fun j => Subtype.val ⁻¹' W j, fun j => (hWo j).preimage continuous_subtype_val,
    ?_, fun j => ?_, fun x => hWord x⟩
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hWcov.symm ▸ mem_univ (x : X) : (x : X) ∈ ⋃ j, W j)
    exact ⟨j, hj⟩
  · obtain ⟨o, ho⟩ := hWref j
    rcases o with _ | i
    · obtain ⟨i⟩ := hι
      exact ⟨i, fun y hy => absurd y.2 (ho hy)⟩
    · exact ⟨i, fun y hy => hU' i ▸ ho hy⟩

/-! ### Lemma 2.8 -/

/-- **Lemma 2.8** (null-homotopy version): in a one-dimensional metric space `X`, a loop in a
subset `A` that is null-homotopic in `X` is null-homotopic in `A`. -/
theorem homotopic_refl_of_map_val (X : Type) [MetricSpace X] (hX : CoveringDimLE 1 X)
    (A : Set X) {a : A} (γ : Path a a)
    (h : (γ.map continuous_subtype_val).Homotopic (Path.refl (a : X))) :
    γ.Homotopic (Path.refl a) := by
  obtain ⟨H⟩ := h
  set K : Set X := range H with hK
  have hKc : IsCompact K := isCompact_range H.continuous
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : PathConnectedSpace K :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_range H.continuous)
  have hK1 : CoveringDimLE 1 K := hX.subtype_of_isClosed hKc.isClosed
  have hmem : ∀ t, (γ.map continuous_subtype_val) t ∈ K := fun t => ⟨(0, t), by simp⟩
  set γK := pathIn (γ.map continuous_subtype_val) K hmem with hγK
  -- `γK` is null-homotopic in `K`, through `H` itself
  have hγK : γK.Homotopic (Path.refl _) :=
    homotopic_of_map_mem H (fun t => (H.apply_zero t).trans rfl) (fun t => by simp)
      (fun s => by simp) (fun s => by simp) (fun z => ⟨z, rfl⟩)
  -- Remark 2.7 in `K`
  obtain ⟨β, hβ, H', hH'⟩ := exists_reduced_homotopy K hK1 γK
  have hβr : β.Homotopic (Path.refl _) := (Path.Homotopic.symm ⟨H'⟩).trans hγK
  obtain ⟨φ, -, hφ⟩ := isReparam_of_reduced_homotopic K hK1 hβ (Or.inl fun _ => rfl) hβr
  have hβeq : β = Path.refl _ := by
    ext t
    exact congrArg Subtype.val (hφ t)
  subst hβeq
  -- the homotopy `H'` lies in the image of `γK`, hence in `A`
  refine homotopic_of_map_mem ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp
    (H' : C(I × I, K))) (fun t => (congrArg Subtype.val (H'.apply_zero t)).trans rfl)
    (fun t => by simp) (fun s => by simp)
    (fun s => by simp) (fun z => ?_)
  obtain ⟨t, ht⟩ := hH' ⟨z, rfl⟩
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ← ht]
  exact (γ t).2

/-- **Lemma 2.8**: in a one-dimensional metric space, the inclusion of any subset is
π₁-injective at every base point. -/
theorem fundamentalGroup_map_val_injective (X : Type) [MetricSpace X] (hX : CoveringDimLE 1 X)
    (A : Set X) (a : A) :
    Function.Injective (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ a) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
  have hγg : FundamentalGroup.fromPath ⟦γ⟧ = g := by rw [hγ]
  rw [← hγg, fundamentalGroup_map_fromPath] at hg
  rw [← hγg]
  exact (fundamentalGroup_fromPath_eq_iff _ _).2
    (homotopic_refl_of_map_val X hX A γ ((fundamentalGroup_fromPath_eq_iff _ _).1 hg))

/-- Lemma 2.8, two-loop form: loops in `A` that are homotopic in `X` are homotopic in `A`. -/
theorem homotopic_of_map_val_homotopic (X : Type) [MetricSpace X] (hX : CoveringDimLE 1 X)
    (A : Set X) {a : A} {γ δ : Path a a}
    (h : (γ.map continuous_subtype_val).Homotopic (δ.map continuous_subtype_val)) :
    γ.Homotopic δ :=
  homotopic_of_map_homotopic (f := ⟨Subtype.val, continuous_subtype_val⟩)
    (fundamentalGroup_map_val_injective X hX A a) h

/-! ### Lemma 3.3 -/

/-- **Lemma 3.3** (loop form): in a one-dimensional Peano continuum `X`, a loop in any subset `A`
whose class in `X` is null-homologous (lies in the commutator subgroup of `π₁(X, a)`) is
null-homologous in `A`. The paper states Lemma 3.3 for any one-dimensional metrizable space; the
restriction to Peano continua (and to `X : Type`) is the scope of the axiom `eda_zeroForm`. -/
theorem fromPath_mem_commutator_of_map_val (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (A : Set X)
    {a : A} (γ : Path a a)
    (h : FundamentalGroup.fromPath ⟦γ.map continuous_subtype_val⟧ ∈
      commutator (FundamentalGroup X a)) :
    FundamentalGroup.fromPath ⟦γ⟧ ∈ commutator (FundamentalGroup A a) := by
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  by_cases hγ : γ.Homotopic (Path.refl a)
  · rw [(fundamentalGroup_fromPath_eq_iff _ _).2 hγ]
    exact Subgroup.one_mem _
  set α := γ.map continuous_subtype_val with hα_def
  have hα : ¬ α.Homotopic (Path.refl (a : X)) := fun h => hγ (homotopic_refl_of_map_val X hX A γ h)
  obtain ⟨ρ, hρred, hρα, hρ0⟩ := eda_zeroForm X hX α hα h
  obtain ⟨β, hβred, H, hH⟩ := exists_reduced_homotopy X hX α
  obtain ⟨φ, -, hφ⟩ := isReparam_of_reduced_homotopic X hX hρred hβred (hρα.trans ⟨H⟩)
  have hρA : ∀ t, ρ t ∈ A := by
    intro t
    have hmem : β (φ t) ∈ range H := ⟨(1, φ t), by simp⟩
    obtain ⟨s, hs⟩ := hH hmem
    rw [show ρ t = β (φ t) from hφ t, ← hs]
    exact (γ s).2
  have h1 : (pathIn ρ A hρA).Homotopic γ :=
    homotopic_of_map_val_homotopic X hX A (by rw [pathIn_map_val]; exact hρα)
  have h2 := fromPath_mem_commutator_of_isZeroFormCut (pathIn ρ A hρA)
    (IsZeroFormCut.of_comp (f := ⟨Subtype.val, continuous_subtype_val⟩) Subtype.val_injective hρ0)
  rwa [(fundamentalGroup_fromPath_eq_iff _ _).2 h1] at h2

/-- **Lemma 3.3**: in a one-dimensional Peano continuum `X`, for every subset `A` and `a ∈ A`, the
map `π₁(A, a)^ab → π₁(X, a)^ab` induced by the inclusion is injective. For path-connected `A`
this is injectivity of `H₁(A) → H₁(X)` (Hurewicz); for `A` with several path components it covers
the summand of `H₁(A)` of the component of `a` only; the general case (finding A-3.3-1) is
`fromPath_mem_commutator_of_sum_eq_zero` (`Peano.Lemma3_3General`). The paper states Lemma 3.3 for
any one-dimensional metrizable space; the restriction to Peano continua (and to `X : Type`) is the
scope of the axiom `eda_zeroForm`. -/
theorem abelianization_map_val_injective (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (A : Set X)
    (a : A) :
    Function.Injective
      (Abelianization.map (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ a)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨g, rfl⟩ : ∃ g, Abelianization.of g = z := by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective z
    exact ⟨g, hg⟩
  rw [Abelianization.map_of, ← mem_commutator_iff_abelianization_of_eq_one] at hz
  rw [← mem_commutator_iff_abelianization_of_eq_one]
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep (FundamentalGroup.toPath g)
  have hγg : FundamentalGroup.fromPath ⟦γ⟧ = g := by rw [hγ]
  rw [← hγg, fundamentalGroup_map_fromPath] at hz
  rw [← hγg]
  exact fromPath_mem_commutator_of_map_val X hX A γ hz

/-! ### Lemma 3.4 -/

/-- **Lemma 3.4** (two-line proof of `notes/checks/A.md`, A-3.4-5; no reducedness needed): in a
one-dimensional Peano continuum, if loops `α` at `x₀` and `β` at `x₁` have disjoint images and
`α` is not null-homologous, then `α` and `β` are not homologous. The paper states Lemma 3.4 for
reduced loops in a one-dimensional path-connected metrizable space; reducedness is not needed, and
the restriction to Peano continua (and to `X : Type`) comes from Lemma 3.3, i.e. from the scope of
the axiom `eda_zeroForm`. -/
theorem not_isHomologous_of_disjoint (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x₀ x₁ : X}
    (α : Path x₀ x₀) (β : Path x₁ x₁) (hd : Disjoint (range α) (range β))
    (hα : FundamentalGroup.fromPath ⟦α⟧ ∉ commutator (FundamentalGroup X x₀)) :
    ¬ IsHomologous α β := by
  classical
  intro hhom
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  set q : Path x₀ x₁ := PathConnectedSpace.somePath x₀ x₁
  have hαc : IsClosed (range α) := (isCompact_range α.continuous).isClosed
  -- the last exit `s₀` of `q` from `range α`
  set T : Set I := q ⁻¹' range α with hT
  have hT0 : (0 : I) ∈ T := ⟨0, by simp⟩
  set s₀ : I := sSup T
  have hs₀ : s₀ ∈ T := (hαc.preimage q.continuous).csSup_mem ⟨0, hT0⟩ (OrderTop.bddAbove T)
  have hafter : ∀ t, s₀ < t → q t ∉ range α := fun t ht hmem =>
    not_le.2 ht (le_csSup (OrderTop.bddAbove T) hmem)
  obtain ⟨u, hu⟩ := hs₀
  -- the space `Y = range α ∪ C`, `C = q([s₀, 1]) ∪ range β`, with `range α ∩ C = {q s₀}`
  set C : Set X := q '' Icc s₀ 1 ∪ range β with hC
  set Y : Set X := range α ∪ C with hY
  have hCc : IsClosed C :=
    ((isCompact_Icc.image q.continuous).union (isCompact_range β.continuous)).isClosed
  have hαC : ∀ y ∈ C, y ∈ range α → y = q s₀ := by
    rintro y (⟨t, ht, rfl⟩ | hyβ) hyα
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [h]
      · exact absurd hyα (hafter t h)
    · exact absurd hyβ (disjoint_left.1 hd hyα)
  -- a path from `x₀` to `x₁` inside `Y`
  set p' : Path x₀ x₁ := ((α.subpath 0 u).trans ((q.subpath s₀ 1).cast hu rfl)).cast
    α.source.symm q.target.symm with hp'
  have hp'Y : ∀ t, p' t ∈ Y := by
    have : range p' ⊆ Y := by
      rw [hp', Path.cast_coe, Path.trans_range, Path.cast_coe, Path.range_subpath,
        Path.range_subpath, uIcc_of_le (le_one' : s₀ ≤ 1)]
      exact union_subset ((image_subset_range _ _).trans subset_union_left)
        (subset_union_left.trans subset_union_right)
    exact fun t => this ⟨t, rfl⟩
  set αY := pathIn α Y (fun t => mem_union_left _ (mem_range_self t))
  set βY := pathIn β Y (fun t => mem_union_right _ (mem_union_right _ (mem_range_self t)))
  set pY := pathIn p' Y hp'Y
  set LY := αY.trans ((pY.trans βY.symm).trans pY.symm)
  -- the loop `α · (p' β⁻¹ p'⁻¹)` is null-homologous in `X`, hence in `Y` (Lemma 3.3)
  have hLX : FundamentalGroup.fromPath ⟦LY.map continuous_subtype_val⟧ ∈
      commutator (FundamentalGroup X x₀) := by
    have hmap : LY.map continuous_subtype_val = α.trans ((p'.trans β.symm).trans p'.symm) := by
      simp only [LY, Path.map_trans, ← Path.map_symm]
      rfl
    rw [hmap, mem_commutator_iff_abelianization_of_eq_one]
    have hR : Path.Homotopic.Quotient.mk ((p'.trans β.symm).trans p'.symm) =
        (Path.Homotopic.Quotient.mk ((p'.trans β).trans p'.symm)).symm := by
      rw [← Path.Homotopic.Quotient.mk_symm, Path.trans_symm, Path.trans_symm, Path.symm_symm]
      simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
    show Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (α.trans ((p'.trans β.symm).trans p'.symm)))) = 1
    rw [Path.Homotopic.Quotient.mk_trans, hR, fundamentalGroup_fromPath_trans,
      fundamentalGroup_fromPath_symm, map_mul, map_inv]
    have h := hhom.forall p'
    exact (congrArg (· * _) (congrArg (·⁻¹) h.symm)).trans (inv_mul_cancel _)
  have hLY := fromPath_mem_commutator_of_map_val X hX Y LY hLX
  -- the retraction of `Y` onto `range α`, with values in `X`
  let rX : X → X := fun y => if y ∈ range α then y else q s₀
  have hrc : ContinuousOn rX Y := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ hαc hCc
    · exact continuousOn_id.congr (fun y hy => by simp only [rX, hy, ↓reduceIte, id])
    · refine (continuousOn_const (c := q s₀)).congr (fun y hy => ?_)
      by_cases h : y ∈ range α
      · simp only [rX, hαC y hy h, ite_self]
      · simp only [rX, h, ↓reduceIte]
  let r : C(Y, X) := ⟨Y.domRestrict rX, hrc.domRestrict⟩
  have hr := monoidHom_map_mem_commutator (FundamentalGroup.map r _) hLY
  rw [fundamentalGroup_map_fromPath] at hr
  have hx₁ : x₁ ∉ range α := fun h => disjoint_left.1 hd h ⟨0, β.source⟩
  have hβr : βY.map r.continuous = Path.refl _ := by
    ext t
    show rX (β t) = rX x₁
    simp only [rX, disjoint_right.1 hd (mem_range_self t), hx₁, ↓reduceIte]
  have hsplit : LY.map r.continuous = (αY.map r.continuous).trans
      (((pY.map r.continuous).trans (βY.map r.continuous).symm).trans
        (pY.map r.continuous).symm) := by
    simp only [LY, Path.map_trans, ← Path.map_symm]
  have hconj : ∀ {a b : X} (P : Path a b) (A : Path a a),
      Path.Homotopic.Quotient.mk (A.trans ((P.trans (Path.refl b).symm).trans P.symm)) =
        Path.Homotopic.Quotient.mk A := by
    intro a b P A
    simp only [Path.refl_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.trans_symm]
  rw [hsplit, hβr] at hr
  change FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _) ∈ _ at hr
  rw [hconj] at hr
  exact hα ((fromPath_mem_commutator_congr _ α
    (fun t => show rX (α t) = α t by simp only [rX, mem_range_self, ↓reduceIte])).1 hr)

/-- **Lemma 3.4**, as stated in the paper ("if at least one of them is not null-homologous"):
loops with disjoint images, one of which is not null-homologous, are not homologous. -/
theorem not_isHomologous_of_disjoint_of_or (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x₀ x₁ : X}
    (α : Path x₀ x₀) (β : Path x₁ x₁) (hd : Disjoint (range α) (range β))
    (h : FundamentalGroup.fromPath ⟦α⟧ ∉ commutator (FundamentalGroup X x₀) ∨
      FundamentalGroup.fromPath ⟦β⟧ ∉ commutator (FundamentalGroup X x₁)) :
    ¬ IsHomologous α β := by
  rcases h with hα | hβ
  · exact not_isHomologous_of_disjoint X hX α β hd hα
  · exact fun hαβ => not_isHomologous_of_disjoint X hX β α hd.symm hβ (IsHomologous.symm hαβ)

/-! ### Lemma 6.3 -/

/-- The standard loop around `ℝ/ℤ` is not null-homologous: its winding number is `1`, while the
winding number, a homomorphism to the abelian group `ℤ`, vanishes on commutators. -/
theorem circleLoop_not_mem_commutator :
    FundamentalGroup.fromPath ⟦unitAddCircleLoop⟧ ∉
      commutator (FundamentalGroup (AddCircle (1 : ℝ)) ((0 : ℝ) : AddCircle (1 : ℝ))) := by
  intro h
  have hw := monoidHom_map_mem_commutator
    (AddCircle.windingNumberIso ((0 : ℝ) : AddCircle (1 : ℝ))).toMonoidHom h
  rw [mem_commutator_iff_abelianization_of_eq_one] at hw
  have h0 := congrArg (Abelianization.lift (MonoidHom.id (Multiplicative ℤ))) hw
  simp only [Abelianization.lift_apply_of, MonoidHom.id_apply, map_one,
    MulEquiv.coe_toMonoidHom] at h0
  have h0' : AddCircle.windingNumberIso ((0 : ℝ) : AddCircle (1 : ℝ))
      (.of (.mk (AddCircle.zsmulLoop 1 0 1))) = 1 := h0
  have h1 := AddCircle.windingNumber_zsmulLoop (p := 1) 0 1
  unfold AddCircle.windingNumber at h1
  rw [h0'] at h1
  simp at h1

/-- A loop once around a simple closed curve `c : ℝ/ℤ → X` in a one-dimensional Peano continuum
is not null-homologous in `X`: it is not null-homologous in `range c ≅ ℝ/ℤ`, and Lemma 3.3
applies. -/
theorem fromPath_map_circleLoop_not_mem_commutator (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X)
    (c : C(AddCircle (1 : ℝ), X)) (hc : Function.Injective c) :
    FundamentalGroup.fromPath ⟦unitAddCircleLoop.map c.continuous⟧ ∉
      commutator (FundamentalGroup X (c ((0 : ℝ) : AddCircle (1 : ℝ)))) := by
  intro h
  have hemb : IsEmbedding c := (c.continuous.isClosedEmbedding hc).isEmbedding
  set e := hemb.toHomeomorph
  set γA := unitAddCircleLoop.map e.continuous
  have h1 : FundamentalGroup.fromPath ⟦γA.map continuous_subtype_val⟧ ∈
      commutator (FundamentalGroup X (e ((0 : ℝ) : AddCircle (1 : ℝ)) : X)) :=
    (fromPath_mem_commutator_congr (γA.map continuous_subtype_val)
      (unitAddCircleLoop.map c.continuous) (fun t => rfl)).2 h
  have h2 := fromPath_mem_commutator_of_map_val X hX (range c) γA h1
  have h3 := monoidHom_map_mem_commutator
    (FundamentalGroup.map (e.symm : C(range c, AddCircle (1 : ℝ))) _) h2
  rw [fundamentalGroup_map_fromPath] at h3
  exact circleLoop_not_mem_commutator ((fromPath_mem_commutator_congr _ unitAddCircleLoop
    (fun t => by simp [γA])).1 h3)

/-- The core of Lemma 6.3: an essential loop `δ` at `x` in a one-dimensional Peano continuum can
be replaced by a loop at `x` inside `range δ` that is not null-homologous, namely a conjugate of
a loop once around a simple closed curve in `range δ`. -/
theorem exists_loop_not_mem_commutator (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x : X}
    (δ : Path x x) (hδ : ¬ δ.Homotopic (Path.refl x)) :
    ∃ ℓ : Path x x, range ℓ ⊆ range δ ∧
      FundamentalGroup.fromPath ⟦ℓ⟧ ∉ commutator (FundamentalGroup X x) := by
  set K := range δ
  have hKc : IsCompact K := isCompact_range δ.continuous
  have : PathConnectedSpace K :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_range δ.continuous)
  have hK1 : CoveringDimLE 1 K := hX.subtype_of_isClosed hKc.isClosed
  set δK := pathIn δ K (fun t => mem_range_self t)
  have hδK : ¬ δK.Homotopic (Path.refl _) := by
    refine not_homotopic_refl_of_map ⟨Subtype.val, continuous_subtype_val⟩ ?_
    change ¬ (δK.map continuous_subtype_val).Homotopic (Path.refl x)
    rwa [pathIn_map_val]
  obtain ⟨c, hc⟩ := exists_simpleClosedCurve K hK1 δK hδK
  set c' : C(AddCircle (1 : ℝ), X) := (ContinuousMap.mk Subtype.val continuous_subtype_val).comp c
  have hc' : Function.Injective c' := Subtype.val_injective.comp hc
  set η₀ := PathConnectedSpace.somePath (⟨x, ⟨0, δ.source⟩⟩ : K)
    (c ((0 : ℝ) : AddCircle (1 : ℝ)))
  set η : Path x (c' ((0 : ℝ) : AddCircle (1 : ℝ))) := η₀.map continuous_subtype_val
  refine ⟨(η.trans (unitAddCircleLoop.map c'.continuous)).trans η.symm, ?_, ?_⟩
  · have hη : range η ⊆ K := by
      rintro _ ⟨t, rfl⟩
      exact (η₀ t).2
    have hγ : range (unitAddCircleLoop.map c'.continuous) ⊆ K := by
      rintro _ ⟨t, rfl⟩
      exact (c (unitAddCircleLoop t)).2
    rw [Path.trans_range, Path.trans_range, Path.symm_range]
    exact union_subset (union_subset hη hγ) hη
  · rw [conj_mem_commutator_iff]
    exact fromPath_map_circleLoop_not_mem_commutator X hX c' hc'

/-- **Lemma 6.3** (corrected per `notes/checks/D.md`): for a one-dimensional Peano continuum `X`
and a wild point `x ∈ w(X)` there is a map `f : 𝔼 → X` from the earring with `f b₀ = x` such
that no loop `f ∘ ℓₙ` is null-homologous. The paper states Lemma 6.3 for any one-dimensional
metrizable space; the restriction to Peano continua (and to `X : Type`) comes from Lemma 3.3, i.e.
from the scope of the axiom `eda_zeroForm`. -/
theorem exists_earringMap_not_mem_commutator (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) {x : X}
    (hx : x ∈ wildSet X) :
    ∃ f : C(earring, X), f earringBase = x ∧ ∀ n,
      FundamentalGroup.fromPath ⟦(earringLoop n).map f.continuous⟧ ∉
        commutator (FundamentalGroup X (f earringBase)) := by
  rw [wildSet_eq_loopWildSet X] at hx
  have key : ∀ n : ℕ, ∃ ℓ : Path x x, range ℓ ⊆ Metric.ball x (1 / ((n : ℝ) + 1)) ∧
      FundamentalGroup.fromPath ⟦ℓ⟧ ∉ commutator (FundamentalGroup X x) := by
    intro n
    obtain ⟨δ, hδU, hδ⟩ := hx _ (Metric.ball_mem_nhds x (by positivity : (0 : ℝ) < 1 / (n + 1)))
    obtain ⟨ℓ, hℓδ, hℓ⟩ := exists_loop_not_mem_commutator X hX δ hδ
    exact ⟨ℓ, hℓδ.trans hδU, hℓ⟩
  choose ℓ hℓU hℓ using key
  have hshrink : ∀ U ∈ 𝓝 x, ∀ᶠ k in atTop, range (ℓ k) ⊆ U := by
    intro U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with k hk
    refine (hℓU k).trans ((Metric.ball_subset_ball ?_).trans hball)
    calc 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by gcongr
      _ ≤ ε := hN.le
  refine ⟨earringMap x ℓ hshrink, earringMap_base hshrink, fun n h => hℓ n ?_⟩
  rw [earringLoop_map_earringMap] at h
  exact (fromPath_mem_commutator_congr ((ℓ n).cast (earringMap_base hshrink)
    (earringMap_base hshrink)) (ℓ n) (fun t => rfl)).1 h

/-- The map of Lemma 6.3 is fully essential (a loop that is not null-homologous is
essential). -/
theorem exists_earringMap_not_mem_commutator_fullyEssential (X : Type) [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X)
    {x : X} (hx : x ∈ wildSet X) :
    ∃ f : C(earring, X), f earringBase = x ∧ FullyEssential f ∧ ∀ n,
      FundamentalGroup.fromPath ⟦(earringLoop n).map f.continuous⟧ ∉
        commutator (FundamentalGroup X (f earringBase)) := by
  obtain ⟨f, hfx, hf⟩ := exists_earringMap_not_mem_commutator X hX hx
  refine ⟨f, hfx, fun n hn => hf n ?_, hf⟩
  rw [(fundamentalGroup_fromPath_eq_iff _ _).2 hn]
  exact Subgroup.one_mem _

end Peano
