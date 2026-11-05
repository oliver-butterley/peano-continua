module

public import PeanoPartA.Lemmas

/-!
# Lemma 3.3 in full generality: several path components

Brazas–Pavešić (arXiv:2610.35875), Lemma 3.3: for a one-dimensional Peano continuum `X` and
**any** subset `A ⊆ X`, the map `H₁(A) → H₁(X)` induced by the inclusion is injective.
`PeanoPartA.Lemmas` proves this for one summand of `H₁(A)` at a time
(`abelianization_map_val_injective`), i.e. for path-connected `A`; the case of several path
components is finding A-3.3-1 of `notes/checks/A.md`. This file closes that gap. The paper itself
only uses path-connected `A` (Lemma 6.3, `A = Cₙ`).

## Statement without a type `H₁(A)`

The statement with genuine singular homology, injectivity of `H₁(A; ℤ) → H₁(X; ℤ)` as a map, is
`Peano.singularHomologyMap_val_injective` (`PeanoPartA.SingularH1Lemmas`), a corollary of the
statement below: there, every element of `H₁(A; ℤ)` is written as a sum of loop classes over
distinct path components (`Peano.exists_finset_sum_h1Class`), which is the decomposition that the
text below takes for granted.

The proof works in the abelianisation model of `PeanoPartA.Homology`: `H₁` of a path-connected
space is the abelianisation of `π₁` (Hurewicz). `H₁` is additive over path components, `H₁(A) = ⊕_c
H₁(A_c)`, so an element
of `H₁(A)` is a finite sum `Σᵢ [αᵢ]_h` of classes of loops `αᵢ` at points `aᵢ` lying in pairwise
distinct path components of `A`, and it is zero iff every `[αᵢ]_h` is zero in `H₁(A_{c(i)})`.
Injectivity of `H₁(A) → H₁(X)` is therefore exactly the statement
`fromPath_mem_commutator_of_sum_eq_zero`:

> for finitely many loops `αᵢ` in `A` at points `aᵢ` in pairwise distinct path components of `A`,
> if `Σᵢ [αᵢ]_h = 0` in `H₁(X)`, then every `αᵢ` is null-homologous in `A`
> (`fromPath ⟦αᵢ⟧ ∈ commutator (FundamentalGroup A aᵢ)`).

The sum is taken in `Additive (Abelianization (FundamentalGroup X x))` for a base point `x`, after
transporting each loop to `x` along a path `pᵢ : x → aᵢ` (`X` is path-connected); by
`abelianization_of_conj_eq` the result does not depend on the paths. `homologyClass x γ`
(`PeanoPartA.Homology`) is this transported class for the paths `PathConnectedSpace.somePath`
(`homologyClass_eq`: any other path gives the same class).

## Proof

Not the arc tree of the review's repair, but an induction that reuses Lemma 3.4
(`not_isHomologous_of_disjoint`), whose proof in `PeanoPartA.Lemmas` is the retraction argument of
the
repair for two components.

* **Reduction to `X`.** Loops in different path components of `A` have disjoint images. By the
  path-connected Lemma 3.3 (`fromPath_mem_commutator_of_map_val`) it suffices to show that each
  loop is null-homologous **in `X`**. So the core statement
  (`homologyClass_eq_zero_of_sum_eq_zero`) is: *finitely many loops in `X` with pairwise disjoint
  images whose classes sum to zero in `H₁(X)` are each null-homologous in `X`.*
* **Induction on the number of loops.** One loop: trivial. At least two loops, `c` one of them:
  take a path `q` from the base point of `ℓ_c` to the base point of another loop and cut it at its
  **first entry** `t₁` into the union `K'` of the images of the loops other than `ℓ_c`
  (closed, a finite union of compacta); `q t₁` lies on some `ℓ_d`. The path
  `p' = q|[0,t₁] · ℓ_d|[v,0]` (from the base point of `ℓ_c` to that of `ℓ_d`) meets the images of
  the other loops `ℓ_j` (`j ≠ c, d`) nowhere: `q t ∉ K'` for `t < t₁`, and `q t₁ ∈ range ℓ_d`,
  disjoint from `range ℓ_j`. The merged loop `L = ℓ_c · p' ℓ_d p'⁻¹` has class
  `[ℓ_c]_h + [ℓ_d]_h` (`homologyClass_trans_conj`) and image disjoint from the remaining loops, so
  replacing `ℓ_c, ℓ_d` by `L` gives a family with one loop fewer and the same sum. By induction
  `[L]_h = 0`, i.e. `ℓ_c` is homologous to `ℓ_d⁻¹`, two loops with disjoint images; Lemma 3.4
  forces `[ℓ_c]_h = 0`, hence `[ℓ_d]_h = 0`; the other loops are covered by the induction.
  No last-exit truncation and no arc (injective path) is needed: disjointness of the merged loop
  from the *remaining* loops is all the induction uses, and Lemma 3.4 needs only disjointness of
  `ℓ_c` and `ℓ_d`.
* **Encoding.** Families of loops at varying base points are `ℓ : ι → Σ y : X, Path y y` with a
  `Finset ι`; the induction replaces `ℓ` by `Function.update ℓ c ⟨_, L⟩` and the index set `s` by
  `s.erase d`, so the index type never changes.

Hypotheses on `X` are those of `PeanoPartA.Lemmas`: a one-dimensional Peano continuum `X : Type`
(compact, connected, locally path-connected metric space of covering dimension `≤ 1`), the scope
of the axiom `eda_zeroForm`; the paper states Lemma 3.3 for any one-dimensional metrizable space.
The statements that mention `homologyClass` take `[PathConnectedSpace X]` in place of
`[ConnectedSpace X]` (equivalent for locally path-connected spaces; it makes `homologyClass`
definable). Axioms: those of Lemma 3.3 and
Lemma 3.4 in `PeanoPartA.Lemmas` (`exists_reduced_homotopy`, `isReparam_of_reduced_homotopic`,
`eda_zeroForm`).
-/

@[expose] public section

open Set Function Topology unitInterval

noncomputable section

namespace Peano

/-! ### Loops in `X` with pairwise disjoint images -/

/-- Inductive form of `homologyClass_eq_zero_of_sum_eq_zero`, by induction on the number `n` of
loops: finitely many loops with pairwise disjoint images in a one-dimensional Peano continuum
whose homology classes sum to zero are each null-homologous. -/
private theorem homologyClass_eq_zero_of_sum_eq_zero_aux (X : Type) [MetricSpace X] [CompactSpace X]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (x : X)
    {ι : Type*} [DecidableEq ι] (n : ℕ) :
    ∀ (ℓ : ι → Σ y : X, Path y y) (s : Finset ι), s.card = n →
      (s : Set ι).Pairwise (Disjoint on fun i => range (ℓ i).2) →
      ∑ i ∈ s, homologyClass x (ℓ i).2 = 0 → ∀ i ∈ s, homologyClass x (ℓ i).2 = 0 := by
  induction n with
  | zero =>
    intro ℓ s hs _ _ i hi
    simp [Finset.card_eq_zero.1 hs] at hi
  | succ n ih =>
    intro ℓ s hs hdisj hsum
    obtain ⟨c, hc⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
    rcases (s.erase c).eq_empty_or_nonempty with he | ⟨d₀, hd₀⟩
    · -- a single loop
      have hsc : s = {c} := by
        ext i
        refine ⟨fun hi => ?_, fun hi => Finset.mem_singleton.1 hi ▸ hc⟩
        by_contra hic
        have : i ∈ s.erase c := Finset.mem_erase.2 ⟨by simpa using hic, hi⟩
        simp [he] at this
      subst hsc
      intro i hi
      rw [Finset.mem_singleton.1 hi]
      simpa using hsum
    -- at least two loops: the union `K'` of the images of the loops other than `ℓ c`
    set K' : Set X := ⋃ j ∈ s.erase c, range (ℓ j).2 with hK'
    have hK'c : IsClosed K' :=
      isClosed_biUnion_finset fun j _ => (isCompact_range (ℓ j).2.continuous).isClosed
    -- a path `q` from the base point of `ℓ c` into `K'`, and its first entry `t₁` into `K'`
    set q : Path (ℓ c).1 (ℓ d₀).1 := PathConnectedSpace.somePath _ _
    set T : Set I := q ⁻¹' K' with hT
    have hT1 : (1 : I) ∈ T := by
      show q 1 ∈ K'
      rw [q.target]
      exact mem_iUnion₂.2 ⟨d₀, hd₀, 0, (ℓ d₀).2.source⟩
    set t₁ : I := sInf T
    have ht₁ : t₁ ∈ T := (hK'c.preimage q.continuous).csInf_mem ⟨1, hT1⟩ (OrderBot.bddBelow T)
    have hbefore : ∀ t, t < t₁ → q t ∉ K' := fun t ht hmem =>
      not_le.2 ht (csInf_le (OrderBot.bddBelow T) hmem)
    obtain ⟨d, hd, v, hv⟩ : ∃ d ∈ s.erase c, ∃ v, (ℓ d).2 v = q t₁ := by
      obtain ⟨d, hd, v, hv⟩ := mem_iUnion₂.1 (show q t₁ ∈ K' from ht₁)
      exact ⟨d, hd, v, hv⟩
    have hdc : d ≠ c := Finset.ne_of_mem_erase hd
    have hds : d ∈ s := Finset.mem_of_mem_erase hd
    -- the connecting path `p' = q|[0, t₁] · (ℓ d)|[v, 0]`
    set p' : Path (ℓ c).1 (ℓ d).1 := ((q.subpath 0 t₁).trans
      (((ℓ d).2.subpath v 0).cast hv.symm (ℓ d).2.source.symm)).cast q.source.symm rfl
    have hp' : range p' ⊆ q '' Icc 0 t₁ ∪ range (ℓ d).2 := by
      rw [Path.cast_coe, Path.trans_range, Path.cast_coe, Path.range_subpath, Path.range_subpath,
        uIcc_of_le (nonneg' : (0 : I) ≤ t₁)]
      exact union_subset_union subset_rfl (image_subset_range _ _)
    -- the merged loop `L = ℓ c · p' (ℓ d) p'⁻¹`
    set L : Path (ℓ c).1 (ℓ c).1 := (ℓ c).2.trans ((p'.trans (ℓ d).2).trans p'.symm)
    have hL : homologyClass x L = homologyClass x (ℓ c).2 + homologyClass x (ℓ d).2 :=
      homologyClass_trans_conj x _ _ _
    have hLdisj : ∀ j ∈ s, j ≠ c → j ≠ d → Disjoint (range L) (range (ℓ j).2) := by
      intro j hj hjc hjd
      have hdj : ∀ y ∈ range (ℓ d).2, y ∉ range (ℓ j).2 := fun y h =>
        disjoint_left.1 (hdisj hds hj (Ne.symm hjd)) h
      have hpj : ∀ y ∈ range p', y ∉ range (ℓ j).2 := by
        intro y hy hyj
        rcases hp' hy with ⟨t, ht, rfl⟩ | hyd
        · rcases eq_or_lt_of_le ht.2 with h | h
          · rw [h] at hyj
            exact hdj _ ⟨v, hv⟩ hyj
          · exact hbefore t h (mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hjc, hj⟩, hyj⟩)
        · exact hdj _ hyd hyj
      rw [disjoint_left]
      intro y hyL hyj
      simp only [L, Path.trans_range, Path.symm_range] at hyL
      rcases hyL with hyc | (hyp | hyd) | hyp
      · exact disjoint_left.1 (hdisj hc hj (Ne.symm hjc)) hyc hyj
      · exact hpj y hyp hyj
      · exact hdj y hyd hyj
      · exact hpj y hyp hyj
    -- the family with `ℓ c, ℓ d` replaced by `L`
    set ℓ' := Function.update ℓ c ⟨(ℓ c).1, L⟩ with hℓ'
    have hℓ'c : ℓ' c = ⟨(ℓ c).1, L⟩ := Function.update_self _ _ _
    have hℓ'j : ∀ j, j ≠ c → ℓ' j = ℓ j := fun j hj => Function.update_of_ne hj _ _
    have hcs' : c ∈ s.erase d := Finset.mem_erase.2 ⟨hdc.symm, hc⟩
    have hcard : (s.erase d).card = n := by
      rw [Finset.card_erase_of_mem hds]
      omega
    have hd' : ((s.erase d : Finset ι) : Set ι).Pairwise (Disjoint on fun i => range (ℓ' i).2) := by
      intro i hi j hj hij
      simp only [Finset.coe_erase, mem_sdiff, Finset.mem_coe, mem_singleton_iff] at hi hj
      show Disjoint (range (ℓ' i).2) (range (ℓ' j).2)
      by_cases hic : i = c
      · subst hic
        rw [hℓ'c, hℓ'j j (Ne.symm hij)]
        exact hLdisj j hj.1 (Ne.symm hij) hj.2
      · by_cases hjc : j = c
        · subst hjc
          rw [hℓ'c, hℓ'j i hic]
          exact (hLdisj i hi.1 hic hi.2).symm
        · rw [hℓ'j i hic, hℓ'j j hjc]
          exact hdisj hi.1 hj.1 hij
    have hsum' : ∑ i ∈ s.erase d, homologyClass x (ℓ' i).2 = 0 := by
      rw [← Finset.add_sum_erase _ _ hcs', hℓ'c,
        Finset.sum_congr rfl (g := fun j => homologyClass x (ℓ j).2)
          (fun j hj => by rw [hℓ'j j (Finset.ne_of_mem_erase hj)])]
      rw [← Finset.add_sum_erase _ _ hds, ← Finset.add_sum_erase _ _ hcs'] at hsum
      rw [hL]
      convert hsum using 1
      abel
    have hIH := ih ℓ' (s.erase d) hcard hd' hsum'
    have hL0 : homologyClass x L = 0 := by
      have := hIH c hcs'
      rw [hℓ'c] at this
      exact this
    -- Lemma 3.4 for `ℓ c` and `(ℓ d)⁻¹`
    have hcd : homologyClass x (ℓ c).2 = homologyClass x (ℓ d).2.symm := by
      rw [homologyClass_symm, eq_neg_iff_add_eq_zero, ← hL, hL0]
    have hc0 : homologyClass x (ℓ c).2 = 0 := by
      rw [homologyClass_eq_zero_iff]
      by_contra hnot
      refine not_isHomologous_of_disjoint X hX (ℓ c).2 (ℓ d).2.symm ?_ hnot
        ((isHomologous_iff_homologyClass_eq x).2 hcd)
      rw [Path.symm_range]
      exact hdisj hc hds (Ne.symm hdc)
    have hd0 : homologyClass x (ℓ d).2 = 0 := by
      rw [hL, hc0, zero_add] at hL0
      exact hL0
    intro i hi
    by_cases hic : i = c
    · subst hic
      exact hc0
    by_cases hid : i = d
    · subst hid
      exact hd0
    have := hIH i (Finset.mem_erase.2 ⟨hid, hi⟩)
    rwa [hℓ'j i hic] at this

/-- **Core of Lemma 3.3**: in a one-dimensional Peano continuum `X`, if finitely many loops
`ℓ i` (`i ∈ s`) have pairwise disjoint images and their homology classes sum to zero in
`H₁(X) ≅ π₁(X, x)^ab`, then each of them is null-homologous. -/
theorem homologyClass_eq_zero_of_sum_eq_zero (X : Type) [MetricSpace X] [CompactSpace X]
    [PathConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (x : X)
    {ι : Type*} (ℓ : ι → Σ y : X, Path y y) (s : Finset ι)
    (hd : (s : Set ι).Pairwise (Disjoint on fun i => range (ℓ i).2))
    (hsum : ∑ i ∈ s, homologyClass x (ℓ i).2 = 0) :
    ∀ i ∈ s, homologyClass x (ℓ i).2 = 0 := by
  classical
  exact homologyClass_eq_zero_of_sum_eq_zero_aux X hX x s.card ℓ s rfl hd hsum

/-! ### Lemma 3.3 for an arbitrary subset -/

/-- **Lemma 3.3** (general form, finding A-3.3-1 of `notes/checks/A.md`): let `X` be a
one-dimensional Peano continuum, `A ⊆ X` any subset, and `αᵢ` (`i : ι`, finite) loops in `A` at
points `aᵢ` lying in pairwise distinct path components of `A`. If the sum of their classes in
`H₁(X) ≅ π₁(X, x)^ab` vanishes, each loop being transported to the base point `x` along a path
`pᵢ : x → aᵢ` in `X`, then every `αᵢ` is null-homologous in `A`. By Hurewicz and additivity of
`H₁` over path components this is injectivity of `H₁(A) → H₁(X)`. -/
theorem fromPath_mem_commutator_of_sum_eq_zero (X : Type) [MetricSpace X] [CompactSpace X]
    [ConnectedSpace X] [LocallyPathConnectedSpace X] (hX : CoveringDimLE 1 X) (A : Set X)
    (x : X) {ι : Type*} [Fintype ι] (a : ι → A) (α : ∀ i, Path (a i) (a i))
    (ha : Pairwise fun i j => ¬ Joined (a i) (a j)) (p : ∀ i, Path x (a i : X))
    (hsum : ∑ i, Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      ⟦((p i).trans ((α i).map continuous_subtype_val)).trans (p i).symm⟧)) = 0) (i : ι) :
    FundamentalGroup.fromPath ⟦α i⟧ ∈ commutator (FundamentalGroup A (a i)) := by
  have : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.2 inferInstance
  set ℓ : ι → Σ y : X, Path y y := fun i => ⟨a i, (α i).map continuous_subtype_val⟩
  have hdisj : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Disjoint on fun i => range (ℓ i).2) := by
    intro i _ j _ hij
    show Disjoint (range ((α i).map continuous_subtype_val))
      (range ((α j).map continuous_subtype_val))
    rw [disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    apply ha hij
    have h1 : Joined (a i) (α i t) := ⟨((α i).subpath 0 t).cast (α i).source.symm rfl⟩
    have h2 : Joined (a j) (α j t') := ⟨((α j).subpath 0 t').cast (α j).source.symm rfl⟩
    rw [show α j t' = α i t from Subtype.ext ht'] at h2
    exact h1.trans h2.symm
  have hsum' : ∑ i ∈ Finset.univ, homologyClass x (ℓ i).2 = 0 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => homologyClass_eq x (p i) _
  have h0 := homologyClass_eq_zero_of_sum_eq_zero X hX x ℓ Finset.univ hdisj hsum' i
    (Finset.mem_univ i)
  rw [homologyClass_eq_zero_iff] at h0
  exact fromPath_mem_commutator_of_map_val X hX A (α i) h0

/-- **Lemma 3.3** (general form) with the transport paths `PathConnectedSpace.somePath`: loops in
`A` at points in pairwise distinct path components of `A` whose homology classes in `X` sum to
zero are each null-homologous in `A`. -/
theorem fromPath_mem_commutator_of_sum_homologyClass_eq_zero (X : Type) [MetricSpace X]
    [CompactSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (hX : CoveringDimLE 1 X) (A : Set X) (x : X) {ι : Type*} [Fintype ι] (a : ι → A)
    (α : ∀ i, Path (a i) (a i)) (ha : Pairwise fun i j => ¬ Joined (a i) (a j))
    (hsum : ∑ i, homologyClass x ((α i).map continuous_subtype_val) = 0) (i : ι) :
    FundamentalGroup.fromPath ⟦α i⟧ ∈ commutator (FundamentalGroup A (a i)) :=
  fromPath_mem_commutator_of_sum_eq_zero X hX A x a α ha
    (fun i => PathConnectedSpace.somePath x (a i)) hsum i

end Peano
