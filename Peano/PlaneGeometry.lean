module

public import Peano.Earring
public import Peano.LocJoin

/-!
# Plane geometry of the earring circles

Elementary facts about the circles `Cₖ = earringCircle k` of the infinite earring and their
parametrisations `earringParam k`, and a radial-retraction lemma for planar circles. They are
used both by the planar models of `Peano.Models` (whose attached earrings are similar copies of
`Peano.earring`) and by the examples of `Peano.Sanity`.

* **Radii.** `rₖ = earringRadius k ≤ 1` (`earringRadius_le_one`), and only finitely many
  `rₖ ≥ ε` (`finite_le_earringRadius`).
* **Parametrisation.** `earringParam k` is continuous, `1`-periodic, injective modulo `1` and
  traces exactly `Cₖ` (`range_earringParam`).
* **Circles.** `Cₖ` is compact, has empty interior in `ℝ²` and is locally joinable everywhere
  (`locJoin_earringCircle`, in the sense of `Peano.LocJoin`); the earring is the base point
  together with its circles and is locally joinable everywhere (`locJoin_earring`).
* **Radial retraction.** A convex set `W` avoiding the centre `c` of a circle of radius `ρ`
  contained in `M`, and meeting `M` only on that circle, carries no essential loop of `M`
  (`homotopic_refl_of_radial_retraction`): radial projection from `c` is a retraction. Points
  of a sup-metric ball of radius `ρ / 2` about a point of the circle avoid `c`
  (`sq_add_sq_pos_of_dist_lt`).

## Main statements

`range_earringParam`, `earringParam_eq_earringParam`, `locJoin_earringCircle`,
`interior_earringCircle`, `locJoin_earring`, `homotopic_refl_of_radial_retraction`.

## Design choices

* Circles are given by their equations `(y₁ - c₁)² + (y₂ - c₂)² = ρ²`, never by `Metric.sphere`
  (the metric on `ℝ × ℝ` is the sup metric); distances in proofs are sup distances.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace Peano

/-! ### Radii and parametrisations of the earring circles -/

/-- `rₖ ≤ 1`. -/
lemma earringRadius_le_one (k : ℕ) : earringRadius k ≤ 1 := by
  unfold earringRadius
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ k := k.cast_nonneg
  linarith

/-- `rₖ ≥ ε` only for finitely many `k`. -/
lemma finite_le_earringRadius {ε : ℝ} (hε : 0 < ε) : {k | ε ≤ earringRadius k}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine (Set.finite_lt_nat N).subset fun k hk => ?_
  simp only [mem_ofPred_eq, earringRadius] at hk ⊢
  by_contra! h
  have hk1 : (N : ℝ) + 1 ≤ k + 1 := by exact_mod_cast Nat.succ_le_succ h
  rw [le_div_iff₀ (by positivity)] at hk
  rw [div_lt_iff₀ hε] at hN
  nlinarith

/-- The parametrisation `earringParam k` traces exactly the circle `Cₖ`. -/
theorem range_earringParam (k : ℕ) : range (earringParam k) = earringCircle k := by
  refine subset_antisymm ?_ fun p hp => ?_
  · rintro _ ⟨t, rfl⟩
    exact earringParam_mem_earringCircle k t
  · obtain ⟨t, -, ht⟩ := exists_earringParam_eq hp
    exact ⟨t, ht⟩

/-- `earringParam k` is `1`-periodic. -/
theorem earringParam_periodic (k : ℕ) : Function.Periodic (earringParam k) 1 := by
  intro t
  simp only [earringParam, mul_add, mul_one, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- `earringParam k` is injective modulo `1`. -/
theorem earringParam_eq_earringParam {k : ℕ} {t t' : ℝ}
    (h : earringParam k t = earringParam k t') : ∃ n : ℤ, t = t' + n := by
  have hr := earringRadius_pos k
  have hc : Real.cos (2 * Real.pi * t) = Real.cos (2 * Real.pi * t') := by
    have := congrArg Prod.fst h
    simp only [earringParam] at this
    have : earringRadius k * (Real.cos (2 * Real.pi * t') - Real.cos (2 * Real.pi * t)) = 0 := by
      linarith
    have := (mul_eq_zero.1 this).resolve_left hr.ne'
    linarith
  have hsn : Real.sin (2 * Real.pi * t) = Real.sin (2 * Real.pi * t') := by
    have := congrArg Prod.snd h
    simp only [earringParam] at this
    exact mul_left_cancel₀ hr.ne' this
  have hcos : Real.cos (2 * Real.pi * t - 2 * Real.pi * t') = 1 := by
    rw [Real.cos_sub, ← hc, ← hsn]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos
  refine ⟨n, ?_⟩
  have := Real.pi_pos
  have : (n : ℝ) * (2 * Real.pi) = (t - t') * (2 * Real.pi) := by rw [hn]; ring
  have := mul_right_cancel₀ (by positivity) this
  linarith

/-- The parametrisation `earringParam k` is continuous. -/
@[fun_prop] theorem continuous_earringParam (k : ℕ) : Continuous (earringParam k) := by
  unfold earringParam; fun_prop

/-! ### The circles and the earring -/

/-- Each circle `Cₖ` is locally joinable (in the sense of `LocJoin`) at every point. -/
theorem locJoin_earringCircle (k : ℕ) (p : ℝ × ℝ) : LocJoin (earringCircle k) p := by
  refine locJoin_of_isClosed (isClosed_earringCircle k) (fun p hp => ?_) p
  rw [← range_earringParam] at hp ⊢
  obtain ⟨t, rfl⟩ := hp
  exact locJoin_range_of_periodic (continuous_earringParam k) (earringParam_periodic k)
    (fun _ _ h => earringParam_eq_earringParam h) t

/-- Each circle `Cₖ` is compact. -/
theorem isCompact_earringCircle (k : ℕ) : IsCompact (earringCircle k) :=
  isCompact_earring.of_isClosed_subset (isClosed_earringCircle k) fun _ hp => mem_iUnion.2 ⟨k, hp⟩

/-- A circle `Cₖ` has empty interior in `ℝ²`. -/
theorem interior_earringCircle (k : ℕ) : interior (earringCircle k) = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  have hmem : ∀ η, |η| < δ → (y.1, y.2 + η) ∈ earringCircle k := fun η hη => hball <| by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simpa using hη
  have h0 : (y.1, y.2 + 0) ∈ earringCircle k := hmem 0 (by simpa using hδ)
  have h1 := hmem (δ / 2) (by rw [abs_of_pos (half_pos hδ)]; linarith)
  have h2 := hmem (-(δ / 2)) (by rw [abs_neg, abs_of_pos (half_pos hδ)]; linarith)
  simp only [earringCircle, mem_ofPred_eq, add_zero] at h0 h1 h2
  nlinarith

/-- The earring is the base point together with its circles. -/
theorem earring_eq_union : earring = {((0, 0) : ℝ × ℝ)} ∪ ⋃ k, earringCircle k := by
  refine (union_eq_right.2 ?_).symm
  rintro _ rfl
  exact mem_iUnion.2 ⟨0, zero_mem_earringCircle 0⟩

/-- The earring is locally joinable (in the sense of `LocJoin`) at every point. -/
theorem locJoin_earring (p : ℝ × ℝ) : LocJoin earring p := by
  rw [earring_eq_union]
  refine locJoin_union_iUnion_of_shrinking earringCircle (fun _ => ((0, 0) : ℝ × ℝ))
    (locJoin_of_isClosed isClosed_singleton fun q hq => Convex.locJoin (convex_singleton _) hq)
    locJoin_earringCircle (fun _ => rfl) (fun k q hq => ?_) (fun ε hε => ?_) p
  · rw [← range_earringParam] at hq ⊢
    exact (isPathConnected_range (continuous_earringParam k)).joinedIn q hq _
      ⟨0, earringParam_zero k⟩
  · refine (finite_le_earringRadius (half_pos hε)).subset fun k hk => ?_
    simp only [mem_ofPred_eq] at hk ⊢
    by_contra! h
    refine hk fun q hq => ?_
    obtain ⟨t, -, rfl⟩ := exists_earringParam_eq hq
    rw [mem_closedBall]
    linarith [dist_earringParam_le k t]

/-! ### Radial retraction onto a planar circle -/

/-- Points within sup distance `ρ / 2` of a point `x` of the circle of centre `c` and radius `ρ`
are not the centre. -/
lemma sq_add_sq_pos_of_dist_lt {c x y : ℝ × ℝ} {ρ : ℝ}
    (hx : (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 = ρ ^ 2) (hy : dist y x < ρ / 2) :
    0 < (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2 := by
  by_contra! hle
  have e1 : y.1 = c.1 := by nlinarith [sq_nonneg (y.1 - c.1), sq_nonneg (y.2 - c.2)]
  have e2 : y.2 = c.2 := by nlinarith [sq_nonneg (y.1 - c.1), sq_nonneg (y.2 - c.2)]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, e1, e2] at hy
  obtain ⟨h1a, h1b⟩ := abs_lt.1 ((le_max_left _ _).trans_lt hy)
  obtain ⟨h2a, h2b⟩ := abs_lt.1 ((le_max_right _ _).trans_lt hy)
  nlinarith

/-- **Null-homotopy by radial retraction.** Let `W ⊆ ℝ²` be convex and avoid the centre `c` of
the circle of radius `ρ > 0` about `c`; suppose this circle lies in `M` and `M ∩ W` lies on it.
Then every loop in `M` whose image lies in `W` is null-homotopic in `M` (radial projection from
`c` is a retraction `W → M`; `homotopic_refl_of_retraction`). -/
theorem homotopic_refl_of_radial_retraction {M W : Set (ℝ × ℝ)} {c : ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hW : Convex ℝ W) (hc : ∀ y ∈ W, 0 < (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2)
    (hCM : ∀ y : ℝ × ℝ, (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2 = ρ ^ 2 → y ∈ M)
    (hMW : ∀ y ∈ W, y ∈ M → (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2 = ρ ^ 2)
    {x : M} (γ : Path x x) (hγ : ∀ t, (γ t : ℝ × ℝ) ∈ W) : γ.Homotopic (Path.refl x) := by
  let N : ℝ × ℝ → ℝ := fun y => √((y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2)
  have hNc : Continuous N := by fun_prop
  have hN0 : ∀ y ∈ W, N y ≠ 0 := fun y hy => (Real.sqrt_pos.2 (hc y hy)).ne'
  have hN2 : ∀ y, N y ^ 2 = (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2 := fun y =>
    Real.sq_sqrt (by positivity)
  let r : ℝ × ℝ → ℝ × ℝ := fun y =>
    (c.1 + ρ * (y.1 - c.1) / N y, c.2 + ρ * (y.2 - c.2) / N y)
  refine homotopic_refl_of_retraction hW r ?_ ?_ ?_ γ hγ
  · refine ContinuousOn.prodMk ?_ ?_
    · exact continuousOn_const.add ((by fun_prop : Continuous fun y : ℝ × ℝ =>
        ρ * (y.1 - c.1)).continuousOn.div hNc.continuousOn hN0)
    · exact continuousOn_const.add ((by fun_prop : Continuous fun y : ℝ × ℝ =>
        ρ * (y.2 - c.2)).continuousOn.div hNc.continuousOn hN0)
  · intro y hy
    refine hCM _ ?_
    have h0 := hN0 y hy
    have h2 := hN2 y
    simp only [r, add_sub_cancel_left]
    field_simp
    rw [h2]
  · intro y hy hyM
    have hy' := hMW y hy hyM
    have hNy : N y = ρ := by
      simp only [N, hy']
      exact Real.sqrt_sq hρ.le
    simp only [r, hNy]
    ext
    · simp only; field_simp; ring
    · simp only; field_simp; ring

end Peano
