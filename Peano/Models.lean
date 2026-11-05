module

public import Peano.PlaneGeometry
public import Peano.LoopWildSet
public import Peano.Dimension
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas

/-!
# Planar models with a prescribed countable wild set

The surjectivity half of the (corrected) Theorem 1.2 of Brazas–Pavešić (arXiv:2610.35875): for
every non-empty countable compact metric space `K` there is a one-dimensional Peano continuum
`A_K ⊆ ℝ²` whose wild set is a copy of `K`. The paper builds `A_λ` for a compact countable ordinal
`λ` from an order embedding `λ ↪ [0, 1]` and earrings attached along `[0, 1] × {0}`; here any
countable compact metric `K` is used directly (see `notes/checks/D.md`, "Theorem 1.2, proof", for
the gaps this construction fills: the earrings must meet the axis only at their attachment points
and be pairwise disjoint).

## Construction

1. **`K ↪ ℝ`** (`exists_continuous_injective_real`). In a countable metric space all but countably
   many radii give clopen balls; the balls `B(a, ρ_{a,n})` with `ρ_{a,n} ∈ (1/(n+2), 1/(n+1))`
   separate points, and the Cantor function `∑ₘ 3⁻ᵐ 𝟙_{Bₘ}` (Mathlib's `Cardinal.cantorFunction`,
   injective for ratio `< 1/2`) turns them into a continuous injection `u : K → ℝ`. For compact `K`
   this is an embedding, and `|u| ≤ L` for some `L`.
2. **Scales** (`exists_scales`). `sₐ ∈ (0, 1]`, tending to `0`, with `4 sₐ s_b < (uₐ - u_b)²` for
   `a ≠ b`: the condition for the discs of radii `sₐ`, `s_b` tangent to the axis from above at
   `uₐ`, `u_b` to be disjoint (`sq_sub_le_of_mem_discs`).
3. **The model** (`ModelData.model`). `[-L, L] × {0}` together with, for every `a`, the image of
   the earring `𝔼` under the similarity `toPlane a : p ↦ (uₐ - sₐ p₂, sₐ p₁)` (a quarter turn, so
   the earring hangs above the axis, tangent to it at `(uₐ, 0)`). The `k`-th circle of the earring
   at `a` has centre `(uₐ, sₐ rₖ)` and radius `sₐ rₖ`, `rₖ = 1/(k+1)`.

## Properties

* **Compact**: closed (`isClosed_union_iUnion_of_shrinking`: all but finitely many earrings lie in
  any given neighbourhood of the axis) and bounded.
* **Connected**: every point is joined to the axis inside its circle.
* **Locally path-connected**: through the metric notion `LocJoin` of `Peano.LocJoin` (points of a
  set near `p` are joined to `p` by paths in the set that stay near `p`). The segment (convex) and
  every circle (image of a periodic curve injective modulo `1`, `locJoin_range_of_periodic`) have
  it, and a union of a set with shrinking pieces attached keeps it
  (`locJoin_union_iUnion_of_shrinking`).
* **One-dimensional** (`coveringDimLE_model`): the model is rim-finite, so
  `coveringDimLE_one_of_finite_frontier` (`Peano.Dimension`) applies. The tool is the projection
  `proj` onto the axis (the earring at `b` goes to `u_b`), continuous on the model because the
  earrings lie in discs tangent to the axis. A point `x` has the neighbourhoods
  `proj⁻¹ (c₁, c₂) ∩ ball x ρ`, whose frontier lies in `{(c₁, 0), (c₂, 0)}` together with the
  points of the square `sphere x ρ` on the finitely many circles that are not small; each circle
  meets a square in finitely many points. The abscissae `c₁, c₂` are chosen off the countable set
  of attachment abscissae. No axiom is used. (The model also has empty interior in `ℝ²`, by
  Baire: `interior_model`.)
* **Wild points**: the earring at `a` is fully essential, because the model retracts onto it
  (`earringFrom`: the inverse similarity on the earring, the base point elsewhere; continuous by
  gluing two closed sets meeting at the attachment point) and its loops are essential in `𝔼`.
* **Non-wild points**: every other point `x` has a ball `W` in which the model is either the
  segment or a single circle; a continuous retraction `W → model` fixing the model (projection to
  the segment, resp. radial projection to the circle, `homotopic_refl_of_radial_retraction`)
  pushes the contraction of a loop in the convex set `W` into the model
  (`homotopic_refl_of_retraction`). So `x ∉ loopWildSet`.

## Main statements

`modelSet K`, with instances `CompactSpace`, `ConnectedSpace` (for non-empty `K`) and
`LocallyPathConnectedSpace`, `coveringDimLE_modelSet`, the embedding `modelIncl K : K → modelSet K`
(`isEmbedding_modelIncl`), `range_modelIncl_subset_wildSet` and
`loopWildSet_modelSet_subset_range`, all collected in `exists_model`. Together with
`wildSet ⊆ loopWildSet` (proved elsewhere) they give `wildSet (modelSet K) ≃ₜ K`. Along the way:
`exists_continuous_injective_real` (a countable metric space injects continuously into `ℝ`) and
`exists_scales`. `exists_modelData_of_countable` attaches the earrings at an arbitrary countable
bounded set of abscissae instead (not necessarily closed; used for a continuum with uncountable
wild set in `Peano.Sanity`).

## Design choices

* Everything lives in `ℝ × ℝ` with its sup metric; circles are given by their equations, never by
  `Metric.sphere`. Distances in proofs are sup distances.
* The attached earrings are images of `Peano.earring` under explicit similarities, so the gluing
  and essentiality results of `Peano.Earring` apply verbatim (`earringTo`, `earringFrom`).
* The construction is parametrised by a structure `ModelData` (embedding, bound, scales and their
  properties), so that the topology is proved for arbitrary admissible data and the choice is made
  once (`modelData`).
* Local path-connectedness is proved in a metric "im kleinen" form (`LocJoin`) and converted at the
  end (`locallyPathConnectedSpace_of_locJoin`), avoiding any general theory of null families.
* File layout: the general tools (`LocJoin`, closedness of shrinking unions, null-homotopy through
  retractions) are in `Peano.LocJoin`, the geometry of the earring circles and the radial
  retraction in `Peano.PlaneGeometry`; this file keeps what is specific to the construction
  (the embedding `K ↪ ℝ`, the scales, the disc separation lemma `sq_sub_le_of_mem_discs`, and the
  model). Proof-only helpers (`rest`, …) are `private`.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace Peano

/-! ### Embedding a countable compact metric space into `ℝ` -/

/-- In a countable metric space, every interval of radii contains a radius `ρ` such that the ball
of radius `ρ` about a given point is clopen (no point lies at distance exactly `ρ`). -/
lemma exists_isClopen_ball {K : Type*} [PseudoMetricSpace K] [Countable K] (a : K) {r₁ r₂ : ℝ}
    (h : r₁ < r₂) : ∃ ρ ∈ Ioo r₁ r₂, IsClopen (ball a ρ) := by
  have hc : (range (dist a)).Countable := countable_range _
  obtain ⟨ρ, hρ, hρ'⟩ := (hc.dense_compl ℝ).exists_between h
  refine ⟨ρ, hρ', ?_, isOpen_ball⟩
  have : ball a ρ = closedBall a ρ := by
    ext x
    simp only [mem_ball, mem_closedBall]
    refine ⟨le_of_lt, fun hx => lt_of_le_of_ne hx fun he => hρ ⟨x, ?_⟩⟩
    rw [dist_comm]; exact he
  rw [this]
  exact isClosed_closedBall

/-- A countable metric space admits a continuous injection into `ℝ`: a countable family of clopen
balls separates points, and the Cantor function `∑ₘ 3⁻ᵐ 𝟙_{Bₘ}` turns it into an injection. -/
theorem exists_continuous_injective_real (K : Type*) [MetricSpace K] [Countable K] :
    ∃ e : K → ℝ, Continuous e ∧ Function.Injective e := by
  rcases isEmpty_or_nonempty K with hK | hK
  · exact ⟨fun _ => 0, continuous_const, fun a => isEmptyElim a⟩
  choose ρ hρ hρc using fun (a : K) (n : ℕ) =>
    exists_isClopen_ball a (show (1 : ℝ) / (n + 2) < 1 / (n + 1) from
      one_div_lt_one_div_of_lt (by positivity) (by linarith))
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (K × ℕ)
  let B : ℕ → Set K := fun m => ball (σ m).1 (ρ (σ m).1 (σ m).2)
  have hB : ∀ m, IsClopen (B m) := fun m => hρc _ _
  let φ : K → ℕ → Bool := fun x m => (B m).boolIndicator x
  have hφ : ∀ m, Continuous fun x => φ x m := fun m =>
    (continuous_boolIndicator_iff_isClopen _).2 (hB m)
  refine ⟨fun x => Cardinal.cantorFunction (1 / 3) (φ x), ?_, ?_⟩
  · refine continuous_tsum (u := fun n => (1 / 3 : ℝ) ^ n) (fun n => ?_)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)) (fun n x => ?_)
    · exact (continuous_of_discreteTopology (f := fun b : Bool =>
        cond b ((1 / 3 : ℝ) ^ n) 0)).comp (hφ n)
    · simp only [Cardinal.cantorFunctionAux]
      cases φ x n <;> simp
  · intro a b hab
    by_contra hne
    have hφab : φ a ≠ φ b := by
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.2 hne)
      obtain ⟨m, hm⟩ := hσ (a, n)
      intro h
      have h1 : φ a m = true := by
        simp only [φ, B, hm, Set.boolIndicator, mem_ball, dist_self]
        simp [lt_trans (by positivity) (hρ a n).1]
      have h2 : φ b m = false := by
        simp only [φ, B, hm, Set.boolIndicator, mem_ball]
        have : ¬ dist b a < ρ a n := by
          rw [dist_comm]; exact not_lt.2 ((hρ a n).2.le.trans hn.le)
        simp [this]
      rw [h] at h1
      rw [h1] at h2
      exact Bool.noConfusion h2
    exact hφab (Cardinal.cantorFunction_injective (by norm_num) (by norm_num) hab)

/-! ### Scales of the attached earrings -/

/-- Scales for the earrings attached along an injective `u : K → ℝ`, `K` countable: positive, at
most `1`, tending to `0` (only finitely many exceed any `ε > 0`), and small enough that the
earrings are pairwise disjoint (`4 sₐ s_b < (uₐ - u_b)²`, the condition for two discs tangent to
the axis from above at `uₐ`, `u_b` with radii `sₐ`, `s_b` to be disjoint).

Construction: enumerate `K` injectively by `n : K → ℕ` and put
`sₐ = 2^{-n a} ∏_{n b < n a} min(1, (uₐ - u_b)²) / 8`. -/
theorem exists_scales {K : Type*} [Countable K] (u : K → ℝ) (hu : Function.Injective u) :
    ∃ s : K → ℝ, (∀ a, 0 < s a) ∧ (∀ a, s a ≤ 1) ∧ (∀ ε > 0, {a | ε ≤ s a}.Finite) ∧
      Pairwise fun a b => 4 * s a * s b < (u a - u b) ^ 2 := by
  obtain ⟨n, hn⟩ := Countable.exists_injective_nat K
  have hT : ∀ a, {b | n b < n a}.Finite := fun a =>
    (Set.finite_lt_nat (n a)).preimage hn.injOn
  set g : K → K → ℝ := fun a b => min 1 ((u a - u b) ^ 2) with hg
  have g_nonneg : ∀ a b, 0 ≤ g a b := fun a b => le_min zero_le_one (sq_nonneg _)
  have g_le_one : ∀ a b, g a b ≤ 1 := fun a b => min_le_left _ _
  set P : K → ℝ := fun a => ∏ b ∈ (hT a).toFinset, g a b with hP
  have P_pos : ∀ a, 0 < P a := fun a => Finset.prod_pos fun b hb => by
    have hb' : n b < n a := by simpa using hb
    have hab : u a ≠ u b := hu.ne fun h => hb'.ne (by rw [h])
    exact lt_min one_pos (by positivity)
  have P_le_one : ∀ a, P a ≤ 1 := fun a =>
    Finset.prod_le_one₀ (fun b _ => g_nonneg a b) (fun b _ => g_le_one a b)
  have P_le : ∀ a b, n b < n a → P a ≤ (u a - u b) ^ 2 := by
    classical
    intro a b hb
    have hb' : b ∈ (hT a).toFinset := by simpa using hb
    calc P a = g a b * ∏ c ∈ (hT a).toFinset.erase b, g a c :=
          (Finset.mul_prod_erase _ _ hb').symm
      _ ≤ g a b * 1 := by
          gcongr
          exact Finset.prod_le_one₀ (fun c _ => g_nonneg a c) (fun c _ => g_le_one a c)
      _ ≤ (u a - u b) ^ 2 := by rw [mul_one]; exact min_le_right _ _
  set s : K → ℝ := fun a => (1 / 2) ^ n a * P a / 8 with hs
  have hpow : ∀ a, (1 / 2 : ℝ) ^ n a ≤ 1 := fun a => pow_le_one₀ (by norm_num) (by norm_num)
  have s_pos : ∀ a, 0 < s a := fun a => by have := P_pos a; positivity
  have s_le : ∀ a, s a ≤ 1 / 8 := fun a => by
    have := P_le_one a; have := hpow a; have := P_pos a
    simp only [hs]
    have : (1 / 2 : ℝ) ^ n a * P a ≤ 1 := by
      nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n a)]
    linarith
  have s_le' : ∀ a b, n b < n a → s a ≤ (u a - u b) ^ 2 / 8 := fun a b h => by
    have := P_le a b h; have := hpow a; have := P_pos a
    simp only [hs]
    have : (1 / 2 : ℝ) ^ n a * P a ≤ (u a - u b) ^ 2 := by
      nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n a)]
    linarith
  refine ⟨s, s_pos, fun a => (s_le a).trans (by norm_num), fun ε hε => ?_, fun a b hab => ?_⟩
  · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ((Set.finite_lt_nat N).preimage hn.injOn).subset fun a ha => ?_
    simp only [mem_ofPred_eq, mem_preimage] at ha ⊢
    by_contra hle
    rw [not_lt] at hle
    have h1 : s a ≤ (1 / 2) ^ n a := by
      have := P_le_one a; have := P_pos a
      simp only [hs]
      have : (1 / 2 : ℝ) ^ n a * P a ≤ (1 / 2) ^ n a := by
        nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n a)]
      have := pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) (n a)
      linarith
    have h2 : (1 / 2 : ℝ) ^ n a ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    linarith
  · have hne : n a ≠ n b := hn.ne hab
    have hd : 0 < (u a - u b) ^ 2 := by
      have : u a - u b ≠ 0 := sub_ne_zero.2 (hu.ne hab)
      positivity
    have ha := s_pos a; have hb := s_pos b
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := s_le' b a h
      have h2 := s_le a
      have : (u b - u a) ^ 2 = (u a - u b) ^ 2 := by ring
      nlinarith
    · have h1 := s_le' a b h
      have h2 := s_le b
      nlinarith

/-- Two discs tangent to the horizontal axis from above, at abscissae `u`, `u'` with radii `s`,
`s'`, meet only if `(u - u')² ≤ 4 s s'`. The disc of radius `s` tangent at `u` is written
`(x - u)² ≤ y (2 s - y)`. -/
lemma sq_sub_le_of_mem_discs {x y u u' s s' : ℝ} (hy : 0 ≤ y) (h : (x - u) ^ 2 ≤ y * (2 * s - y))
    (h' : (x - u') ^ 2 ≤ y * (2 * s' - y)) (hs : 0 < s) (hs' : 0 < s') :
    (u - u') ^ 2 ≤ 4 * s * s' := by
  set α := x - u
  set β := x - u'
  set Q := 2 * s - y
  set R := 2 * s' - y
  have hPQ : 0 ≤ y * Q := (sq_nonneg α).trans h
  have hPR : 0 ≤ y * R := (sq_nonneg β).trans h'
  have h1 : (α * β) ^ 2 ≤ (y * Q) * (y * R) := by
    rw [mul_pow]; exact mul_le_mul h h' (sq_nonneg _) hPQ
  have h2 : 0 ≤ y ^ 2 + Q * R := by
    rcases hy.eq_or_lt with h0 | h0
    · subst h0; simp only [Q, R]; nlinarith
    · have hQ : 0 ≤ Q := nonneg_of_mul_nonneg_right (by linarith) h0
      have hR : 0 ≤ R := nonneg_of_mul_nonneg_right (by linarith) h0
      positivity
  have h3 : 2 * |α * β| ≤ y ^ 2 + Q * R := by
    have : (2 * |α * β|) ^ 2 ≤ (y ^ 2 + Q * R) ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith [sq_nonneg (y ^ 2 - Q * R)]
    exact (pow_le_pow_iff_left₀ (by positivity) h2 two_ne_zero).1 this
  have h4 := neg_abs_le (α * β)
  have hαβ : u - u' = β - α := by simp only [α, β]; ring
  rw [hαβ]
  have : 4 * s * s' = (y + Q) * (y + R) := by simp only [Q, R]; ring
  rw [this]
  nlinarith

/-! ### The data of a model -/

/-- The data from which a model is built: a continuous injection `u : K → [-L, L]` (the
abscissae of the attachment points) and scales `s : K → (0, 1]` tending to `0` and making the
attached earrings pairwise disjoint. -/
structure ModelData (K : Type*) [TopologicalSpace K] where
  /-- The abscissa of the attachment point of the earring at `a`. -/
  u : K → ℝ
  /-- The scale of the earring attached at `a`. -/
  s : K → ℝ
  /-- A bound for `|u|`; the axis segment of the model is `[-L, L] × {0}`. -/
  L : ℝ
  /-- `u` is continuous. -/
  continuous_u : Continuous u
  /-- `u` is injective. -/
  injective_u : Function.Injective u
  /-- The attachment points lie on the segment. -/
  abs_u_le : ∀ a, |u a| ≤ L
  /-- The scales are positive. -/
  s_pos : ∀ a, 0 < s a
  /-- The scales are at most `1`. -/
  s_le_one : ∀ a, s a ≤ 1
  /-- The scales tend to `0`. -/
  finite_le_s : ∀ ε > 0, {a | ε ≤ s a}.Finite
  /-- Distinct earrings are disjoint. -/
  sep : Pairwise fun a b => 4 * s a * s b < (u a - u b) ^ 2

/-- Model data exist for every countable compact metric space. -/
theorem nonempty_modelData (K : Type*) [MetricSpace K] [CompactSpace K] [Countable K] :
    Nonempty (ModelData K) := by
  obtain ⟨u, hu, hinj⟩ := exists_continuous_injective_real K
  obtain ⟨L, hL⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_scales u hinj
  exact ⟨⟨u, s, L, hu, hinj, fun a => by simpa using hL a (mem_univ a), h1, h2, h3, h4⟩⟩

/-- Model data attaching the earrings at the points `(a, 0)` of a countable bounded set
`S ⊆ ℝ`, which need not be closed (`u` is the inclusion `S → ℝ`). For dense `S` the model has an
uncountable wild set (`Peano.Sanity.exists_peano_wildSet_not_countable`). -/
theorem exists_modelData_of_countable (S : Set ℝ) (hS : S.Countable)
    (hb : Bornology.IsBounded S) : ∃ D : ModelData S, ∀ a, D.u a = a := by
  have : Countable S := hS.to_subtype
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  obtain ⟨s, h1, h2, h3, h4⟩ := exists_scales (Subtype.val : S → ℝ) Subtype.val_injective
  exact ⟨⟨Subtype.val, s, C, continuous_subtype_val, Subtype.val_injective,
    fun a => by simpa [Real.norm_eq_abs] using hC a a.2, h1, h2, h3, h4⟩, fun _ => rfl⟩

namespace ModelData

variable {K : Type*} [TopologicalSpace K] (D : ModelData K)

/-! ### Geometry of the attached earrings -/

/-- The similarity placing the earring at `a`: rotate by a quarter turn (so that the earring is
tangent to the horizontal axis from above), scale by `sₐ`, translate to `(uₐ, 0)`. -/
def toPlane (a : K) (p : ℝ × ℝ) : ℝ × ℝ := (D.u a - D.s a * p.2, D.s a * p.1)

/-- The inverse of `toPlane a`. -/
def fromPlane (a : K) (y : ℝ × ℝ) : ℝ × ℝ := (y.2 / D.s a, (D.u a - y.1) / D.s a)

/-- `fromPlane a` is a left inverse of `toPlane a`. -/
@[simp] lemma fromPlane_toPlane (a : K) (p : ℝ × ℝ) : D.fromPlane a (D.toPlane a p) = p := by
  have := (D.s_pos a).ne'
  ext <;> simp [fromPlane, toPlane, this]

/-- `fromPlane a` is a right inverse of `toPlane a`. -/
@[simp] lemma toPlane_fromPlane (a : K) (y : ℝ × ℝ) : D.toPlane a (D.fromPlane a y) = y := by
  have := (D.s_pos a).ne'
  ext <;> simp [fromPlane, toPlane, this, mul_div_cancel₀]

/-- `toPlane a` is continuous. -/
@[fun_prop] lemma continuous_toPlane (a : K) : Continuous (D.toPlane a) := by
  unfold toPlane; fun_prop

/-- `fromPlane a` is continuous. -/
@[fun_prop] lemma continuous_fromPlane (a : K) : Continuous (D.fromPlane a) := by
  unfold fromPlane; fun_prop

/-- The attachment point `(uₐ, 0)` of the earring at `a`. -/
def base (a : K) : ℝ × ℝ := (D.u a, 0)

/-- `toPlane a` sends the base point of the earring to the attachment point. -/
@[simp] lemma toPlane_zero (a : K) : D.toPlane a (0, 0) = D.base a := by
  simp [toPlane, base]

/-- `fromPlane a` sends exactly the attachment point to the origin. -/
lemma fromPlane_eq_zero_iff {a : K} {y : ℝ × ℝ} : D.fromPlane a y = (0, 0) ↔ y = D.base a := by
  constructor
  · intro h; rw [← D.toPlane_fromPlane a y, h, toPlane_zero]
  · rintro rfl; rw [← toPlane_zero, fromPlane_toPlane]

/-- The `k`-th circle of the earring at `a`. -/
def circle (a : K) (k : ℕ) : Set (ℝ × ℝ) := D.fromPlane a ⁻¹' earringCircle k

/-- The earring attached at `a`. -/
def ear (a : K) : Set (ℝ × ℝ) := D.fromPlane a ⁻¹' earring

/-- The axis segment `[-L, L] × {0}`. -/
def seg : Set (ℝ × ℝ) := Icc (-D.L) D.L ×ˢ {0}

/-- **The model**: the axis segment with an earring attached at every `(uₐ, 0)`. -/
def model : Set (ℝ × ℝ) := D.seg ∪ ⋃ a, D.ear a

/-- The earring at `a` is the union of its circles. -/
lemma ear_eq_iUnion (a : K) : D.ear a = ⋃ k, D.circle a k := by
  simp [ear, circle, earring, preimage_iUnion]

/-- The model is the segment together with all the circles of all the earrings. -/
lemma model_eq : D.model = D.seg ∪ ⋃ i : K × ℕ, D.circle i.1 i.2 := by
  simp [model, ear_eq_iUnion, iUnion_prod']

/-- The equation of the `k`-th circle at `a`: centre `(uₐ, sₐ rₖ)`, radius `sₐ rₖ`. -/
lemma mem_circle_iff {a : K} {k : ℕ} {y : ℝ × ℝ} : y ∈ D.circle a k ↔
    (y.1 - D.u a) ^ 2 + (y.2 - D.s a * earringRadius k) ^ 2 = (D.s a * earringRadius k) ^ 2 := by
  have hs := (D.s_pos a).ne'
  simp only [circle, earringCircle, fromPlane, mem_preimage, mem_ofPred_eq]
  rw [div_sub' hs, div_pow, div_pow, ← add_div, div_eq_iff (by positivity)]
  constructor <;> intro h <;> linear_combination h

/-- Points of the `k`-th circle at `a` lie at heights `0 ≤ y₂ ≤ 2 sₐ rₖ`, within `sₐ rₖ`
horizontally of `uₐ`, and in the disc of radius `sₐ` tangent to the axis at `(uₐ, 0)`. -/
lemma circle_bounds {a : K} {k : ℕ} {y : ℝ × ℝ} (hy : y ∈ D.circle a k) :
    0 ≤ y.2 ∧ y.2 ≤ 2 * (D.s a * earringRadius k) ∧ |y.1 - D.u a| ≤ D.s a * earringRadius k ∧
      (y.1 - D.u a) ^ 2 ≤ y.2 * (2 * D.s a - y.2) := by
  rw [mem_circle_iff] at hy
  have hs := D.s_pos a
  have hr := earringRadius_pos k
  have hr1 := earringRadius_le_one k
  have hρ : 0 < D.s a * earringRadius k := mul_pos hs hr
  have hρs : D.s a * earringRadius k ≤ D.s a := mul_le_of_le_one_right hs.le hr1
  set ρ := D.s a * earringRadius k
  have h1 : y.2 * (y.2 - 2 * ρ) ≤ 0 := by nlinarith [sq_nonneg (y.1 - D.u a)]
  have h2 : 0 ≤ y.2 := by
    by_contra! h; nlinarith
  refine ⟨h2, ?_, ?_, ?_⟩
  · by_contra! h; nlinarith
  · rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y.2 - ρ)]
  · nlinarith

/-- The `k`-th circle at `a` lies in the (sup-metric) ball of radius `2 sₐ rₖ` about the
attachment point. -/
lemma circle_subset_closedBall (a : K) (k : ℕ) :
    D.circle a k ⊆ closedBall (D.base a) (2 * (D.s a * earringRadius k)) := by
  intro y hy
  obtain ⟨h1, h2, h3, -⟩ := D.circle_bounds hy
  have hρ : 0 < D.s a * earringRadius k := mul_pos (D.s_pos a) (earringRadius_pos k)
  rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [base, sub_zero]
  refine max_le (by linarith) ?_
  rw [abs_of_nonneg h1]; exact h2

/-- A point lies on the earring at `a` iff it lies on one of its circles. -/
lemma mem_ear_iff {a : K} {y : ℝ × ℝ} : y ∈ D.ear a ↔ ∃ k, y ∈ D.circle a k := by
  rw [ear_eq_iUnion, mem_iUnion]

/-- The earring at `a` lies in the ball of radius `2 sₐ` about the attachment point. -/
lemma ear_subset_closedBall (a : K) : D.ear a ⊆ closedBall (D.base a) (2 * D.s a) := by
  intro y hy
  obtain ⟨k, hk⟩ := D.mem_ear_iff.1 hy
  refine closedBall_subset_closedBall ?_ (D.circle_subset_closedBall a k hk)
  have := mul_le_of_le_one_right (D.s_pos a).le (earringRadius_le_one k)
  linarith

/-- Earrings attached at distinct points are disjoint. -/
lemma disjoint_ear {a b : K} (hab : a ≠ b) : Disjoint (D.ear a) (D.ear b) := by
  refine Set.disjoint_left.2 fun y ha hb => ?_
  obtain ⟨j, hj⟩ := D.mem_ear_iff.1 ha
  obtain ⟨k, hk⟩ := D.mem_ear_iff.1 hb
  obtain ⟨h0, -, -, h⟩ := D.circle_bounds hj
  obtain ⟨-, -, -, h'⟩ := D.circle_bounds hk
  have := sq_sub_le_of_mem_discs h0 h h' (D.s_pos a) (D.s_pos b)
  linarith [D.sep hab]

/-- The earring at `a` meets the horizontal axis only at its attachment point. -/
lemma eq_base_of_mem_ear {a : K} {y : ℝ × ℝ} (hy : y ∈ D.ear a) (h0 : y.2 = 0) :
    y = D.base a := by
  obtain ⟨k, hk⟩ := D.mem_ear_iff.1 hy
  obtain ⟨-, -, -, h⟩ := D.circle_bounds hk
  rw [h0] at h
  have : y.1 = D.u a := by nlinarith [sq_nonneg (y.1 - D.u a)]
  exact Prod.ext this h0

/-- The attachment point lies on every circle of the earring. -/
lemma base_mem_circle (a : K) (k : ℕ) : D.base a ∈ D.circle a k := by
  simp only [circle, mem_preimage, D.fromPlane_eq_zero_iff.2 rfl]
  exact zero_mem_earringCircle k

/-- The attachment point lies on the earring. -/
lemma base_mem_ear (a : K) : D.base a ∈ D.ear a :=
  D.mem_ear_iff.2 ⟨0, D.base_mem_circle a 0⟩

/-- The circles are closed. -/
lemma isClosed_circle (a : K) (k : ℕ) : IsClosed (D.circle a k) :=
  (isClosed_earringCircle k).preimage (D.continuous_fromPlane a)

/-- The attached earrings are closed (indeed compact). -/
lemma isClosed_ear (a : K) : IsClosed (D.ear a) :=
  isCompact_earring.isClosed.preimage (D.continuous_fromPlane a)

/-- Two distinct circles of the same earring meet only at its attachment point. -/
lemma eq_base_of_mem_circle_of_mem_circle {a : K} {j k : ℕ} (hjk : j ≠ k) {y : ℝ × ℝ}
    (hj : y ∈ D.circle a j) (hk : y ∈ D.circle a k) : y = D.base a := by
  have : D.fromPlane a y ∈ earringCircle j ∩ earringCircle k := ⟨hj, hk⟩
  rw [earringCircle_inter_earringCircle hjk] at this
  exact D.fromPlane_eq_zero_iff.1 this

/-- The attachment points lie on the segment. -/
lemma base_mem_seg (a : K) : D.base a ∈ D.seg :=
  ⟨abs_le.1 (D.abs_u_le a), rfl⟩

/-- The segment is closed. -/
lemma isClosed_seg : IsClosed D.seg := isClosed_Icc.prod isClosed_singleton

/-- The segment is convex. -/
lemma convex_seg : Convex ℝ D.seg := (convex_Icc _ _).prod (convex_singleton _)

/-- The segment is part of the model. -/
lemma seg_subset_model : D.seg ⊆ D.model := subset_union_left

/-- The attached earrings are part of the model. -/
lemma ear_subset_model (a : K) : D.ear a ⊆ D.model :=
  (subset_iUnion D.ear a).trans subset_union_right

/-- The circles of an earring are part of it. -/
lemma circle_subset_ear (a : K) (k : ℕ) : D.circle a k ⊆ D.ear a := by
  rw [ear_eq_iUnion]; exact subset_iUnion (D.circle a) k

/-! ### Parametrisation of the circles -/

/-- The `1`-periodic parametrisation of the `k`-th circle at `a`, starting at the attachment
point. -/
def param (a : K) (k : ℕ) (t : ℝ) : ℝ × ℝ := D.toPlane a (earringParam k t)

/-- The parametrisation is continuous. -/
lemma continuous_param (a : K) (k : ℕ) : Continuous (D.param a k) :=
  (D.continuous_toPlane a).comp (continuous_earringParam k)

/-- The parametrisation is `1`-periodic. -/
lemma param_periodic (a : K) (k : ℕ) : Function.Periodic (D.param a k) 1 := fun t => by
  simp only [param, earringParam_periodic k t]

/-- The parametrisation traces exactly the circle. -/
lemma range_param (a : K) (k : ℕ) : range (D.param a k) = D.circle a k := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    simp only [circle, param, mem_preimage, fromPlane_toPlane]
    exact earringParam_mem_earringCircle k t
  · intro hy
    obtain ⟨t, -, ht⟩ := exists_earringParam_eq hy
    exact ⟨t, by simp [param, ht]⟩

/-- The parametrisation is injective modulo `1`. -/
lemma param_eq_param {a : K} {k : ℕ} {t t' : ℝ} (h : D.param a k t = D.param a k t') :
    ∃ n : ℤ, t = t' + n :=
  earringParam_eq_earringParam (by simpa [param] using congrArg (D.fromPlane a) h)

/-- The parametrisation starts at the attachment point. -/
@[simp] lemma param_zero (a : K) (k : ℕ) : D.param a k 0 = D.base a := by
  simp [param]

/-- Each circle is locally joinable everywhere. -/
lemma locJoin_circle (a : K) (k : ℕ) (p : ℝ × ℝ) : LocJoin (D.circle a k) p := by
  refine locJoin_of_isClosed (D.isClosed_circle a k) (fun p hp => ?_) p
  rw [← D.range_param] at hp ⊢
  obtain ⟨t, rfl⟩ := hp
  exact locJoin_range_of_periodic (D.continuous_param a k) (D.param_periodic a k)
    (fun _ _ h => D.param_eq_param h) t

/-- Each point of a circle is joined to the attachment point inside the circle. -/
lemma joinedIn_circle_base {a : K} {k : ℕ} {q : ℝ × ℝ} (hq : q ∈ D.circle a k) :
    JoinedIn (D.circle a k) q (D.base a) := by
  rw [← D.range_param] at hq ⊢
  exact (isPathConnected_range (D.continuous_param a k)).joinedIn q hq _ ⟨0, D.param_zero a k⟩

/-! ### Topology of the model -/

/-- All but finitely many circles lie in arbitrarily small balls about their attachment points. -/
lemma finite_circle_not_small {ε : ℝ} (hε : 0 < ε) :
    {i : K × ℕ | ¬ D.circle i.1 i.2 ⊆ closedBall (D.base i.1) ε}.Finite := by
  refine ((D.finite_le_s (ε / 2) (half_pos hε)).prod
    (finite_le_earringRadius (half_pos hε))).subset fun ⟨a, k⟩ h => ?_
  simp only [mem_ofPred_eq] at h
  have hs := D.s_pos a; have hs1 := D.s_le_one a
  have hr := earringRadius_pos k; have hr1 := earringRadius_le_one k
  have hlt : ε < 2 * (D.s a * earringRadius k) := by
    by_contra! hle
    exact h ((D.circle_subset_closedBall a k).trans (closedBall_subset_closedBall hle))
  constructor
  · show ε / 2 ≤ D.s a; nlinarith
  · show ε / 2 ≤ earringRadius k; nlinarith

/-- All but finitely many earrings lie in arbitrarily small balls about their attachment
points. -/
lemma finite_ear_not_small {ε : ℝ} (hε : 0 < ε) :
    {a : K | ¬ D.ear a ⊆ closedBall (D.base a) ε}.Finite := by
  refine (D.finite_le_s (ε / 2) (half_pos hε)).subset fun a h => ?_
  simp only [mem_ofPred_eq] at h ⊢
  by_contra! hlt
  exact h ((D.ear_subset_closedBall a).trans (closedBall_subset_closedBall (by linarith)))

/-- The model is closed in `ℝ²`. -/
lemma isClosed_model : IsClosed D.model :=
  isClosed_union_iUnion_of_shrinking D.isClosed_seg D.ear D.isClosed_ear D.base D.base_mem_seg
    fun _ hε => D.finite_ear_not_small hε

/-- The model is bounded. -/
lemma isBounded_model : Bornology.IsBounded D.model := by
  refine (isBounded_closedBall (x := ((0 : ℝ), (0 : ℝ))) (r := D.L + 2)).subset ?_
  rintro y (⟨⟨h1, h2⟩, h3⟩ | hy)
  · simp only [mem_singleton_iff] at h3
    rw [mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, h3]
    simp only [sub_zero, abs_zero]
    exact max_le (abs_le.2 ⟨by linarith, by linarith⟩) (by linarith)
  · obtain ⟨a, ha⟩ := mem_iUnion.1 hy
    have h1 := D.ear_subset_closedBall a ha
    rw [mem_closedBall] at h1 ⊢
    have h2 : dist (D.base a) ((0 : ℝ), (0 : ℝ)) ≤ D.L := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      simp only [base, sub_zero, abs_zero]
      exact max_le (D.abs_u_le a) ((abs_nonneg _).trans (D.abs_u_le a))
    have := D.s_le_one a
    linarith [dist_triangle y (D.base a) ((0 : ℝ), (0 : ℝ))]

/-- The model is compact. -/
lemma isCompact_model : IsCompact D.model :=
  Metric.isCompact_of_isClosed_isBounded D.isClosed_model D.isBounded_model

/-- The model is locally joinable at every point. -/
lemma locJoin_model (p : ℝ × ℝ) : LocJoin D.model p := by
  rw [model_eq]
  exact locJoin_union_iUnion_of_shrinking (fun i : K × ℕ => D.circle i.1 i.2)
    (fun i => D.base i.1)
    (locJoin_of_isClosed D.isClosed_seg fun _ hp => Convex.locJoin D.convex_seg hp)
    (fun i p => D.locJoin_circle i.1 i.2 p) (fun i => D.base_mem_seg i.1)
    (fun _ _ hq => D.joinedIn_circle_base hq) (fun _ hε => D.finite_circle_not_small hε) p

/-- The model is path-connected. -/
lemma isPathConnected_model [Nonempty K] : IsPathConnected D.model := by
  obtain ⟨a₀⟩ := ‹Nonempty K›
  have hseg : ∀ y ∈ D.seg, JoinedIn D.model y (D.base a₀) := fun y hy =>
    ((D.convex_seg.isPathConnected ⟨y, hy⟩).joinedIn y hy _ (D.base_mem_seg a₀)).mono
      D.seg_subset_model
  refine ⟨D.base a₀, D.seg_subset_model (D.base_mem_seg a₀), fun {y} hy => ?_⟩
  rcases hy with hy | hy
  · exact (hseg y hy).symm
  · obtain ⟨a, ha⟩ := mem_iUnion.1 hy
    obtain ⟨k, hk⟩ := D.mem_ear_iff.1 ha
    exact ((D.joinedIn_circle_base hk).mono
      ((D.circle_subset_ear a k).trans (D.ear_subset_model a))).trans
      (hseg _ (D.base_mem_seg a)) |>.symm

/-- The interior of a circle in `ℝ²` is empty. -/
lemma interior_circle (a : K) (k : ℕ) : interior (D.circle a k) = ∅ := by
  refine eq_empty_of_forall_notMem fun y hy => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy)
  have hmem : ∀ η, |η| < δ → (y.1, y.2 + η) ∈ D.circle a k := fun η hη => hball <| by
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simpa using hη
  have h0 := D.mem_circle_iff.1 (hmem 0 (by simpa using hδ))
  have h1 := D.mem_circle_iff.1 (hmem (δ / 2) (by rw [abs_of_pos (half_pos hδ)]; linarith))
  have h2 := D.mem_circle_iff.1 (hmem (-(δ / 2)) (by
    rw [abs_neg, abs_of_pos (half_pos hδ)]; linarith))
  simp only [add_zero] at h0 h1 h2
  nlinarith

/-- The interior of the axis segment in `ℝ²` is empty. -/
lemma interior_seg : interior D.seg = ∅ := by
  rw [seg, interior_prod_eq, interior_singleton, prod_empty]

/-- The model has empty interior in `ℝ²`. -/
lemma interior_model [Countable K] : interior D.model = ∅ := by
  have hM : IsMeagre D.model := by
    rw [model_eq]
    refine (IsNowhereDense.isMeagre ?_).union (isMeagre_iUnion fun i => IsNowhereDense.isMeagre ?_)
    · exact D.isClosed_seg.isNowhereDense_iff.2 D.interior_seg
    · exact (D.isClosed_circle i.1 i.2).isNowhereDense_iff.2 (D.interior_circle i.1 i.2)
  by_contra h
  exact not_isMeagre_of_isOpen isOpen_interior (nonempty_iff_ne_empty.2 h)
    (hM.mono interior_subset)

/-- The model is a compact space. -/
instance compactSpace_model : CompactSpace D.model :=
  isCompact_iff_compactSpace.1 D.isCompact_model

/-- The model is connected. -/
instance connectedSpace_model [Nonempty K] : ConnectedSpace D.model :=
  have : PathConnectedSpace D.model :=
    isPathConnected_iff_pathConnectedSpace.1 D.isPathConnected_model
  inferInstance

/-- The model is locally path-connected. -/
instance locallyPathConnectedSpace_model : LocallyPathConnectedSpace D.model :=
  locallyPathConnectedSpace_of_locJoin fun p _ => D.locJoin_model p

/-! ### Wild points -/

/-- The attachment points, as points of the model: `a ↦ (uₐ, 0)`. -/
def incl (a : K) : D.model := ⟨D.base a, D.seg_subset_model (D.base_mem_seg a)⟩

/-- The attachment point depends continuously on `a`. -/
lemma continuous_base : Continuous D.base := by
  unfold base; have := D.continuous_u; fun_prop

/-- `incl` is continuous. -/
lemma continuous_incl : Continuous D.incl :=
  D.continuous_base.subtype_mk _

/-- `incl` is injective. -/
lemma injective_incl : Function.Injective D.incl := fun _ _ h =>
  D.injective_u (congrArg (fun y : D.model => (y : ℝ × ℝ).1) h)

/-- For compact `K`, `incl` is a topological embedding. -/
lemma isEmbedding_incl [CompactSpace K] : Topology.IsEmbedding D.incl :=
  (D.continuous_incl.isClosedEmbedding D.injective_incl).isEmbedding

/-- The earring attached at `a`, as a map `𝔼 → model`. -/
def earringTo (a : K) : C(earring, D.model) where
  toFun p := ⟨D.toPlane a p, D.ear_subset_model a (by simp [ear])⟩
  continuous_toFun := ((D.continuous_toPlane a).comp continuous_subtype_val).subtype_mk _

/-- The earring at `a` is based at the attachment point `incl a`. -/
@[simp] lemma earringTo_base (a : K) : D.earringTo a earringBase = D.incl a :=
  Subtype.ext (by simp [earringTo, earringBase, incl])

/-- The rest of the model, seen from the earring at `a`: the segment and the other earrings. -/
private def rest (a : K) : Set (ℝ × ℝ) := D.seg ∪ ⋃ b : {b // b ≠ a}, D.ear b

/-- The rest of the model, seen from the earring at `a`, is closed. -/
private lemma isClosed_rest (a : K) : IsClosed (D.rest a) := by
  refine isClosed_union_iUnion_of_shrinking D.isClosed_seg (fun b : {b // b ≠ a} => D.ear b)
    (fun b => D.isClosed_ear b) (fun b => D.base b) (fun b => D.base_mem_seg b) fun ε hε => ?_
  exact (D.finite_ear_not_small hε).preimage Subtype.val_injective.injOn

/-- The model is the earring at `a` together with the rest. -/
private lemma model_subset_ear_union_rest (a : K) : D.model ⊆ D.ear a ∪ D.rest a := by
  rintro y (hy | hy)
  · exact Or.inr (Or.inl hy)
  · obtain ⟨b, hb⟩ := mem_iUnion.1 hy
    by_cases hba : b = a
    · subst hba; exact Or.inl hb
    · exact Or.inr (Or.inr (mem_iUnion.2 ⟨⟨b, hba⟩, hb⟩))

/-- The earring at `a` meets the rest only at the attachment point. -/
private lemma eq_base_of_mem_ear_of_mem_rest {a : K} {y : ℝ × ℝ} (h : y ∈ D.ear a)
    (h' : y ∈ D.rest a) : y = D.base a := by
  rcases h' with h' | h'
  · exact D.eq_base_of_mem_ear h h'.2
  · obtain ⟨⟨b, hb⟩, hy⟩ := mem_iUnion.1 h'
    exact absurd hy (Set.disjoint_left.1 (D.disjoint_ear (Ne.symm hb)) h)

open Classical in
/-- The retraction of the model onto the earring at `a` (inverted into `𝔼`): the earring is mapped
back by `fromPlane a`, everything else to the base point. -/
def earringFrom (a : K) : C(D.model, earring) where
  toFun x := if h : (x : ℝ × ℝ) ∈ D.ear a then ⟨D.fromPlane a x, h⟩ else earringBase
  continuous_toFun := by
    rw [← continuousOn_univ]
    have hU : (univ : Set D.model) =
        {x : D.model | (x : ℝ × ℝ) ∈ D.ear a} ∪ {x | (x : ℝ × ℝ) ∈ D.rest a} := by
      ext x; simpa using D.model_subset_ear_union_rest a x.2
    rw [hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ ((D.isClosed_ear a).preimage continuous_subtype_val)
      ((D.isClosed_rest a).preimage continuous_subtype_val)
    · rw [continuousOn_iff_continuous_domRestrict]
      have : (({x : D.model | (x : ℝ × ℝ) ∈ D.ear a}).domRestrict fun x : D.model =>
          if h : (x : ℝ × ℝ) ∈ D.ear a then (⟨D.fromPlane a x, h⟩ : earring) else earringBase) =
          fun x => ⟨D.fromPlane a x, x.2⟩ := by
        funext x
        have hx : ((x : D.model) : ℝ × ℝ) ∈ D.ear a := x.2
        simp [Set.domRestrict, hx]
      rw [this]
      exact ((D.continuous_fromPlane a).comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    · refine continuousOn_const (c := earringBase).congr fun x hx => ?_
      by_cases h : (x : ℝ × ℝ) ∈ D.ear a
      · have hb := D.eq_base_of_mem_ear_of_mem_rest h hx
        simp only [h, dite_true]
        exact Subtype.ext (by simp [earringBase, D.fromPlane_eq_zero_iff.2 hb])
      · simp [h]

/-- `earringFrom a` is a left inverse of `earringTo a`. -/
@[simp] lemma earringFrom_earringTo (a : K) (p : earring) :
    D.earringFrom a (D.earringTo a p) = p := by
  have h : D.toPlane a p ∈ D.ear a := by simp [ear]
  simp [earringFrom, earringTo, h]

/-- The earring at `a` is fully essential in the model. -/
theorem fullyEssential_earringTo (a : K) : FullyEssential (D.earringTo a) := by
  intro k
  refine not_homotopic_refl_of_map (D.earringFrom a) ?_
  have hb : D.earringFrom a (D.earringTo a earringBase) = earringBase :=
    D.earringFrom_earringTo a _
  have heq : ((earringLoop k).map (D.earringTo a).continuous).map (D.earringFrom a).continuous =
      (earringLoop k).cast hb hb :=
    Path.ext <| funext fun t => D.earringFrom_earringTo a (earringLoop k t)
  rw [heq, cast_homotopic_refl_iff]
  exact earringLoop_not_homotopic_refl k

/-- Every attachment point is wild. -/
theorem incl_mem_wildSet (a : K) : D.incl a ∈ wildSet D.model :=
  ⟨D.earringTo a, D.earringTo_base a, D.fullyEssential_earringTo a⟩

/-- All attachment points are wild. -/
theorem range_incl_subset_wildSet : range D.incl ⊆ wildSet D.model := by
  rintro _ ⟨a, rfl⟩; exact D.incl_mem_wildSet a

/-! ### Points that are not attachment points are not wild -/

/-- For compact `K` the set of attachment points is closed. -/
lemma isClosed_range_base [CompactSpace K] : IsClosed (range D.base) :=
  (isCompact_range D.continuous_base).isClosed

/-- For compact `K`, the attachment points together with all the earrings form a closed set. -/
private lemma isClosed_range_base_union [CompactSpace K] : IsClosed (range D.base ∪ ⋃ a, D.ear a) :=
  isClosed_union_iUnion_of_shrinking D.isClosed_range_base D.ear D.isClosed_ear D.base
    (fun a => mem_range_self a) fun _ hε => D.finite_ear_not_small hε

/-- Every point of the segment other than an attachment point has a neighbourhood in which all
loops are null-homotopic in the model: near such a point the model is the segment, and the
nearest-point projection onto the segment is a retraction. -/
lemma exists_nhds_homotopic_refl_of_mem_seg [CompactSpace K] {x : D.model}
    (hx : (x : ℝ × ℝ) ∈ D.seg) (hxb : x ∉ range D.incl) :
    ∃ U ∈ 𝓝 x, ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  have hxb' : (x : ℝ × ℝ) ∉ range D.base := fun ⟨a, ha⟩ => hxb ⟨a, Subtype.ext ha⟩
  have hxT : (x : ℝ × ℝ) ∉ range D.base ∪ ⋃ a, D.ear a := by
    rintro (h | h)
    · exact hxb' h
    · obtain ⟨a, ha⟩ := mem_iUnion.1 h
      exact hxb' ⟨a, (D.eq_base_of_mem_ear ha hx.2).symm⟩
  obtain ⟨δ, hδ, hT⟩ := Metric.isOpen_iff.1 D.isClosed_range_base_union.isOpen_compl _ hxT
  have hW : ∀ y ∈ ball (x : ℝ × ℝ) δ, y ∈ D.model → y ∈ D.seg := by
    intro y hy hyM
    rcases hyM with hyS | hyE
    · exact hyS
    · exact absurd (Or.inr hyE) (hT hy)
  have hL : -D.L ≤ D.L := hx.1.1.trans hx.1.2
  let r : ℝ × ℝ → ℝ × ℝ := fun y => (max (-D.L) (min D.L y.1), 0)
  refine ⟨Subtype.val ⁻¹' ball (x : ℝ × ℝ) δ,
    (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hδ),
    fun γ hγ => homotopic_refl_of_retraction (convex_ball _ δ) r ?_ ?_ ?_ γ
      fun t => hγ (mem_range_self t)⟩
  · exact ((continuous_const.max (continuous_const.min continuous_fst)).prodMk
      continuous_const).continuousOn
  · intro y _
    exact D.seg_subset_model ⟨⟨le_max_left _ _, max_le hL (min_le_left _ _)⟩, rfl⟩
  · intro y hy hyM
    obtain ⟨⟨h1, h2⟩, h3⟩ := hW y hy hyM
    simp only [mem_singleton_iff] at h3
    simp only [r, min_eq_right h2, max_eq_right h1]
    exact Prod.ext rfl h3.symm

/-- Every point of a circle other than its attachment point has a neighbourhood in which all
loops are null-homotopic in the model: near such a point the model is the circle, and the radial
projection onto the circle is a retraction. -/
lemma exists_nhds_homotopic_refl_of_mem_circle {x : D.model} {a : K} {k : ℕ}
    (hx : (x : ℝ × ℝ) ∈ D.circle a k) (hxb : (x : ℝ × ℝ) ≠ D.base a) :
    ∃ U ∈ 𝓝 x, ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  have hρ : 0 < D.s a * earringRadius k := mul_pos (D.s_pos a) (earringRadius_pos k)
  set ρ := D.s a * earringRadius k with hρ_def
  have hx2 : 0 < (x : ℝ × ℝ).2 := by
    obtain ⟨h0, -⟩ := D.circle_bounds hx
    refine lt_of_le_of_ne h0 fun h => hxb ?_
    exact D.eq_base_of_mem_ear (D.circle_subset_ear a k hx) h.symm
  -- the rest of the model, away from the circle `(a, k)`
  set R := D.seg ∪ ⋃ i : {i : K × ℕ // i ≠ (a, k)}, D.circle i.1.1 i.1.2 with hR_def
  have hRc : IsClosed R :=
    isClosed_union_iUnion_of_shrinking D.isClosed_seg
      (fun i : {i : K × ℕ // i ≠ (a, k)} => D.circle i.1.1 i.1.2) (fun i => D.isClosed_circle _ _)
      (fun i => D.base i.1.1) (fun i => D.base_mem_seg _)
      fun _ hε => (D.finite_circle_not_small hε).preimage Subtype.val_injective.injOn
  have hxR : (x : ℝ × ℝ) ∉ R := by
    rintro (h | h)
    · exact hx2.ne' h.2
    · obtain ⟨⟨⟨b, j⟩, hbj⟩, hy⟩ := mem_iUnion.1 h
      by_cases hba : b = a
      · subst hba
        have hjk : j ≠ k := fun h => hbj (by rw [h])
        exact hxb (D.eq_base_of_mem_circle_of_mem_circle hjk hy hx)
      · exact Set.disjoint_left.1 (D.disjoint_ear hba) (D.circle_subset_ear b j hy)
          (D.circle_subset_ear a k hx)
  obtain ⟨δ₀, hδ₀, hδR⟩ := Metric.isOpen_iff.1 hRc.isOpen_compl _ hxR
  set δ := min δ₀ (ρ / 2) with hδ_def
  have hδ : 0 < δ := lt_min hδ₀ (half_pos hρ)
  set W := ball (x : ℝ × ℝ) δ with hW_def
  have hWM : ∀ y ∈ W, y ∈ D.model → y ∈ D.circle a k := by
    intro y hy hyM
    have hyR : y ∉ R := hδR (ball_subset_ball (min_le_left _ _) hy)
    rw [model_eq] at hyM
    rcases hyM with hyS | hyC
    · exact absurd (Or.inl hyS) hyR
    · obtain ⟨⟨b, j⟩, hy'⟩ := mem_iUnion.1 hyC
      by_cases hbj : (b, j) = (a, k)
      · simp only [Prod.mk.injEq] at hbj
        rw [← hbj.1, ← hbj.2]; exact hy'
      · exact absurd (Or.inr (mem_iUnion.2 ⟨⟨(b, j), hbj⟩, hy'⟩)) hyR
  refine ⟨Subtype.val ⁻¹' W, (isOpen_ball.preimage continuous_subtype_val).mem_nhds
    (mem_ball_self hδ), fun γ hγ => ?_⟩
  -- radial projection from the centre `(uₐ, ρ)` of the circle retracts `W` onto it
  refine homotopic_refl_of_radial_retraction (c := (D.u a, ρ)) hρ (convex_ball _ δ)
    (fun y hy => sq_add_sq_pos_of_dist_lt (D.mem_circle_iff.1 hx)
      ((mem_ball.1 hy).trans_le (min_le_right _ _)))
    (fun y hy => D.ear_subset_model a (D.circle_subset_ear a k (D.mem_circle_iff.2 hy)))
    (fun y hy hyM => D.mem_circle_iff.1 (hWM y hy hyM)) γ fun t => hγ (mem_range_self t)

/-- **Non-wild points.** For compact `K`, every point of the model at which arbitrarily small
essential loops are based is an attachment point. -/
theorem loopWildSet_subset_range_incl [CompactSpace K] :
    loopWildSet D.model ⊆ range D.incl := by
  intro x hx
  by_contra hxr
  suffices ∃ U ∈ 𝓝 x, ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x) by
    obtain ⟨U, hU, h⟩ := this
    obtain ⟨γ, hγU, hγ⟩ := hx U hU
    exact hγ (h γ hγU)
  rcases x.2 with hs | he
  · exact D.exists_nhds_homotopic_refl_of_mem_seg hs hxr
  · obtain ⟨a, ha⟩ := mem_iUnion.1 he
    obtain ⟨k, hk⟩ := D.mem_ear_iff.1 ha
    exact D.exists_nhds_homotopic_refl_of_mem_circle hk fun h => hxr ⟨a, Subtype.ext h.symm⟩

/-! ### One-dimensionality -/

/-- Points of the model lie in the closed upper half-plane. -/
lemma snd_nonneg {y : ℝ × ℝ} (hy : y ∈ D.model) : 0 ≤ y.2 := by
  rcases hy with hy | hy
  · exact le_of_eq (hy.2 : y.2 = 0).symm
  · obtain ⟨b, hb⟩ := mem_iUnion.1 hy
    obtain ⟨k, hk⟩ := D.mem_ear_iff.1 hb
    exact (D.circle_bounds hk).1

open Classical in
/-- The projection of the model onto the axis: a point of the earring at `b` goes to the
abscissa `u_b` of its attachment point, a point of the segment to its abscissa. (Defined on all
of `ℝ²`; only its values on the model matter.) -/
def proj (y : ℝ × ℝ) : ℝ :=
  if h : ∃ b, y ∈ D.ear b ∧ 0 < y.2 then D.u h.choose else y.1

/-- On the axis (and below it), `proj` is the abscissa. -/
lemma proj_of_not_pos {y : ℝ × ℝ} (h : ¬ 0 < y.2) : D.proj y = y.1 := by
  rw [proj, dite_eq_right (fun ⟨_, _, h'⟩ => h h')]

/-- On the segment, `proj` is the abscissa. -/
lemma proj_of_mem_seg {y : ℝ × ℝ} (hy : y ∈ D.seg) : D.proj y = y.1 :=
  D.proj_of_not_pos (by rw [(hy.2 : y.2 = 0)]; exact lt_irrefl 0)

/-- On the earring at `b`, `proj` is the abscissa `u_b` of the attachment point. -/
lemma proj_of_mem_ear {b : K} {y : ℝ × ℝ} (hy : y ∈ D.ear b) : D.proj y = D.u b := by
  by_cases h2 : 0 < y.2
  · have h : ∃ b, y ∈ D.ear b ∧ 0 < y.2 := ⟨b, hy, h2⟩
    rw [proj, dite_eq_left h]
    by_contra hne
    have hb : h.choose ≠ b := fun e => hne (by rw [e])
    exact Set.disjoint_left.1 (D.disjoint_ear hb) h.choose_spec.1 hy
  · rw [D.proj_of_not_pos h2]
    obtain ⟨k, hk⟩ := D.mem_ear_iff.1 hy
    have h0 : y.2 = 0 := le_antisymm (not_lt.1 h2) (D.circle_bounds hk).1
    exact (congrArg Prod.fst (D.eq_base_of_mem_ear hy h0)).trans rfl

/-- `proj` takes values in `[-L, L]` on the model. -/
lemma abs_proj_le {y : ℝ × ℝ} (hy : y ∈ D.model) : |D.proj y| ≤ D.L := by
  rcases hy with hy | hy
  · rw [D.proj_of_mem_seg hy]; exact abs_le.2 hy.1
  · obtain ⟨b, hb⟩ := mem_iUnion.1 hy
    rw [D.proj_of_mem_ear hb]; exact D.abs_u_le b

/-- A point of the model at height `y₂` is within `√(2 y₂)` of `proj y` horizontally (the
earrings lie in discs tangent to the axis, of radius at most `1`). -/
lemma sq_proj_sub_fst_le {y : ℝ × ℝ} (hy : y ∈ D.model) : (D.proj y - y.1) ^ 2 ≤ 2 * y.2 := by
  rcases hy with hy | hy
  · rw [D.proj_of_mem_seg hy, sub_self, (hy.2 : y.2 = 0)]; norm_num
  · obtain ⟨b, hb⟩ := mem_iUnion.1 hy
    obtain ⟨k, hk⟩ := D.mem_ear_iff.1 hb
    obtain ⟨h0, -, -, h⟩ := D.circle_bounds hk
    rw [D.proj_of_mem_ear hb]
    have := D.s_le_one b
    nlinarith [sq_nonneg (D.u b - y.1), mul_nonneg h0 (sub_nonneg.2 this), mul_nonneg h0 h0]

/-- `proj` is continuous on the model: it is locally constant off the axis (near a point of the
earring at `a` above the axis the model is that earring), and near a point `(t, 0)` of the axis
it is close to the abscissa by `sq_proj_sub_fst_le`. -/
lemma continuous_proj : Continuous fun z : D.model => D.proj z := by
  rw [Metric.continuous_iff]
  intro y ε hε
  rcases (D.snd_nonneg y.2).lt_or_eq with hy | hy
  · -- off the axis `proj` is locally constant
    obtain ⟨a, ha⟩ : ∃ a, (y : ℝ × ℝ) ∈ D.ear a := by
      rcases y.2 with h | h
      · exact (hy.ne' h.2).elim
      · exact mem_iUnion.1 h
    have hyR : (y : ℝ × ℝ) ∉ D.rest a := by
      rintro (h | h)
      · exact hy.ne' h.2
      · obtain ⟨⟨b, hb⟩, h⟩ := mem_iUnion.1 h
        exact Set.disjoint_left.1 (D.disjoint_ear hb) h ha
    obtain ⟨δ, hδ, hδR⟩ := Metric.isOpen_iff.1 (D.isClosed_rest a).isOpen_compl _ hyR
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have hzR : (z : ℝ × ℝ) ∉ D.rest a := hδR (show dist (z : ℝ × ℝ) y < δ from hz)
    have hza : (z : ℝ × ℝ) ∈ D.ear a := (D.model_subset_ear_union_rest a z.2).resolve_right hzR
    rw [D.proj_of_mem_ear hza, D.proj_of_mem_ear ha, dist_self]
    exact hε
  · -- on the axis
    have hπy : D.proj y = (y : ℝ × ℝ).1 := D.proj_of_not_pos (by rw [← hy]; exact lt_irrefl 0)
    refine ⟨min (ε / 2) (ε ^ 2 / 8), lt_min (half_pos hε) (by positivity), fun z hz => ?_⟩
    have hz1 : |(z : ℝ × ℝ).1 - (y : ℝ × ℝ).1| < ε / 2 :=
      (abs_fst_sub_le_dist _ _).trans_lt (hz.trans_le (min_le_left _ _))
    have hz2 : |(z : ℝ × ℝ).2 - (y : ℝ × ℝ).2| < ε ^ 2 / 8 :=
      (abs_snd_sub_le_dist _ _).trans_lt (hz.trans_le (min_le_right _ _))
    rw [← hy, sub_zero, abs_of_nonneg (D.snd_nonneg z.2)] at hz2
    have hsq := D.sq_proj_sub_fst_le z.2
    have h3 : |D.proj z - (z : ℝ × ℝ).1| < ε / 2 :=
      abs_lt_of_sq_lt_sq (by nlinarith) (by positivity)
    rw [Real.dist_eq, hπy]
    calc |D.proj z - (y : ℝ × ℝ).1|
        ≤ |D.proj z - (z : ℝ × ℝ).1| + |(z : ℝ × ℝ).1 - (y : ℝ × ℝ).1| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h3 hz1
      _ = ε := add_halves ε

/-- A circle of the model meets a sup-metric sphere in finitely many points. -/
lemma finite_inter_sphere_circle (a : K) (k : ℕ) (x : ℝ × ℝ) (ρ : ℝ) :
    (D.circle a k ∩ sphere x ρ).Finite :=
  (Peano.finite_circle_inter_sphere (D.u a, D.s a * earringRadius k)
    (D.s a * earringRadius k) x ρ).subset fun _ hy => ⟨D.mem_circle_iff.1 hy.1, hy.2⟩

/-- The frontier of the neighbourhood `proj⁻¹ (c₁, c₂) ∩ ball x ρ` is finite, provided `c₁, c₂`
are not attachment abscissae, the sphere `sphere x ρ` misses the segment over `[c₁, c₂]`, and
only finitely many circles attached over `[c₁, c₂]` meet it. The frontier lies in
`proj⁻¹ {c₁, c₂} = {(c₁, 0), (c₂, 0)}` together with the points of `sphere x ρ` over `[c₁, c₂]`. -/
private lemma finite_frontier_aux {x : D.model} {ρ c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (hc₁ : c₁ ∉ range D.u) (hc₂ : c₂ ∉ range D.u)
    (hseg : ∀ y ∈ D.seg, y.1 ∈ Icc c₁ c₂ → dist y (x : ℝ × ℝ) ≠ ρ)
    (hcirc : {i : K × ℕ | ∃ y ∈ D.circle i.1 i.2,
      D.u i.1 ∈ Icc c₁ c₂ ∧ dist y (x : ℝ × ℝ) = ρ}.Finite) :
    (frontier ((fun z : D.model => D.proj z) ⁻¹' Ioo c₁ c₂ ∩ ball x ρ)).Finite := by
  have hπ := D.continuous_proj
  have h1 : frontier ((fun z : D.model => D.proj z) ⁻¹' Ioo c₁ c₂ ∩ ball x ρ) ⊆
      {z | D.proj z = c₁ ∨ D.proj z = c₂} ∪ {z | D.proj z ∈ Icc c₁ c₂ ∧ dist z x = ρ} := by
    refine (frontier_inter_subset _ _).trans (union_subset_union ?_ ?_)
    · refine inter_subset_left.trans ((hπ.frontier_preimage_subset _).trans ?_)
      rw [frontier_Ioo hc]
      intro z hz
      simpa using hz
    · rintro z ⟨hz1, hz2⟩
      exact ⟨closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage hπ) hz1,
        dist_eq_of_mem_frontier_ball hz2⟩
  refine Finite.subset (Finite.union ?_ ?_) h1
  · refine ((toFinite ({(c₁, 0), (c₂, 0)} : Set (ℝ × ℝ))).preimage
      Subtype.val_injective.injOn).subset fun z hz => ?_
    have hzs : (z : ℝ × ℝ) ∈ D.seg := by
      rcases z.2 with h | h
      · exact h
      · obtain ⟨b, hb⟩ := mem_iUnion.1 h
        rcases hz with hz | hz <;> rw [D.proj_of_mem_ear hb] at hz
        · exact (hc₁ ⟨b, hz⟩).elim
        · exact (hc₂ ⟨b, hz⟩).elim
    have h2 : (z : ℝ × ℝ).2 = 0 := hzs.2
    rcases hz with hz | hz <;> rw [D.proj_of_mem_seg hzs] at hz
    · exact Or.inl (Prod.ext hz h2)
    · exact Or.inr (Prod.ext hz h2)
  · refine ((hcirc.biUnion fun i _ => D.finite_inter_sphere_circle i.1 i.2 (x : ℝ × ℝ) ρ).preimage
      Subtype.val_injective.injOn).subset fun z hz => ?_
    obtain ⟨hz1, hz2⟩ := hz
    rcases z.2 with h | h
    · exact (hseg _ h (by rwa [D.proj_of_mem_seg h] at hz1) hz2).elim
    · obtain ⟨b, hb⟩ := mem_iUnion.1 h
      obtain ⟨k, hk⟩ := D.mem_ear_iff.1 hb
      rw [D.proj_of_mem_ear hb] at hz1
      exact mem_iUnion₂.2 ⟨(b, k), ⟨z, hk, hz1, hz2⟩, hk, hz2⟩

/-- **The model is at most one-dimensional.** It is rim-finite
(`coveringDimLE_one_of_finite_frontier`): a point `x` has the neighbourhoods
`proj⁻¹ (c₁, c₂) ∩ ball x ρ` with finite frontier (`finite_frontier_aux`). Off the axis, take
`ρ < x₂ / 4` and `(c₁, c₂) ⊇ [-L, L]`: only the finitely many circles reaching height `x₂ / 2`
can meet the sphere. On the axis, `x = (t, 0)`, take `ρ` small and `c₁ < t < c₂` within `ρ / 2`
of `t` and off the countably many attachment abscissae: then only the finitely many circles not
within `ρ / 4` of their attachment point can meet the sphere. -/
theorem coveringDimLE_model [Countable K] : CoveringDimLE 1 D.model := by
  refine coveringDimLE_one_of_finite_frontier fun x N hN => ?_
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  suffices ∃ ρ ∈ Ioo 0 r, ∃ c₁ c₂, c₁ < D.proj x ∧ D.proj x < c₂ ∧ c₁ ∉ range D.u ∧
      c₂ ∉ range D.u ∧ (∀ y ∈ D.seg, y.1 ∈ Icc c₁ c₂ → dist y (x : ℝ × ℝ) ≠ ρ) ∧
      {i : K × ℕ | ∃ y ∈ D.circle i.1 i.2,
        D.u i.1 ∈ Icc c₁ c₂ ∧ dist y (x : ℝ × ℝ) = ρ}.Finite by
    obtain ⟨ρ, hρ, c₁, c₂, h1, h2, hc₁, hc₂, hseg, hcirc⟩ := this
    exact ⟨_, (isOpen_Ioo.preimage D.continuous_proj).inter isOpen_ball,
      ⟨⟨h1, h2⟩, mem_ball_self hρ.1⟩,
      inter_subset_right.trans ((ball_subset_ball hρ.2.le).trans hrN),
      D.finite_frontier_aux (h1.trans h2) hc₁ hc₂ hseg hcirc⟩
  rcases (D.snd_nonneg x.2).lt_or_eq with hx2 | hx2
  · -- off the axis
    set ρ := min (r / 2) ((x : ℝ × ℝ).2 / 4) with hρ_def
    have hρ0 : 0 < ρ := lt_min (half_pos hr) (by linarith)
    have hρx : ρ ≤ (x : ℝ × ℝ).2 / 4 := min_le_right _ _
    have hπ := abs_le.1 (D.abs_proj_le x.2)
    have hu : ∀ c, D.L < |c| → c ∉ range D.u := fun c hc ⟨a, ha⟩ => by
      have := D.abs_u_le a; rw [ha] at this; linarith
    refine ⟨ρ, ⟨hρ0, (min_le_left _ _).trans_lt (half_lt_self hr)⟩, -D.L - 1, D.L + 1,
      by linarith, by linarith, hu _ ?_, hu _ ?_, fun y hy _ hd => ?_, ?_⟩
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
    · have h0 : y.2 = 0 := hy.2
      have := abs_snd_sub_le_dist y x
      rw [hd, h0] at this
      have := neg_le_abs (0 - (x : ℝ × ℝ).2)
      linarith
    · refine (D.finite_circle_not_small (ε := (x : ℝ × ℝ).2 / 2) (by linarith)).subset ?_
      intro i hi
      obtain ⟨y, hy, -, hd⟩ := hi
      intro hsub
      have h1 : dist y (D.base i.1) ≤ (x : ℝ × ℝ).2 / 2 := hsub hy
      have h2 := abs_snd_sub_le_dist y (D.base i.1)
      have h3 := abs_snd_sub_le_dist y x
      have hb : (D.base i.1).2 = 0 := rfl
      rw [hb, sub_zero] at h2
      rw [hd] at h3
      have := le_abs_self y.2
      have := neg_le_abs (y.2 - (x : ℝ × ℝ).2)
      linarith
  · -- on the axis
    have hπx : D.proj x = (x : ℝ × ℝ).1 := D.proj_of_not_pos (by rw [← hx2]; exact lt_irrefl 0)
    set t := (x : ℝ × ℝ).1 with ht
    set ρ := r / 2 with hρ_def
    have hρ0 : 0 < ρ := half_pos hr
    obtain ⟨c₁, hc₁, hc₁'⟩ := ((countable_range D.u).dense_compl ℝ).exists_between
      (show t - ρ / 2 < t by linarith)
    obtain ⟨c₂, hc₂, hc₂'⟩ := ((countable_range D.u).dense_compl ℝ).exists_between
      (show t < t + ρ / 2 by linarith)
    have hnear : ∀ v ∈ Icc c₁ c₂, dist ((v, 0) : ℝ × ℝ) (x : ℝ × ℝ) < ρ / 2 := by
      intro v hv
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      dsimp only
      rw [← hx2, sub_self, abs_zero]
      exact max_lt (abs_lt.2 ⟨by linarith [hv.1, hc₁'.1], by linarith [hv.2, hc₂'.2]⟩)
        (by linarith)
    refine ⟨ρ, ⟨hρ0, half_lt_self hr⟩, c₁, c₂, by rw [hπx]; exact hc₁'.2, by rw [hπx]; exact hc₂'.1,
      hc₁, hc₂,
      fun y hy hy1 hd => ?_, ?_⟩
    · have hy' : y = (y.1, 0) := Prod.ext rfl (hy.2 : y.2 = 0)
      have := hnear y.1 hy1
      rw [← hy', hd] at this
      linarith
    · refine (D.finite_circle_not_small (ε := ρ / 4) (by linarith)).subset ?_
      intro i hi
      obtain ⟨y, hy, hu, hd⟩ := hi
      intro hsub
      have h1 : dist y (D.base i.1) ≤ ρ / 4 := hsub hy
      have h2 : dist (D.base i.1) (x : ℝ × ℝ) < ρ / 2 := hnear _ hu
      linarith [dist_triangle y (D.base i.1) (x : ℝ × ℝ)]

end ModelData

/-! ### The models `A_K` -/

section Models

variable (K : Type*) [MetricSpace K] [CompactSpace K] [Countable K]

/-- A fixed choice of model data for `K`. -/
def modelData : ModelData K := Classical.choice (nonempty_modelData K)

/-- **The model `A_K ⊆ ℝ²`** of a countable compact metric space `K`: a segment of the horizontal
axis with a scaled copy of the earring attached at the image of every point of `K` under an
embedding `K ↪ ℝ`. -/
def modelSet : Set (ℝ × ℝ) := (modelData K).model

/-- `A_K` is compact. -/
theorem isCompact_modelSet : IsCompact (modelSet K) := (modelData K).isCompact_model

/-- `A_K` has empty interior in `ℝ²`. -/
theorem interior_modelSet : interior (modelSet K) = ∅ := (modelData K).interior_model

/-- `A_K` is a compact space. -/
instance compactSpace_modelSet : CompactSpace (modelSet K) := (modelData K).compactSpace_model

/-- `A_K` is connected (for non-empty `K`). -/
instance connectedSpace_modelSet [Nonempty K] : ConnectedSpace (modelSet K) :=
  (modelData K).connectedSpace_model

/-- `A_K` is locally path-connected. -/
instance locallyPathConnectedSpace_modelSet : LocallyPathConnectedSpace (modelSet K) :=
  (modelData K).locallyPathConnectedSpace_model

/-- `A_K` is at most one-dimensional. -/
theorem coveringDimLE_modelSet : CoveringDimLE 1 (modelSet K) :=
  (modelData K).coveringDimLE_model

/-- The embedding `K ↪ A_K` onto the attachment points of the earrings. -/
def modelIncl : K → modelSet K := (modelData K).incl

/-- `modelIncl K` is a topological embedding. -/
theorem isEmbedding_modelIncl : Topology.IsEmbedding (modelIncl K) :=
  (modelData K).isEmbedding_incl

/-- The points of `K` are wild in `A_K`. -/
theorem range_modelIncl_subset_wildSet : range (modelIncl K) ⊆ wildSet (modelSet K) :=
  (modelData K).range_incl_subset_wildSet

/-- Only the points of `K` can be loop-wild in `A_K`. -/
theorem loopWildSet_modelSet_subset_range : loopWildSet (modelSet K) ⊆ range (modelIncl K) :=
  (modelData K).loopWildSet_subset_range_incl

end Models

/-- **Surjectivity half of Theorem 1.2 (as corrected).** Every non-empty countable compact metric
space `K` is realised, up to the comparison `wildSet ⊆ loopWildSet`, as the wild set of a
one-dimensional Peano continuum in the plane: there is a compact, connected, locally
path-connected planar set `A` with empty interior and `CoveringDimLE 1`, and an embedding
`ι : K → A` with `range ι ⊆ wildSet A` and `loopWildSet A ⊆ range ι`. -/
theorem exists_model (K : Type*) [MetricSpace K] [CompactSpace K] [Countable K] [Nonempty K] :
    ∃ A : Set (ℝ × ℝ), IsCompact A ∧ interior A = ∅ ∧ ConnectedSpace A ∧
      LocallyPathConnectedSpace A ∧ CoveringDimLE 1 A ∧
      ∃ ι : K → A, Topology.IsEmbedding ι ∧ range ι ⊆ wildSet A ∧ loopWildSet A ⊆ range ι :=
  ⟨modelSet K, isCompact_modelSet K, interior_modelSet K, inferInstance, inferInstance,
    coveringDimLE_modelSet K, modelIncl K, isEmbedding_modelIncl K,
    range_modelIncl_subset_wildSet K, loopWildSet_modelSet_subset_range K⟩

end Peano
