module

public import Peano.Defs
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Tactic.IntervalCases

/-!
# The infinite earring: geometry, gluing, sub-earrings, essential loops

Infrastructure about `Peano.earring` used by the later files.

* **Geometry.** The circles `Cₖ = earringCircle k` are closed, two distinct circles meet only at
  `b₀ = (0, 0)`, the earring is compact, and the loops `ℓₖ = earringLoop k` shrink to `b₀`
  (`loopsShrinkTo_earringLoop`). Away from `b₀` the circles are locally finite: `Cₖ ∖ {b₀}` is
  open in the earring (`isOpen_preimage_earringCircle_diff`).
* **Shrinking loop families.** `LoopsShrinkTo y γ`: every neighbourhood of `y` contains the image
  of `γ k` for all large `k`; the hypothesis of the gluing lemma.
* **Gluing lemma.** For any topological space `Y` (no metric, no separation axiom), a point `y` and
  loops `γ k : Path y y` with `LoopsShrinkTo y γ`, `earringMap y γ h : C(earring, Y)` sends `b₀` to
  `y` and `ℓₖ(t)` to `γ k t` (`earringMap_base`, `earringMap_earringLoop`,
  `earringLoop_map_earringMap`), and is the unique such map (`earringMap_unique`). Conversely the
  loops `f ∘ ℓₖ` of any map `f` shrink to `f b₀` (`loopsShrinkTo_map_earringLoop`).
* **Sub-earrings.** `earringSub ν hν` sends `ℓₖ` to `ℓ_{ν k}` when `ν → ∞`; precomposition with it
  preserves full essentiality (`FullyEssential.comp_earringSub`).
* **Casts.** `homotopic_cast_iff`: casting the end points of two paths (`Path.cast`) does not change
  whether they are homotopic; `cast_homotopic_refl_iff` is the case of the constant loop.
* **Essential loops.** No `ℓₖ` is null-homotopic (`earringLoop_not_homotopic_refl`), so the
  identity is fully essential and `b₀ ∈ w(𝔼)`.

## Design

The gluing map is not defined circle by circle. Instead the earring is presented as a quotient of
the compact space `OnePoint ℕ × I` (`ℕ` with a point `∞` added, times the unit interval) by
`earringPre : (k, t) ↦ ℓₖ(t)`, `(∞, t) ↦ b₀`, which is continuous (the loops shrink),
surjective, and a closed map (compact to Hausdorff), hence a quotient map. A family of shrinking
loops `γ` gives the continuous map `earringMapAux y γ : (k, t) ↦ γ k t`, `(∞, t) ↦ y` on
`OnePoint ℕ × I` (continuity at `∞` is exactly the shrinking hypothesis), which is constant on the
fibres of `earringPre` (the parametrisation of `Cₖ` is injective on `(0, 1)` and the circles meet
only at `b₀`); `earringMap` is its descent. This needs no topological assumption on `Y`, and no
homeomorphism `Cₖ ≃ S¹`. `earringPre` and `earringMapAux` are implementation details: they stay
public only because the body of `earringMap` mentions them, and all their lemmas are private.

Sub-earring maps and the "winding" maps `earringWind k : 𝔼 → ℝ/ℤ` (the circle `Cₖ` once around,
all other circles to the base point) are instances of the gluing lemma. Essentiality of `ℓₖ` is
then read off from Mathlib's winding number on `AddCircle 1`: `earringWind k ∘ ℓₖ` is the loop
`unitAddCircleLoop = AddCircle.zsmulLoop 1 0 1`, of winding number `1`, whereas the constant loop
has winding number `0`.
-/

@[expose] public section

open Set Filter Topology unitInterval OnePoint

noncomputable section

namespace Peano

/-! ### Geometry of the circles -/

/-- The radii are positive. -/
lemma earringRadius_pos (k : ℕ) : 0 < earringRadius k := by
  unfold earringRadius; positivity

/-- Distinct circles have distinct radii. -/
lemma earringRadius_injective : Function.Injective earringRadius := by
  intro j k h
  simp only [earringRadius, one_div, inv_inj, add_left_inj, Nat.cast_inj] at h
  exact h

/-- The equation of `Cₖ` in the form `x² + y² = 2 rₖ x`. -/
lemma mem_earringCircle_iff {k : ℕ} {p : ℝ × ℝ} :
    p ∈ earringCircle k ↔ p.1 ^ 2 + p.2 ^ 2 = 2 * earringRadius k * p.1 := by
  simp only [earringCircle, mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-- Each circle of the earring is closed in `ℝ²`. -/
lemma isClosed_earringCircle (k : ℕ) : IsClosed (earringCircle k) :=
  isClosed_eq (by fun_prop) (by fun_prop)

/-- The base point lies on every circle. -/
lemma zero_mem_earringCircle (k : ℕ) : ((0, 0) : ℝ × ℝ) ∈ earringCircle k := by
  simp [earringCircle]

/-- Two distinct circles of the earring meet exactly at the base point `(0, 0)`. -/
lemma earringCircle_inter_earringCircle {j k : ℕ} (hjk : j ≠ k) :
    earringCircle j ∩ earringCircle k = {(0, 0)} := by
  refine subset_antisymm ?_ (by simp [zero_mem_earringCircle])
  rintro ⟨x, y⟩ ⟨hj, hk⟩
  rw [mem_earringCircle_iff] at hj hk
  have hr : earringRadius j ≠ earringRadius k := earringRadius_injective.ne hjk
  have hx : x = 0 := by
    have : (earringRadius j - earringRadius k) * x = 0 := by simp only at hj hk; linarith
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hr)
  subst hx
  have hy : y = 0 := by simp only at hj; nlinarith
  simp [hy]

/-- `earringParam k t` lies on the circle `Cₖ`. -/
lemma earringParam_mem_earringCircle (k : ℕ) (t : ℝ) : earringParam k t ∈ earringCircle k := by
  simp only [earringCircle, earringParam, mem_ofPred_eq]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t)]

/-- The points of `Cₖ` are within (sup-)distance `2 rₖ` of the base point. -/
lemma dist_earringParam_le (k : ℕ) (t : ℝ) :
    dist (earringParam k t) ((0, 0) : ℝ × ℝ) ≤ 2 * earringRadius k := by
  have hr := earringRadius_pos k
  have h1 := Real.neg_one_le_cos (2 * Real.pi * t)
  have h2 := Real.cos_le_one (2 * Real.pi * t)
  have h3 := Real.neg_one_le_sin (2 * Real.pi * t)
  have h4 := Real.sin_le_one (2 * Real.pi * t)
  rw [Prod.dist_eq]
  simp only [earringParam, Real.dist_eq, sub_zero]
  refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> nlinarith

/-- The parametrisation starts at the base point. -/
@[simp] lemma earringParam_zero (k : ℕ) : earringParam k 0 = (0, 0) := by
  simp [earringParam]

/-- The parametrisation ends at the base point. -/
@[simp] lemma earringParam_one (k : ℕ) : earringParam k 1 = (0, 0) := by
  simp [earringParam]

/-- On `[0, 1]`, the parametrisation of `Cₖ` hits the base point only at the end points. -/
lemma earringParam_eq_zero {k : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (h : earringParam k t = (0, 0)) : t = 0 ∨ t = 1 := by
  have hr := earringRadius_pos k
  have hc : Real.cos (2 * Real.pi * t) = 1 := by
    have := congrArg Prod.fst h
    simp only [earringParam] at this
    have : earringRadius k * (1 - Real.cos (2 * Real.pi * t)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hr.ne'
    linarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hc
  have htn : t = n := by
    have := Real.pi_pos
    field_simp at hn
    nlinarith
  rw [htn] at ht ⊢
  have h0 : (0 : ℤ) ≤ n := by exact_mod_cast ht.1
  have h1 : n ≤ 1 := by exact_mod_cast ht.2
  interval_cases n <;> simp

/-- On `[0, 1]`, the parametrisation of `Cₖ` is injective away from the base point. -/
lemma earringParam_injOn {k : ℕ} {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (h : earringParam k s = earringParam k t) (h0 : earringParam k s ≠ (0, 0)) : s = t := by
  have hr := earringRadius_pos k
  have hc : Real.cos (2 * Real.pi * s) = Real.cos (2 * Real.pi * t) := by
    have := congrArg Prod.fst h
    simp only [earringParam] at this
    have : earringRadius k * (Real.cos (2 * Real.pi * t) - Real.cos (2 * Real.pi * s)) = 0 := by
      linarith
    have := (mul_eq_zero.1 this).resolve_left hr.ne'
    linarith
  have hsn : Real.sin (2 * Real.pi * s) = Real.sin (2 * Real.pi * t) := by
    have := congrArg Prod.snd h
    simp only [earringParam] at this
    exact mul_left_cancel₀ hr.ne' this
  have hcos : Real.cos (2 * Real.pi * s - 2 * Real.pi * t) = 1 := by
    rw [Real.cos_sub, ← hc, ← hsn]
    nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * s)]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos
  have hstn : s - t = n := by
    have := Real.pi_pos
    field_simp at hn
    nlinarith
  have h1 : (-1 : ℤ) ≤ n := by
    have : (-1 : ℝ) ≤ n := by rw [← hstn]; linarith [hs.1, ht.2]
    exact_mod_cast this
  have h2 : n ≤ 1 := by
    have : (n : ℝ) ≤ 1 := by rw [← hstn]; linarith [hs.2, ht.1]
    exact_mod_cast this
  interval_cases n
  · exfalso
    have hs0 : s = 0 := by simp at hstn; linarith [hs.1, ht.2]
    exact h0 (by rw [hs0, earringParam_zero])
  · simp at hstn; linarith
  · exfalso
    have hs1 : s = 1 := by simp at hstn; linarith [hs.2, ht.1]
    exact h0 (by rw [hs1, earringParam_one])

/-- Every point of `Cₖ` is `earringParam k t` for some `t ∈ [0, 1]`. -/
lemma exists_earringParam_eq {k : ℕ} {p : ℝ × ℝ} (hp : p ∈ earringCircle k) :
    ∃ t ∈ Icc (0 : ℝ) 1, earringParam k t = p := by
  set r := earringRadius k with hr_def
  have hr : 0 < r := earringRadius_pos k
  have hp' : (p.1 - r) ^ 2 + p.2 ^ 2 = r ^ 2 := hp
  set z : ℂ := ⟨(r - p.1) / r, p.2 / r⟩ with hz_def
  have hnorm : ‖z‖ = 1 := by
    have : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      field_simp
      nlinarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) two_ne_zero).1 this
  have hz : z ≠ 0 := by
    intro h
    simp [h] at hnorm
  have hcos : Real.cos (Complex.arg z) = (r - p.1) / r := by
    rw [Complex.cos_arg hz, hnorm, div_one]
  have hsin : Real.sin (Complex.arg z) = p.2 / r := by
    rw [Complex.sin_arg, hnorm, div_one]
  have key : ∀ t : ℝ, Real.cos (2 * Real.pi * t) = Real.cos (Complex.arg z) →
      Real.sin (2 * Real.pi * t) = Real.sin (Complex.arg z) → earringParam k t = p := by
    intro t hc hs
    ext
    · simp only [earringParam, ← hr_def, hc, hcos]
      field_simp
      ring
    · simp only [earringParam, ← hr_def, hs, hsin]
      field_simp
  have h1 := Complex.neg_pi_lt_arg z
  have h2 := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  by_cases h0 : 0 ≤ Complex.arg z
  · refine ⟨Complex.arg z / (2 * Real.pi), ⟨by positivity, ?_⟩, key _ ?_ ?_⟩
    · rw [div_le_one (by positivity)]; linarith
    · congr 1; field_simp
    · congr 1; field_simp
  · rw [not_le] at h0
    have he : 2 * Real.pi * (Complex.arg z / (2 * Real.pi) + 1) =
        Complex.arg z + 2 * Real.pi := by
      field_simp
    refine ⟨Complex.arg z / (2 * Real.pi) + 1, ⟨?_, ?_⟩, key _ ?_ ?_⟩
    · have : -1 / 2 < Complex.arg z / (2 * Real.pi) := by
        rw [lt_div_iff₀ (by positivity)]; linarith
      linarith
    · have : Complex.arg z / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos h0 (by positivity)
      linarith
    · rw [he, Real.cos_add_two_pi]
    · rw [he, Real.sin_add_two_pi]

/-! ### Shrinking loop families -/

/-- The loops `γ k` *shrink to* `y`: every neighbourhood of `y` contains the image of `γ k` for
all large `k`. This is the hypothesis of the gluing lemma `earringMap`. (An `abbrev`, so that a
proof of it can be applied directly to a neighbourhood.) -/
abbrev LoopsShrinkTo {Y : Type*} [TopologicalSpace Y] (y : Y) (γ : ℕ → Path y y) : Prop :=
  ∀ U ∈ 𝓝 y, ∀ᶠ k in atTop, range (γ k) ⊆ U

/-- The earring loops shrink to the base point: every neighbourhood of `b₀` contains `ℓₖ(I)` for
all large `k`. -/
theorem loopsShrinkTo_earringLoop : LoopsShrinkTo earringBase earringLoop := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  have : Tendsto (fun k : ℕ => 2 * earringRadius k) atTop (𝓝 0) := by
    simpa [earringRadius] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  filter_upwards [this.eventually (gt_mem_nhds hε)] with k hk
  rintro _ ⟨t, rfl⟩
  apply hball
  rw [Metric.mem_ball, Subtype.dist_eq]
  exact (dist_earringParam_le k t).trans_lt hk

/-! ### Loop families on `OnePoint ℕ × I` -/

variable {Y : Type*} [TopologicalSpace Y]

/-- The map `OnePoint ℕ × I → Y` assembled from a family of loops at `y`:
`(k, t) ↦ γ k t` and `(∞, t) ↦ y`. -/
def earringMapAux (y : Y) (γ : ℕ → Path y y) (p : OnePoint ℕ × I) : Y :=
  p.1.elim y (fun k => γ k p.2)

/-- `earringMapAux y γ (k, t) = γ k t`. -/
@[simp] private lemma earringMapAux_coe (y : Y) (γ : ℕ → Path y y) (k : ℕ) (t : I) :
    earringMapAux y γ ((k : OnePoint ℕ), t) = γ k t := rfl

/-- `earringMapAux y γ (∞, t) = y`. -/
@[simp] private lemma earringMapAux_infty (y : Y) (γ : ℕ → Path y y) (t : I) :
    earringMapAux y γ (∞, t) = y := rfl

/-- If the loops `γ k` shrink to `y`, the assembled map `earringMapAux y γ` is continuous. -/
private theorem continuous_earringMapAux {y : Y} {γ : ℕ → Path y y}
    (h : LoopsShrinkTo y γ) : Continuous (earringMapAux y γ) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, t⟩
  induction a using OnePoint.rec with
  | infty =>
    intro U hU
    rw [nhds_prod_eq, OnePoint.nhds_infty_eq, sup_prod, mem_map, mem_sup]
    constructor
    · have hev : ∀ᶠ a in map ((↑) : ℕ → OnePoint ℕ) (coclosedCompact ℕ),
          ∀ s : I, earringMapAux y γ (a, s) ∈ U := by
        rw [eventually_map, coclosedCompact_eq_cocompact, cocompact_eq_cofinite,
          Nat.cofinite_eq_atTop]
        filter_upwards [h U hU] with k hk s
        exact hk ⟨s, rfl⟩
      exact (hev.prod_inl _).mono fun p hp => hp p.2
    · have hev : ∀ᶠ a in pure (∞ : OnePoint ℕ), ∀ s : I, earringMapAux y γ (a, s) ∈ U :=
        eventually_pure.2 fun _ => mem_of_mem_nhds hU
      exact (hev.prod_inl _).mono fun p hp => hp p.2
  | coe k =>
    have hk : ∀ᶠ a in 𝓝 (k : OnePoint ℕ), a = (k : OnePoint ℕ) := by
      rw [OnePoint.nhds_coe_eq, nhds_discrete, map_pure]
      exact eventually_pure.2 rfl
    refine ContinuousAt.congr (f := fun p : OnePoint ℕ × I => γ k p.2) (by fun_prop) ?_
    rw [nhds_prod_eq]
    exact (hk.prod_inl _).mono fun p hp => by
      obtain ⟨a, s⟩ := p
      simp only at hp
      simp [hp]

/-! ### The earring as a quotient of `OnePoint ℕ × I` -/

/-- The surjection `OnePoint ℕ × I → 𝔼`, `(k, t) ↦ ℓₖ(t)`, `(∞, t) ↦ b₀`. -/
def earringPre : OnePoint ℕ × I → earring :=
  earringMapAux earringBase earringLoop

/-- `earringPre (k, t) = ℓₖ(t)`. -/
@[simp] private lemma earringPre_coe (k : ℕ) (t : I) :
    earringPre ((k : OnePoint ℕ), t) = earringLoop k t := rfl

/-- `earringPre (∞, t) = b₀`. -/
@[simp] private lemma earringPre_infty (t : I) : earringPre (∞, t) = earringBase := rfl

/-- `earringPre` is continuous, since the earring loops shrink to `b₀`. -/
private lemma continuous_earringPre : Continuous earringPre :=
  continuous_earringMapAux loopsShrinkTo_earringLoop

/-- Every point of the earring is some `ℓₖ(t)`. -/
private lemma surjective_earringPre : Function.Surjective earringPre := by
  rintro ⟨p, hp⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 hp
  obtain ⟨t, ht, rfl⟩ := exists_earringParam_eq hk
  exact ⟨((k : OnePoint ℕ), ⟨t, ht⟩), rfl⟩

/-- The earring is compact. -/
instance : CompactSpace earring :=
  surjective_earringPre.compactSpace continuous_earringPre

/-- The earring is a compact subset of `ℝ²`. -/
lemma isCompact_earring : IsCompact earring :=
  isCompact_iff_compactSpace.2 inferInstance

/-- `earringPre` is a quotient map (continuous surjection from a compact space onto a Hausdorff
space). -/
private lemma isQuotientMap_earringPre : IsQuotientMap earringPre :=
  .of_surjective_continuous surjective_earringPre continuous_earringPre

/-- `ℓₖ(t) = b₀` only at the end points `t = 0, 1`. -/
lemma earringLoop_apply_eq_base {k : ℕ} {t : I} (h : earringLoop k t = earringBase) :
    t = 0 ∨ t = 1 := by
  have h' : earringParam k t = (0, 0) := congrArg Subtype.val h
  rcases earringParam_eq_zero t.2 h' with h0 | h1
  · exact .inl (Subtype.ext h0)
  · exact .inr (Subtype.ext h1)

/-- Away from the base point, `ℓₖ(t) = ℓⱼ(s)` with `s, t ∈ I` forces `k = j` and `t = s`. -/
lemma earringLoop_apply_injective {j k : ℕ} {s t : I} (h : earringLoop j s = earringLoop k t)
    (h0 : earringLoop j s ≠ earringBase) : j = k ∧ s = t := by
  have h' : earringParam j s = earringParam k t := congrArg Subtype.val h
  have h0' : earringParam j s ≠ (0, 0) := fun he => h0 (Subtype.ext he)
  have hjk : j = k := by
    by_contra hjk
    have hmem : earringParam j s ∈ earringCircle j ∩ earringCircle k :=
      ⟨earringParam_mem_earringCircle j s, h' ▸ earringParam_mem_earringCircle k t⟩
    rw [earringCircle_inter_earringCircle hjk] at hmem
    exact h0' hmem
  subst hjk
  exact ⟨rfl, Subtype.ext (earringParam_injOn s.2 t.2 h' h0')⟩

/-- Over the base point, `earringMapAux y γ` takes the value `y`. -/
private lemma earringMapAux_eq_of_earringPre_eq_base {y : Y} (γ : ℕ → Path y y) {p : OnePoint ℕ × I}
    (hp : earringPre p = earringBase) : earringMapAux y γ p = y := by
  obtain ⟨a, t⟩ := p
  induction a using OnePoint.rec with
  | infty => rfl
  | coe k =>
    rcases earringLoop_apply_eq_base hp with rfl | rfl <;> simp

/-- `earringMapAux y γ` is constant on the fibres of `earringPre`. -/
private lemma earringMapAux_factorsThrough (y : Y) (γ : ℕ → Path y y) :
    Function.FactorsThrough (earringMapAux y γ) earringPre := by
  intro p q hpq
  by_cases h0 : earringPre p = earringBase
  · rw [earringMapAux_eq_of_earringPre_eq_base γ h0,
      earringMapAux_eq_of_earringPre_eq_base γ (hpq ▸ h0)]
  obtain ⟨a, s⟩ := p
  obtain ⟨b, t⟩ := q
  induction a using OnePoint.rec with
  | infty => exact absurd rfl h0
  | coe j =>
    induction b using OnePoint.rec with
    | infty => exact absurd hpq h0
    | coe k =>
      obtain ⟨rfl, rfl⟩ := earringLoop_apply_injective hpq h0
      rfl

/-! ### The gluing lemma -/

/-- **Gluing lemma.** A family of loops `γ k` at `y` shrinking to `y` defines a map `𝔼 → Y`
sending `b₀ ↦ y` and `ℓₖ(t) ↦ γ k t`. -/
def earringMap (y : Y) (γ : ℕ → Path y y) (h : LoopsShrinkTo y γ) :
    C(earring, Y) :=
  IsQuotientMap.lift (f := ⟨earringPre, by exact continuous_earringPre⟩)
    (by exact isQuotientMap_earringPre) ⟨earringMapAux y γ, by exact continuous_earringMapAux h⟩
    (by exact earringMapAux_factorsThrough y γ)

section earringMap

variable {y : Y} {γ : ℕ → Path y y} (h : LoopsShrinkTo y γ)

/-- The defining property of `earringMap`: `earringMap y γ h ∘ earringPre = earringMapAux y γ`. -/
private lemma earringMap_earringPre (p : OnePoint ℕ × I) :
    earringMap y γ h (earringPre p) = earringMapAux y γ p :=
  DFunLike.congr_fun (IsQuotientMap.lift_comp (f := ⟨earringPre, continuous_earringPre⟩)
    isQuotientMap_earringPre ⟨earringMapAux y γ, continuous_earringMapAux h⟩
    (by exact earringMapAux_factorsThrough y γ)) p

/-- The glued map sends the base point to `y`. -/
@[simp] theorem earringMap_base : earringMap y γ h earringBase = y :=
  earringMap_earringPre h (∞, 0)

/-- The glued map sends `ℓₖ(t)` to `γ k t`. -/
@[simp] theorem earringMap_earringLoop (k : ℕ) (t : I) :
    earringMap y γ h (earringLoop k t) = γ k t :=
  earringMap_earringPre h ((k : OnePoint ℕ), t)

/-- The glued map sends the loop `ℓₖ` to `γ k` (as paths, up to the cast of the end points
along `earringMap_base`). -/
theorem earringLoop_map_earringMap (k : ℕ) :
    (earringLoop k).map (earringMap y γ h).continuous =
      (γ k).cast (earringMap_base h) (earringMap_base h) := by
  ext t
  simp

/-- Uniqueness in the gluing lemma: a map `𝔼 → Y` is determined by its values on the loops. -/
theorem earringMap_unique (f : C(earring, Y)) (hf : ∀ k t, f (earringLoop k t) = γ k t) :
    f = earringMap y γ h := by
  ext p
  obtain ⟨⟨a, t⟩, rfl⟩ := surjective_earringPre p
  induction a using OnePoint.rec with
  | infty =>
    have : earringPre (∞, t) = earringLoop 0 0 := by simp
    rw [this, hf, earringMap_earringLoop]
  | coe k => simp [hf]

end earringMap

/-- Converse of the gluing lemma: for every map `f : 𝔼 → Y`, the loops `f ∘ ℓₖ` shrink to
`f b₀`. -/
theorem loopsShrinkTo_map_earringLoop (f : C(earring, Y)) :
    LoopsShrinkTo (f earringBase) (fun k => (earringLoop k).map f.continuous) := by
  intro U hU
  filter_upwards [loopsShrinkTo_earringLoop _ (f.continuous.continuousAt hU)] with k hk
  rw [Path.map_coe, range_comp]
  exact image_subset_iff.2 hk

/-! ### Local finiteness of the circles away from the base point -/

/-- `Cₖ ∖ {b₀}` (as a subset of the earring) is open in the earring: near a point of `Cₖ` other
than `b₀` the earring consists of `Cₖ` only. -/
theorem isOpen_preimage_earringCircle_diff (k : ℕ) :
    IsOpen (((↑) : earring → ℝ × ℝ) ⁻¹' earringCircle k \ {earringBase}) := by
  rw [← isQuotientMap_earringPre.isOpen_preimage]
  have : earringPre ⁻¹' (((↑) : earring → ℝ × ℝ) ⁻¹' earringCircle k \ {earringBase}) =
      {(k : OnePoint ℕ)} ×ˢ {t : I | t ≠ 0 ∧ t ≠ 1} := by
    ext ⟨a, t⟩
    induction a using OnePoint.rec with
    | infty => simp
    | coe j =>
      simp only [Set.mem_sdiff, mem_preimage, earringPre_coe, mem_prod, mem_singleton_iff,
        OnePoint.coe_eq_coe, mem_ofPred_eq]
      constructor
      · rintro ⟨hmem, hne⟩
        refine ⟨?_, ?_, ?_⟩
        · by_contra hjk
          have h2 : earringParam j t ∈ earringCircle j ∩ earringCircle k :=
            ⟨earringParam_mem_earringCircle j t, hmem⟩
          rw [earringCircle_inter_earringCircle hjk] at h2
          exact hne (Subtype.ext h2)
        · rintro rfl; simp at hne
        · rintro rfl; simp at hne
      · rintro ⟨rfl, h0, h1⟩
        refine ⟨earringParam_mem_earringCircle j t, fun he => ?_⟩
        rcases earringLoop_apply_eq_base he with h | h
        · exact h0 h
        · exact h1 h
  rw [this]
  refine IsOpen.prod ?_ ?_
  · simpa using OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_discrete {k})
  · have : {t : I | t ≠ 0 ∧ t ≠ 1} = ({0, 1} : Set I)ᶜ := by ext; simp
    rw [this]
    exact (Set.toFinite _).isClosed.isOpen_compl

/-! ### Sub-earrings -/

/-- The sub-earring map `𝔼 → 𝔼` sending `ℓₖ` to `ℓ_{ν k}`, for `ν → ∞`. -/
def earringSub (ν : ℕ → ℕ) (hν : Tendsto ν atTop atTop) : C(earring, earring) :=
  earringMap earringBase (fun k => earringLoop (ν k))
    fun U hU => hν.eventually (loopsShrinkTo_earringLoop U hU)

section earringSub

variable {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop)

/-- The sub-earring map fixes the base point. -/
@[simp] theorem earringSub_base : earringSub ν hν earringBase = earringBase :=
  earringMap_base _

/-- The sub-earring map sends `ℓₖ(t)` to `ℓ_{ν k}(t)`. -/
@[simp] theorem earringSub_earringLoop (k : ℕ) (t : I) :
    earringSub ν hν (earringLoop k t) = earringLoop (ν k) t :=
  earringMap_earringLoop _ k t

end earringSub

/-! ### Casts of paths

`Path.cast` changes the type of a path along equalities of its end points without changing the
underlying function; points that agree only propositionally (such as `earringMap y γ h b₀ = y`)
are compared through it. Every lemma here is proved by `subst`. -/

/-- Casting the end points of two paths does not change whether they are homotopic. -/
theorem homotopic_cast_iff {X : Type*} [TopologicalSpace X] {x y x' y' : X} (p q : Path x y)
    (hx : x' = x) (hy : y' = y) :
    (p.cast hx hy).Homotopic (q.cast hx hy) ↔ p.Homotopic q := by
  subst hx hy
  rfl

/-- Casting a loop along an equality of base points does not change whether it is
null-homotopic. -/
theorem cast_homotopic_refl_iff {X : Type*} [TopologicalSpace X] {x x' : X} (h : x' = x)
    (p : Path x x) : (p.cast h h).Homotopic (Path.refl x') ↔ p.Homotopic (Path.refl x) := by
  have hr : (Path.refl x).cast h h = Path.refl x' := by subst h; rfl
  rw [← hr, homotopic_cast_iff]

/-- A cast of a cast is a cast. -/
theorem path_cast_cast {X : Type*} [TopologicalSpace X] {x y x' y' x'' y'' : X} (p : Path x y)
    (hx : x' = x) (hy : y' = y) (hx' : x'' = x') (hy' : y'' = y') :
    (p.cast hx hy).cast hx' hy' = p.cast (hx'.trans hx) (hy'.trans hy) :=
  rfl

/-! ### Essential loops -/

/-- If the image of a loop under a map is essential, the loop is essential. (Applied to a
retraction this says that loops essential in a retract are essential in the whole space.) -/
theorem not_homotopic_refl_of_map {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : C(X, Z)) {x : X} {p : Path x x}
    (hp : ¬ (p.map f.continuous).Homotopic (Path.refl (f x))) : ¬ p.Homotopic (Path.refl x) :=
  fun h => hp <| by
    have hr : (Path.refl x).map f.continuous = Path.refl (f x) := by ext; rfl
    simpa [hr] using h.map f

/-- The loop `ℓₖ` under `f ∘ earringSub ν` is the loop `ℓ_{ν k}` under `f`, up to the cast along
`earringSub_base`. -/
theorem earringLoop_map_comp_earringSub (f : C(earring, Y)) {ν : ℕ → ℕ}
    (hν : Tendsto ν atTop atTop) (k : ℕ) :
    (earringLoop k).map (f.comp (earringSub ν hν)).continuous =
      ((earringLoop (ν k)).map f.continuous).cast (congrArg f (earringSub_base hν))
        (congrArg f (earringSub_base hν)) := by
  ext t
  simp

/-- Precomposing a fully essential map with a sub-earring map gives a fully essential map. -/
theorem FullyEssential.comp_earringSub {g : C(earring, Y)} (hg : FullyEssential g) {ν : ℕ → ℕ}
    (hν : Tendsto ν atTop atTop) : FullyEssential (g.comp (earringSub ν hν)) := by
  intro k hk
  rw [earringLoop_map_comp_earringSub, cast_homotopic_refl_iff] at hk
  exact hg (ν k) hk

/-- The standard loop `t ↦ t` around the circle `ℝ/ℤ = AddCircle 1`, based at `0`. (The instance
`Fact (0 < 1)` needed for `AddCircle 1` is Mathlib's `ZeroLEOneClass.factZeroLtOne`.) -/
def unitAddCircleLoop : Path ((0 : ℝ) : AddCircle (1 : ℝ)) ((0 : ℝ) : AddCircle (1 : ℝ)) :=
  AddCircle.zsmulLoop 1 0 1

/-- The standard loop around `ℝ/ℤ` is essential (winding number `1 ≠ 0`). -/
theorem unitAddCircleLoop_not_homotopic_refl : ¬ unitAddCircleLoop.Homotopic (Path.refl _) := by
  intro h
  have h1 := AddCircle.windingNumber_zsmulLoop (p := 1) 0 1
  have h0 := AddCircle.windingNumber_eq_div (p := 1) (Path.refl ((0 : ℝ) : AddCircle (1 : ℝ)))
    (ContinuousMap.const _ 0) (by ext; simp)
  have hq : Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop 1 0 1) =
      Path.Homotopic.Quotient.mk (Path.refl ((0 : ℝ) : AddCircle (1 : ℝ))) :=
    Quotient.sound h
  rw [hq] at h1
  rw [h1] at h0
  simp at h0

/-- The map `𝔼 → ℝ/ℤ` winding `Cₖ` once around the circle and collapsing the other circles to the
base point. -/
def earringWind (k : ℕ) : C(earring, AddCircle (1 : ℝ)) :=
  earringMap _ (fun j => if j = k then unitAddCircleLoop else Path.refl _) fun U hU => by
    filter_upwards [eventually_gt_atTop k] with j hj
    simp only [hj.ne', ↓reduceIte]
    rintro _ ⟨t, rfl⟩
    exact mem_of_mem_nhds hU

/-- `earringWind k` sends the base point to `0`. -/
@[simp] theorem earringWind_base (k : ℕ) :
    earringWind k earringBase = ((0 : ℝ) : AddCircle (1 : ℝ)) :=
  earringMap_base _

/-- `earringWind k` sends `ℓₖ` to the standard loop. -/
theorem earringWind_earringLoop (k : ℕ) (t : I) :
    earringWind k (earringLoop k t) = unitAddCircleLoop t :=
  (earringMap_earringLoop _ k t).trans (by simp)

/-- **The earring loops are essential**: no `ℓₖ` is null-homotopic in the earring. -/
theorem earringLoop_not_homotopic_refl (k : ℕ) :
    ¬ (earringLoop k).Homotopic (Path.refl earringBase) := by
  refine not_homotopic_refl_of_map (earringWind k) ?_
  have heq : (earringLoop k).map (earringWind k).continuous =
      unitAddCircleLoop.cast (earringWind_base k) (earringWind_base k) := by
    ext t
    exact earringWind_earringLoop k t
  rw [heq, cast_homotopic_refl_iff]
  exact unitAddCircleLoop_not_homotopic_refl

/-- The identity of the earring is fully essential. -/
theorem fullyEssential_id : FullyEssential (ContinuousMap.id earring) := by
  intro k
  simpa using earringLoop_not_homotopic_refl k

/-- The base point of the earring lies in its wild set. -/
theorem earringBase_mem_wildSet : earringBase ∈ wildSet earring :=
  ⟨ContinuousMap.id earring, rfl, fullyEssential_id⟩

end Peano
