module

public import Peano.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# One-dimensionality from neighbourhoods with finite frontier

`CoveringDimLE 1` (Lebesgue covering dimension `≤ 1`, `Peano.Defs`) is proved for compact
Hausdorff spaces that are *rim-finite*: every point has arbitrarily small open neighbourhoods
whose frontier is finite (`coveringDimLE_one_of_finite_frontier`). This replaces the former
textbook axiom on planar compacta with empty interior; the planar spaces of the formalisation
(the circle, the arc, the earring and the models of Theorem 1.2) are all rim-finite.

## The argument

Let `U` be a finite open cover. Every point `x` has an open neighbourhood `W x ⊆ U i` with finite
frontier; finitely many of them, `w₀, …, w_{n-1}`, cover `X` (compactness). The sets
`Vⱼ = wⱼ ∖ closure (⋃_{j' < j} w_{j'})` are open, pairwise disjoint, and cover everything except
the finite set `F = ⋃ⱼ frontier wⱼ`: if `j` is least with `x ∈ wⱼ` and `x ∉ Vⱼ`, then `x` lies in
the closure of some `w_{j'}`, `j' < j`, but not in `w_{j'}`, so on its frontier. The points of `F`
are separated by pairwise disjoint open sets `B p ⊆ U i` (Hausdorff). The family `V ∪ B` is a
finite open refinement in which every point lies in at most one `Vⱼ` and at most one `B p`, so
it has order `≤ 2`.

## Planar sets

For `A ⊆ ℝ²` (with the sup metric of `ℝ × ℝ`), sup-metric balls are used as neighbourhoods; the
frontier of a ball in `A` lies in `A ∩ sphere x ρ`. So a compact `A` such that every point has
arbitrarily small radii `ρ` with `A ∩ sphere x ρ` finite is one-dimensional
(`coveringDimLE_one_of_finite_sphere`). A Euclidean circle meets a sup-metric sphere (the
boundary of a square) in finitely many points (`finite_circle_inter_sphere`): each of the four
sides lies on a line, which meets the circle at most twice.

## Main statements

`coveringDimLE_one_of_finite_frontier`, `coveringDimLE_one_of_finite_sphere`,
`finite_circle_inter_sphere`.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace Peano

/-! ### Rim-finite compact spaces are one-dimensional -/

/-- A set of indices of a sum type that meets each summand in a subsingleton has at most two
elements. -/
lemma ncard_le_two_of_subsingleton {α β : Type*} [Finite α] [Finite β] (S : Set (α ⊕ β))
    (h₁ : {a | Sum.inl a ∈ S}.Subsingleton) (h₂ : {b | Sum.inr b ∈ S}.Subsingleton) :
    S.ncard ≤ 2 := by
  have hS : S ⊆ Sum.inl '' {a | Sum.inl a ∈ S} ∪ Sum.inr '' {b | Sum.inr b ∈ S} := by
    rintro (a | b) h
    · exact Or.inl ⟨a, h, rfl⟩
    · exact Or.inr ⟨b, h, rfl⟩
  calc S.ncard ≤ (Sum.inl '' {a | Sum.inl a ∈ S} ∪ Sum.inr '' {b | Sum.inr b ∈ S}).ncard :=
        ncard_le_ncard hS (toFinite _)
    _ ≤ (Sum.inl '' {a | Sum.inl a ∈ S}).ncard + (Sum.inr '' {b | Sum.inr b ∈ S}).ncard :=
        ncard_union_le _ _
    _ ≤ {a | Sum.inl a ∈ S}.ncard + {b | Sum.inr b ∈ S}.ncard :=
        add_le_add (ncard_image_le (toFinite _)) (ncard_image_le (toFinite _))
    _ ≤ 1 + 1 := add_le_add (ncard_le_one_iff_subsingleton.2 h₁)
        (ncard_le_one_iff_subsingleton.2 h₂)

/-- **Rim-finite compact Hausdorff spaces have covering dimension `≤ 1`.** If every point has
arbitrarily small open neighbourhoods with finite frontier, every finite open cover has a finite
open refinement of order `≤ 2`. -/
theorem coveringDimLE_one_of_finite_frontier {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X]
    (h : ∀ x : X, ∀ N ∈ 𝓝 x, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ (frontier W).Finite) :
    CoveringDimLE 1 X := by
  intro ι _ U hUo hUcov
  have hmem : ∀ x : X, ∃ i, x ∈ U i := fun x => mem_iUnion.1 (hUcov ▸ mem_univ x)
  choose i hi using hmem
  choose W hWo hxW hWU hWf using fun x => h x (U (i x)) ((hUo (i x)).mem_nhds (hi x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  -- the finitely many neighbourhoods, linearly ordered
  let e := t.equivFin
  let w : Fin t.card → Set X := fun j => W (e.symm j)
  have hwo : ∀ j, IsOpen (w j) := fun j => hWo _
  have hwcov : ∀ x, ∃ j, x ∈ w j := by
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    exact ⟨e ⟨y, hy⟩, by simpa [w] using hxy⟩
  -- the finite set of frontier points
  let F : Set X := ⋃ j, frontier (w j)
  have hF : F.Finite := finite_iUnion fun j => hWf _
  -- disjointified neighbourhoods
  let V : Fin t.card → Set X := fun j => w j \ closure (⋃ j' ∈ {j' | j' < j}, w j')
  have hVo : ∀ j, IsOpen (V j) := fun j => (hwo j).sdiff isClosed_closure
  have hVdisj : ∀ x j j', x ∈ V j → x ∈ V j' → j = j' := by
    intro x j j' hj hj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hj'.2 (subset_closure (mem_biUnion (show j ∈ {j'' | j'' < j'} from hlt) hj.1))
    · exact hj.2 (subset_closure (mem_biUnion (show j' ∈ {j'' | j'' < j} from hlt) hj'.1))
  have hVcov : ∀ x, x ∉ F → ∃ j, x ∈ V j := by
    intro x hxF
    obtain ⟨j₀, hj₀⟩ := hwcov x
    obtain ⟨j, hj, hmin⟩ := (wellFounded_lt (α := Fin t.card)).has_min {j | x ∈ w j} ⟨j₀, hj₀⟩
    refine ⟨j, hj, fun hc => hxF ?_⟩
    rw [(toFinite {j' | j' < j}).closure_biUnion] at hc
    obtain ⟨j', hj', hc⟩ := mem_iUnion₂.1 hc
    refine mem_iUnion.2 ⟨j', ?_⟩
    rw [(hwo j').frontier_eq]
    exact ⟨hc, fun h => hmin j' h hj'⟩
  -- separating the frontier points
  obtain ⟨S, hS, hSdisj⟩ := hF.t2_separation
  let e' := hF.toFinset.equivFin
  let pt : Fin hF.toFinset.card → X := fun q => (e'.symm q : X)
  have hpt : ∀ q, pt q ∈ F := fun q => hF.mem_toFinset.1 (e'.symm q).2
  have hpt_inj : Function.Injective pt := fun q q' h =>
    e'.symm.injective (Subtype.ext h)
  let B : Fin hF.toFinset.card → Set X := fun q => S (pt q) ∩ U (i (pt q))
  refine ⟨Fin t.card ⊕ Fin hF.toFinset.card, inferInstance, Sum.elim V B, ?_, ?_, ?_, ?_⟩
  · rintro (j | q)
    · exact hVo j
    · exact (hS _).2.inter (hUo _)
  · refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
    by_cases hx : x ∈ F
    · refine ⟨Sum.inr (e' ⟨x, hF.mem_toFinset.2 hx⟩), ?_⟩
      have : pt (e' ⟨x, hF.mem_toFinset.2 hx⟩) = x := by simp [pt]
      show x ∈ B _
      simp only [B, this]
      exact ⟨(hS x).1, hi x⟩
    · obtain ⟨j, hj⟩ := hVcov x hx
      exact ⟨Sum.inl j, hj⟩
  · rintro (j | q)
    · exact ⟨i (e.symm j), sdiff_subset.trans (hWU _)⟩
    · exact ⟨i (pt q), inter_subset_right⟩
  · intro x
    refine ncard_le_two_of_subsingleton _ (fun j hj j' hj' => hVdisj x j j' hj hj')
      fun q hq q' hq' => hpt_inj ?_
    exact hSdisj.elim (hpt q) (hpt q') (not_disjoint_iff.2 ⟨x, hq.1, hq'.1⟩)

/-! ### Planar sets -/

/-- A point of a sup-metric sphere in `ℝ²` lies on one of the four lines carrying the sides of
the square. -/
lemma mem_sphere_prod_cases {x y : ℝ × ℝ} {ρ : ℝ} (h : y ∈ sphere x ρ) :
    y.1 = x.1 + ρ ∨ y.1 = x.1 - ρ ∨ y.2 = x.2 + ρ ∨ y.2 = x.2 - ρ := by
  rw [mem_sphere, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
  rcases max_choice |y.1 - x.1| |y.2 - x.2| with h' | h' <;> rw [h'] at h
  · rcases abs_choice (y.1 - x.1) with h'' | h'' <;> rw [h''] at h
    · left; linarith
    · right; left; linarith
  · rcases abs_choice (y.2 - x.2) with h'' | h'' <;> rw [h''] at h
    · right; right; left; linarith
    · right; right; right; linarith

/-- A solution of `(v - c)² = K` is `c ± √K`. -/
lemma eq_add_sqrt_or_eq_sub_sqrt {v c K : ℝ} (h : (v - c) ^ 2 = K) :
    v = c + √K ∨ v = c - √K := by
  have : √K = |v - c| := by rw [← h, Real.sqrt_sq_eq_abs]
  rcases abs_choice (v - c) with h' | h'
  · left; linarith
  · right; linarith

/-- A circle meets a vertical line in at most two points. -/
lemma finite_circle_inter_vertical (c : ℝ × ℝ) (R α : ℝ) :
    {y : ℝ × ℝ | (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2 = R ^ 2 ∧ y.1 = α}.Finite := by
  refine (toFinite ({(α, c.2 + √(R ^ 2 - (α - c.1) ^ 2)),
    (α, c.2 - √(R ^ 2 - (α - c.1) ^ 2))} : Set (ℝ × ℝ))).subset ?_
  rintro y ⟨h, hα⟩
  have h2 : (y.2 - c.2) ^ 2 = R ^ 2 - (α - c.1) ^ 2 := by rw [← hα]; linarith
  rcases eq_add_sqrt_or_eq_sub_sqrt h2 with h' | h'
  · exact Or.inl (Prod.ext hα h')
  · exact Or.inr (Prod.ext hα h')

/-- A circle meets a horizontal line in at most two points. -/
lemma finite_circle_inter_horizontal (c : ℝ × ℝ) (R β : ℝ) :
    {y : ℝ × ℝ | (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2 = R ^ 2 ∧ y.2 = β}.Finite := by
  refine (toFinite ({(c.1 + √(R ^ 2 - (β - c.2) ^ 2), β),
    (c.1 - √(R ^ 2 - (β - c.2) ^ 2), β)} : Set (ℝ × ℝ))).subset ?_
  rintro y ⟨h, hβ⟩
  have h2 : (y.1 - c.1) ^ 2 = R ^ 2 - (β - c.2) ^ 2 := by rw [← hβ]; linarith
  rcases eq_add_sqrt_or_eq_sub_sqrt h2 with h' | h'
  · exact Or.inl (Prod.ext h' hβ)
  · exact Or.inr (Prod.ext h' hβ)

/-- **A Euclidean circle meets a sup-metric sphere (a square) in finitely many points.** -/
theorem finite_circle_inter_sphere (c : ℝ × ℝ) (R : ℝ) (x : ℝ × ℝ) (ρ : ℝ) :
    ({y : ℝ × ℝ | (y.1 - c.1) ^ 2 + (y.2 - c.2) ^ 2 = R ^ 2} ∩ sphere x ρ).Finite := by
  refine (((finite_circle_inter_vertical c R (x.1 + ρ)).union
    (finite_circle_inter_vertical c R (x.1 - ρ))).union
    ((finite_circle_inter_horizontal c R (x.2 + ρ)).union
    (finite_circle_inter_horizontal c R (x.2 - ρ)))).subset ?_
  rintro y ⟨hc, hs⟩
  rcases mem_sphere_prod_cases hs with h | h | h | h
  exacts [Or.inl (Or.inl ⟨hc, h⟩), Or.inl (Or.inr ⟨hc, h⟩), Or.inr (Or.inl ⟨hc, h⟩),
    Or.inr (Or.inr ⟨hc, h⟩)]

/-- The horizontal distance is at most the sup distance in `ℝ²`. -/
lemma abs_fst_sub_le_dist (y x : ℝ × ℝ) : |y.1 - x.1| ≤ dist y x := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_left _ _

/-- The vertical distance is at most the sup distance in `ℝ²`. -/
lemma abs_snd_sub_le_dist (y x : ℝ × ℝ) : |y.2 - x.2| ≤ dist y x := by
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]; exact le_max_right _ _

/-- The frontier of an open ball of a metric space lies in the sphere. -/
lemma dist_eq_of_mem_frontier_ball {M : Type*} [PseudoMetricSpace M] {x y : M} {ρ : ℝ}
    (hy : y ∈ frontier (ball x ρ)) : dist y x = ρ := by
  rw [frontier, isOpen_ball.interior_eq] at hy
  exact le_antisymm (closure_ball_subset_closedBall hy.1) (not_lt.1 hy.2)

/-- **Planar compacta meeting small squares in finitely many points are one-dimensional.** If
every point `x` of a compact `A ⊆ ℝ²` has arbitrarily small radii `ρ` for which `A` meets the
sup-metric sphere `sphere x ρ` in finitely many points, then `CoveringDimLE 1 A`. -/
theorem coveringDimLE_one_of_finite_sphere (A : Set (ℝ × ℝ)) [CompactSpace A]
    (h : ∀ x ∈ A, ∀ r > 0, ∃ ρ ∈ Ioo 0 r, (A ∩ sphere x ρ).Finite) : CoveringDimLE 1 A := by
  refine coveringDimLE_one_of_finite_frontier fun x N hN => ?_
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨ρ, hρ, hfin⟩ := h x x.2 r hr
  refine ⟨ball x ρ, isOpen_ball, mem_ball_self hρ.1, (ball_subset_ball hρ.2.le).trans hrN, ?_⟩
  refine (hfin.preimage Subtype.val_injective.injOn).subset fun y hy => ?_
  exact ⟨y.2, (dist_eq_of_mem_frontier_ball hy : dist y x = ρ)⟩

end Peano
