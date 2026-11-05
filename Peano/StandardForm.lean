module

public import Peano.Arcs
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Filter.Cofinite

/-!
# Lemmas 4.3, 4.5 and Corollary 4.4 for arc systems (§4)

Brazas–Pavešić, §4, stated for an `ArcSystem` (see `Peano.Arcs`). The paper's sequences
`n₁ < n₂ < ⋯` of arc indices are encoded by injective sequences `u : ℕ → ι`, which also covers
finitely many arcs (no injective sequence then exists), so no case split is needed. The paper's
proofs of Lemma 4.3 and of the compactness step of Lemma 4.5 have gaps, repaired in
`notes/checks/B.md`.

Proofs. Lemma 4.3 follows the three-point repair of `B.md` without subsequences: each long arc
contains three points at pairwise distance `≥ ε / 4` (`exists_three_points`, by the intermediate
value theorem); a cluster point `(x, y, z)` of these triples has disjoint connected
neighbourhoods, each meeting the arc and a point outside it, hence each containing one of the at
most two end points (`exists_ends_mem_of_isPreconnected`), which is impossible
(`not_forall_three_points`). Lemma 4.5 ("conditions ⇒ open") is proved directly rather than via
the auxiliary topology `X'` of the paper: a sequence outside `U` converging to `x ∈ U ∩ W` lies
eventually off `W` by (1); if it meets finitely many arcs, (2) gives a contradiction; otherwise
Lemma 4.3 moves end points of these arcs to `x` and (3) gives the contradiction.
-/

@[expose] public section

open Set Filter Topology unitInterval

noncomputable section

namespace Peano

namespace ArcSystem

variable {X : Type*} [MetricSpace X] (S : ArcSystem X)

/-! ### Elementary facts about arcs -/

/-- The open unit interval is the image of `(0, 1) ⊆ ℝ` under the projection onto `I`. -/
theorem openUnit_eq_image_projIcc :
    openUnit = projIcc (0 : ℝ) 1 zero_le_one '' Ioo 0 1 := by
  ext t
  constructor
  · intro ht
    exact ⟨t, ht, projIcc_val zero_le_one t⟩
  · rintro ⟨s, hs, rfl⟩
    change (0 : ℝ) < _ ∧ _ < (1 : ℝ)
    rw [projIcc_of_mem zero_le_one (Ioo_subset_Icc_self hs)]
    exact hs

/-- The open unit interval is preconnected. -/
theorem isPreconnected_openUnit : IsPreconnected openUnit := by
  rw [openUnit_eq_image_projIcc]
  exact isPreconnected_Ioo.image _ continuous_projIcc.continuousOn

/-- The open unit interval is dense in `I`. -/
theorem closure_openUnit : closure openUnit = (univ : Set I) := by
  refine eq_univ_of_forall fun t => ?_
  rw [openUnit_eq_image_projIcc]
  refine image_closure_subset_closure_image continuous_projIcc ⟨t, ?_, projIcc_val _ t⟩
  rw [closure_Ioo zero_ne_one]
  exact t.2

/-- The open arc is preconnected. -/
theorem isPreconnected_arc (i : S.ι) : IsPreconnected (S.arc i) :=
  isPreconnected_openUnit.image _ (S.h i).continuous.continuousOn

/-- The closed arc is compact. -/
theorem isCompact_closedArc (i : S.ι) : IsCompact (S.closedArc i) :=
  isCompact_range (S.h i).continuous

/-- The open arc lies in the closed arc. -/
theorem arc_subset_closedArc (i : S.ι) : S.arc i ⊆ S.closedArc i := image_subset_range _ _

/-- The end points lie in the closed arc. -/
theorem ends_subset_closedArc (i : S.ι) : S.ends i ⊆ S.closedArc i := by
  rintro _ (rfl | rfl) <;> exact mem_range_self _

/-- The closed arc is the closure of the open arc. -/
theorem closure_arc (i : S.ι) : closure (S.arc i) = S.closedArc i := by
  refine subset_antisymm ((S.isCompact_closedArc i).isClosed.closure_subset_iff.2
    (S.arc_subset_closedArc i)) ?_
  rintro _ ⟨t, rfl⟩
  refine image_closure_subset_closure_image (S.h i).continuous ⟨t, ?_, rfl⟩
  rw [closure_openUnit]
  trivial

/-- The closed arc is the open arc together with its end points. -/
theorem closedArc_subset_arc_union_ends (i : S.ι) : S.closedArc i ⊆ S.arc i ∪ S.ends i := by
  rintro _ ⟨t, rfl⟩
  by_cases ht : t ∈ openUnit
  · exact Or.inl ⟨t, ht, rfl⟩
  · right
    have h0 : (0 : ℝ) ≤ t := t.2.1
    have h1 : (t : ℝ) ≤ 1 := t.2.2
    simp only [openUnit, mem_ofPred_eq, not_and_or, not_lt] at ht
    rcases ht with ht | ht
    · left; congr 1; exact Subtype.ext (le_antisymm ht h0)
    · right; congr 1; exact Subtype.ext (le_antisymm h1 ht)

/-- The end points do not lie in the open arc (they lie in `W`). -/
theorem ends_disjoint_arc (i : S.ι) : Disjoint (S.ends i) (S.arc i) := by
  rw [Set.disjoint_left]
  intro e he hea
  have hW : e ∈ S.W := by rcases he with rfl | rfl; exacts [(S.mem_W i).1, (S.mem_W i).2]
  have : e ∈ S.Wᶜ := S.iUnion_eq ▸ mem_iUnion.2 ⟨i, hea⟩
  exact this hW

/-- Distinct open arcs are disjoint. -/
theorem disjoint_arc {i j : S.ι} (hij : i ≠ j) : Disjoint (S.arc i) (S.arc j) := S.disjoint hij

/-- Every point outside `W` lies in some open arc. -/
theorem exists_mem_arc_of_notMem_W {x : X} (hx : x ∉ S.W) : ∃ i, x ∈ S.arc i := by
  have : x ∈ ⋃ i, S.arc i := (S.iUnion_eq).symm ▸ hx
  simpa using this

/-- **Separation by the end points.** A preconnected set `V` that meets the open arc `Oᵢ` and
contains a point outside it contains an end point of `Oᵢ`. -/
theorem exists_ends_mem_of_isPreconnected {V : Set X} (hV : IsPreconnected V) (i : S.ι)
    {p x : X} (hp : p ∈ V ∩ S.arc i) (hx : x ∈ V) (hxi : x ∉ S.arc i) :
    ∃ e ∈ S.ends i, e ∈ V := by
  by_contra! hne
  have hcover : V ⊆ S.arc i ∪ (closure (S.arc i))ᶜ := by
    intro y hy
    by_cases hyc : y ∈ closure (S.arc i)
    · rw [S.closure_arc] at hyc
      rcases S.closedArc_subset_arc_union_ends i hyc with h | h
      · exact Or.inl h
      · exact absurd hy (hne y h)
    · exact Or.inr hyc
  have hxc : x ∉ closure (S.arc i) := by
    intro hxc
    rw [S.closure_arc] at hxc
    rcases S.closedArc_subset_arc_union_ends i hxc with h | h
    · exact hxi h
    · exact hne x h hx
  obtain ⟨y, -, hy1, hy2⟩ := hV _ _ (S.isOpen_arc i) isClosed_closure.isOpen_compl hcover
    ⟨p, hp.1, hp.2⟩ ⟨x, hx, hxc⟩
  exact hy2 (subset_closure hy1)

/-- A point lies in the open arcs of at most one term of an injective sequence of indices, so it
eventually lies outside them. -/
theorem eventually_notMem_arc {u : ℕ → S.ι} (hu : Function.Injective u) (x : X) :
    ∀ᶠ n in atTop, x ∉ S.arc (u n) := by
  by_cases h : ∃ m, x ∈ S.arc (u m)
  · obtain ⟨m, hm⟩ := h
    filter_upwards [eventually_gt_atTop m] with n hn hxn
    exact Set.disjoint_left.1 (S.disjoint_arc (hu.ne hn.ne')) hxn hm
  · push Not at h
    exact Eventually.of_forall h

/-- Closed arcs are bounded. -/
theorem isBounded_closedArc (i : S.ι) : Bornology.IsBounded (S.closedArc i) :=
  (S.isCompact_closedArc i).isBounded

variable [CompactSpace X] [LocallyPathConnectedSpace X]

omit [CompactSpace X] [LocallyPathConnectedSpace X] in
/-- An open arc whose closure has diameter at least `ε > 0` contains three points at pairwise
distance at least `ε / 4`: two points at distance `> ε / 2`, and (intermediate value theorem on
the connected arc) a third point equidistant from them. -/
theorem exists_three_points {ε : ℝ} (hε : 0 < ε) {i : S.ι}
    (hi : ε ≤ Metric.diam (S.closedArc i)) :
    ∃ a ∈ S.arc i, ∃ b ∈ S.arc i, ∃ c ∈ S.arc i,
      ε / 4 ≤ dist a b ∧ ε / 4 ≤ dist b c ∧ ε / 4 ≤ dist a c := by
  rw [← S.closure_arc, Metric.diam_closure] at hi
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ S.arc i, ∃ b ∈ S.arc i, ε / 2 < dist a b := by
    by_contra! h
    have := Metric.diam_le_of_forall_dist_le (by positivity) h
    linarith
  obtain ⟨c, hc, hcab⟩ := (S.isPreconnected_arc i).intermediate_value ha hb
    (f := fun w => dist w a - dist w b) (by fun_prop)
    (show (0 : ℝ) ∈ Icc (dist a a - dist a b) (dist b a - dist b b) by
      simp only [dist_self, zero_sub, sub_zero, mem_Icc, Left.neg_nonpos_iff]
      exact ⟨dist_nonneg, dist_nonneg⟩)
  have hcab' : dist c a = dist c b := by simp only at hcab; linarith
  have htri := dist_triangle a c b
  rw [dist_comm a c] at htri
  refine ⟨a, ha, b, hb, c, hc, by linarith, ?_, ?_⟩
  · rw [dist_comm]; linarith
  · rw [dist_comm]; linarith

/-- **Core of Lemma 4.3.** There is no injective sequence of arcs each containing three points at
pairwise distance at least `δ > 0`: a cluster point `(x, y, z)` of the triples has pairwise
disjoint connected neighbourhoods of radius `δ / 4`, each of which eventually contains an end
point of the arc, and two of the three must share one of the at most two end points. -/
theorem not_forall_three_points {δ : ℝ} (hδ : 0 < δ) {u : ℕ → S.ι} (hu : Function.Injective u)
    (a b c : ℕ → X) (ha : ∀ n, a n ∈ S.arc (u n)) (hb : ∀ n, b n ∈ S.arc (u n))
    (hc : ∀ n, c n ∈ S.arc (u n)) (hab : ∀ n, δ ≤ dist (a n) (b n))
    (hbc : ∀ n, δ ≤ dist (b n) (c n)) (hac : ∀ n, δ ≤ dist (a n) (c n)) : False := by
  obtain ⟨⟨x, y, z⟩, hxyz⟩ :=
    exists_clusterPt_of_compactSpace (map (fun n => (a n, b n, c n)) atTop)
  have hball : ∀ w : X, ∃ V : Set X, IsPreconnected V ∧ IsOpen V ∧ w ∈ V ∧
      V ⊆ Metric.ball w (δ / 4) := fun w =>
    ⟨connectedComponentIn (Metric.ball w (δ / 4)) w, isPreconnected_connectedComponentIn,
      Metric.isOpen_ball.connectedComponentIn, mem_connectedComponentIn (Metric.mem_ball_self
        (by positivity)), connectedComponentIn_subset _ _⟩
  obtain ⟨Vx, hVxc, hVxo, hxV, hVxb⟩ := hball x
  obtain ⟨Vy, hVyc, hVyo, hyV, hVyb⟩ := hball y
  obtain ⟨Vz, hVzc, hVzo, hzV, hVzb⟩ := hball z
  have hfreq := mapClusterPt_iff_frequently.1 hxyz (Vx ×ˢ Vy ×ˢ Vz)
    (prod_mem_nhds (hVxo.mem_nhds hxV) (prod_mem_nhds (hVyo.mem_nhds hyV) (hVzo.mem_nhds hzV)))
  obtain ⟨n, ⟨han, hbn, hcn⟩, ⟨hxn, hyn⟩, hzn⟩ := (hfreq.and_eventually
    (((S.eventually_notMem_arc hu x).and (S.eventually_notMem_arc hu y)).and
      (S.eventually_notMem_arc hu z))).exists
  obtain ⟨ex, hex, hexV⟩ := S.exists_ends_mem_of_isPreconnected hVxc (u n) ⟨han, ha n⟩ hxV hxn
  obtain ⟨ey, hey, heyV⟩ := S.exists_ends_mem_of_isPreconnected hVyc (u n) ⟨hbn, hb n⟩ hyV hyn
  obtain ⟨ez, hez, hezV⟩ := S.exists_ends_mem_of_isPreconnected hVzc (u n) ⟨hcn, hc n⟩ hzV hzn
  have hclose : ∀ (w p e : X) (V : Set X), V ⊆ Metric.ball w (δ / 4) → p ∈ V → e ∈ V →
      dist p e < δ / 2 := fun w p e V hV hp he => by
    have h1 := hV hp
    have h2 := hV he
    rw [Metric.mem_ball] at h1 h2
    linarith [dist_triangle_right p e w]
  have dx := hclose _ _ _ _ hVxb han hexV
  have dy := hclose _ _ _ _ hVyb hbn heyV
  have dz := hclose _ _ _ _ hVzb hcn hezV
  have pig : ex = ey ∨ ey = ez ∨ ex = ez := by
    rcases hex with rfl | rfl <;> rcases hey with rfl | rfl <;> rcases hez with rfl | rfl <;>
      simp
  rcases pig with rfl | rfl | rfl
  · linarith [dist_triangle_right (a n) (b n) ex, hab n]
  · linarith [dist_triangle_right (b n) (c n) ey, hbc n]
  · linarith [dist_triangle_right (a n) (c n) ex, hac n]

/-! ### Lemma 4.3, Corollary 4.4, Lemma 4.5 -/

/-- **Lemma 4.3.** The diameters of the closed arcs tend to `0` (along the cofinite filter, which
is the paper's `n → ∞` and is vacuous for finitely many arcs). -/
theorem tendsto_diam_closedArc :
    Tendsto (fun i => Metric.diam (S.closedArc i)) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [eventually_cofinite]
  by_contra hinf
  set T := {i | ¬dist (Metric.diam (S.closedArc i)) 0 < ε} with hT
  set u : ℕ → S.ι := fun n => (Set.Infinite.natEmbedding T hinf n : S.ι) with hu_def
  have hu : Function.Injective u :=
    Subtype.val_injective.comp (Set.Infinite.natEmbedding T hinf).injective
  have hdiam : ∀ n, ε ≤ Metric.diam (S.closedArc (u n)) := fun n => by
    have := (Set.Infinite.natEmbedding T hinf n).2
    simp only [hT, mem_ofPred_eq, Real.dist_eq, sub_zero, not_lt] at this
    rwa [abs_of_nonneg Metric.diam_nonneg] at this
  choose a ha b hb c hc hab hbc hac using fun n => S.exists_three_points hε (hdiam n)
  exact S.not_forall_three_points (by positivity) hu a b c ha hb hc hab hbc hac

/-- Lemma 4.3 along an injective sequence of arcs. -/
theorem tendsto_diam_closedArc_comp {u : ℕ → S.ι} (hu : Function.Injective u) :
    Tendsto (fun k => Metric.diam (S.closedArc (u k))) atTop (𝓝 0) := by
  have : Tendsto u atTop cofinite := by
    rw [← Nat.cofinite_eq_atTop]
    exact hu.tendsto_cofinite
  exact S.tendsto_diam_closedArc.comp this

/-- **Corollary 4.4.** If end points `e k ∈ ∂O_{u k}` of distinct arcs converge to `x`, then the
closed arcs `Ō_{u k}` eventually lie in any neighbourhood of `x`. -/
theorem eventually_closedArc_subset {u : ℕ → S.ι} (hu : Function.Injective u) {e : ℕ → X}
    (he : ∀ k, e k ∈ S.ends (u k)) {x : X} (hx : Tendsto e atTop (𝓝 x)) {U : Set X}
    (hU : U ∈ 𝓝 x) : ∀ᶠ k in atTop, S.closedArc (u k) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  filter_upwards [Metric.tendsto_nhds.1 hx (ε / 2) (by positivity),
    Metric.tendsto_nhds.1 (S.tendsto_diam_closedArc_comp hu) (ε / 2) (by positivity)]
    with k hk1 hk2
  intro p hp
  apply hball
  rw [Metric.mem_ball]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.diam_nonneg] at hk2
  have := Metric.dist_le_diam_of_mem (S.isBounded_closedArc _) hp
    (S.ends_subset_closedArc _ (he k))
  linarith [dist_triangle p (e k) x]

/-- The three conditions of Lemma 4.5 on a set `U ⊆ X`. -/
def LocalCondition (U : Set X) : Prop :=
  IsOpen ((↑) ⁻¹' U : Set S.W) ∧
  (∀ i, IsOpen ((↑) ⁻¹' U : Set (S.closedArc i))) ∧
  ∀ (u : ℕ → S.ι), Function.Injective u → ∀ (e : ℕ → X), (∀ k, e k ∈ S.ends (u k)) →
    ∀ x ∈ U ∩ S.W, Tendsto e atTop (𝓝 x) → ∀ᶠ k in atTop, S.closedArc (u k) ⊆ U

omit [CompactSpace X] [LocallyPathConnectedSpace X] in
/-- If `U ∩ s` is relatively open in `s`, there is an open `G` of `X` with `G ∩ s = U ∩ s`. -/
theorem exists_isOpen_inter_eq {U s : Set X} (h : IsOpen ((↑) ⁻¹' U : Set s)) :
    ∃ G : Set X, IsOpen G ∧ ∀ y ∈ s, (y ∈ G ↔ y ∈ U) := by
  obtain ⟨G, hG, hGeq⟩ := isOpen_induced_iff.1 h
  exact ⟨G, hG, fun y hy => Set.ext_iff.1 hGeq ⟨y, hy⟩⟩

omit [CompactSpace X] [LocallyPathConnectedSpace X] in
/-- Lemma 4.5, "conditions ⇒ open", at a point of `W`, when a sequence `z n → x` outside `U` has
its points in finitely many arcs: some arc `Oᵢ` contains `z n` for infinitely many `n`, so
`x ∈ Ōᵢ` and condition (2) for `i` gives a contradiction. -/
theorem false_of_finite_range {U : Set X} (h2 : ∀ i, IsOpen ((↑) ⁻¹' U : Set (S.closedArc i)))
    {x : X} (hxU : x ∈ U) {z : ℕ → X} (hzx : Tendsto z atTop (𝓝 x)) (hzU : ∀ n, z n ∉ U)
    {j : ℕ → S.ι} (hj : ∀ n, z n ∈ S.arc (j n)) (hfin : (range j).Finite) : False := by
  have := hfin.to_subtype
  obtain ⟨⟨i, hi⟩, hinf⟩ := Finite.exists_infinite_fiber (fun n => (⟨j n, n, rfl⟩ : range j))
  have hfreq : ∃ᶠ n in atTop, j n = i := by
    rw [Nat.frequently_atTop_iff_infinite]
    convert infinite_coe_iff.1 hinf using 1
    ext n
    simp [Subtype.ext_iff]
  obtain ⟨φ, hφ, hφi⟩ := extraction_of_frequently_atTop hfreq
  have hzφ := hzx.comp hφ.tendsto_atTop
  have hmem : ∀ n, z (φ n) ∈ S.closedArc i := fun n =>
    S.arc_subset_closedArc i (hφi n ▸ hj (φ n))
  have hx : x ∈ S.closedArc i :=
    (S.isCompact_closedArc i).isClosed.mem_of_tendsto hzφ (Eventually.of_forall hmem)
  obtain ⟨G, hG, hGU⟩ := exists_isOpen_inter_eq (h2 i)
  obtain ⟨n, hn⟩ := (hzφ.eventually (hG.mem_nhds ((hGU x hx).2 hxU))).exists
  exact hzU _ ((hGU _ (hmem n)).1 hn)

/-- Lemma 4.5, "conditions ⇒ open", at a point of `W`, when a sequence `z n → x` outside `U` has
its points in infinitely many arcs: along an injective sequence of these arcs, Lemma 4.3 moves
their first end points to `x`, and condition (3) puts the arcs, hence the points, in `U`. -/
theorem false_of_infinite_range {U : Set X} (hU : S.LocalCondition U) {x : X} (hxU : x ∈ U)
    (hxW : x ∈ S.W) {z : ℕ → X} (hzx : Tendsto z atTop (𝓝 x)) (hzU : ∀ n, z n ∉ U)
    {j : ℕ → S.ι} (hj : ∀ n, z n ∈ S.arc (j n)) (hinf : (range j).Infinite) : False := by
  set u : ℕ → S.ι := fun k => (Set.Infinite.natEmbedding _ hinf k : S.ι) with hu_def
  have hu : Function.Injective u :=
    Subtype.val_injective.comp (Set.Infinite.natEmbedding _ hinf).injective
  choose m hm using fun k => (Set.Infinite.natEmbedding _ hinf k).2
  have hm_inj : Function.Injective m := fun k k' hkk' => hu (by
    simp only [hu_def, ← hm, hkk'])
  have hmt : Tendsto m atTop atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hm_inj.tendsto_cofinite
  have hw : ∀ k, z (m k) ∈ S.closedArc (u k) := fun k => by
    have := hj (m k)
    rw [hm k] at this
    exact S.arc_subset_closedArc _ this
  have he : ∀ k, S.h (u k) 0 ∈ S.ends (u k) := fun k => Or.inl rfl
  have hex : Tendsto (fun k => S.h (u k) 0) atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hzm := tendsto_iff_dist_tendsto_zero.1 (hzx.comp hmt)
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => (dist_triangle _ (z (m k)) x).trans
      (add_le_add (Metric.dist_le_diam_of_mem (S.isBounded_closedArc _)
        (S.ends_subset_closedArc _ (he k)) (hw k)) le_rfl)) ?_
    simpa using (S.tendsto_diam_closedArc_comp hu).add hzm
  obtain ⟨k, hk⟩ := (hU.2.2 u hu _ he x ⟨hxU, hxW⟩ hex).exists
  exact hzU _ (hk (hw k))

/-- **Lemma 4.5.** `U` is open in `X` if and only if (1) `U ∩ W` is open in `W`, (2) `U ∩ Ōᵢ` is
open in `Ōᵢ` for each `i`, and (3) whenever end points of distinct arcs `O_{u k}` converge to a
point of `U ∩ W`, the closed arcs `Ō_{u k}` eventually lie in `U`. -/
theorem isOpen_iff_localCondition {U : Set X} : IsOpen U ↔ S.LocalCondition U := by
  refine ⟨fun hU => ⟨hU.preimage continuous_subtype_val,
    fun i => hU.preimage continuous_subtype_val,
    fun u hu e he x hx hex => S.eventually_closedArc_subset hu he hex (hU.mem_nhds hx.1)⟩,
    fun hU => ?_⟩
  rw [isOpen_iff_mem_nhds]
  intro x hxU
  by_cases hxW : x ∈ S.W
  · by_contra hnot
    have hcl : x ∈ closure Uᶜ := by
      rw [closure_compl]
      exact fun h => hnot (mem_interior_iff_mem_nhds.1 h)
    obtain ⟨y, hyU, hyx⟩ := mem_closure_iff_seq_limit.1 hcl
    obtain ⟨G, hG, hGU⟩ := exists_isOpen_inter_eq hU.1
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hyx (hG.mem_nhds ((hGU x hxW).2 hxU)))
    have hz : ∀ n, y (n + N) ∉ S.W := fun n hW =>
      hyU _ ((hGU _ hW).1 (hN _ (Nat.le_add_left N n)))
    choose j hj using fun n => S.exists_mem_arc_of_notMem_W (hz n)
    have hzx : Tendsto (fun n => y (n + N)) atTop (𝓝 x) := (tendsto_add_atTop_iff_nat N).2 hyx
    rcases (range j).finite_or_infinite with hfin | hinf
    · exact S.false_of_finite_range hU.2.1 hxU hzx (fun n => hyU _) hj hfin
    · exact S.false_of_infinite_range hU hxU hxW hzx (fun n => hyU _) hj hinf
  · obtain ⟨i, hi⟩ := S.exists_mem_arc_of_notMem_W hxW
    obtain ⟨G, hG, hGU⟩ := exists_isOpen_inter_eq (hU.2.1 i)
    have hxG := (hGU x (S.arc_subset_closedArc i hi)).2 hxU
    filter_upwards [hG.mem_nhds hxG, (S.isOpen_arc i).mem_nhds hi] with y hyG hy
    exact (hGU y (S.arc_subset_closedArc i hy)).1 hyG

end ArcSystem

end Peano
