module

public import Peano.Earring
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Local joinability, unions of shrinking pieces, null-homotopy through retractions

General tools used to build the planar models of `Peano.Models` (and the examples of
`Peano.Sanity`); nothing here refers to the earring or to the paper's constructions.
(`Peano.Earring` is imported only for the cast lemma `homotopic_cast_iff`.)

* **Local joinability.** `LocJoin P p` says that points of `P` near `p` are joined to `p` by paths
  in `P` that stay near `p` (local path-connectedness "im kleinen", for a subset of a pseudometric
  space). Convex sets (`Convex.locJoin`) and simple closed curves (`locJoin_range_of_periodic`)
  have it at their points; it passes to finite unions (`locJoin_biUnion`) and, more importantly, to
  a set with *shrinking* pieces attached (`locJoin_union_iUnion_of_shrinking`). A set locally
  joinable at each of its points is a locally path-connected space
  (`locallyPathConnectedSpace_of_locJoin`).
* **Closedness of shrinking unions.** `isClosed_union_iUnion_of_shrinking`: a closed set with
  closed pieces attached, all but finitely many of which lie in arbitrarily small balls about
  their attachment points, is closed.
* **Null-homotopy through a retraction.** If `r : W → M` fixes `M ∩ W` and `W` is simply
  connected (`homotopic_refl_of_retraction_of_simplyConnectedSpace`), e.g. convex in a real
  topological vector space (`homotopic_refl_of_retraction`), then every loop of `M` inside `W` is
  null-homotopic in `M`.

## Main statements

`LocJoin`, `Convex.locJoin`, `locJoin_range_of_periodic`, `isClosed_union_iUnion_of_shrinking`,
`locJoin_union_iUnion_of_shrinking`, `locallyPathConnectedSpace_of_locJoin`,
`homotopic_refl_of_retraction_of_simplyConnectedSpace`, `homotopic_refl_of_retraction`.

## Design choices

* `LocJoin` is a metric, pointwise notion about a *subset* of an ambient space, rather than a
  property of the subtype: this lets unions of subsets be handled directly, and avoids any general
  theory of null families. Mathlib's characterisation
  `locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds` converts it to
  `LocallyPathConnectedSpace` at the end.
* Everything is stated for pseudometric spaces, except `locJoin_range_of_periodic` (metric: it uses
  that compact sets are closed); the convexity lemmas live in real seminormed spaces, resp. real
  topological vector spaces.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace Peano

/-! ### Local joinability in pseudometric spaces -/

section LocJoin

variable {E : Type*} [PseudoMetricSpace E]

/-- `P` is *locally joinable at `p`*: points of `P` close to `p` are joined to `p` by paths in
`P` staying close to `p`. (For `p ∈ P` this is local path-connectedness of `P` at `p` "im
kleinen"; for `p ∉ P` it says nothing unless `p` is in the closure of `P`.) For a set locally
joinable at each of its points, the subtype is a `LocallyPathConnectedSpace`
(`locallyPathConnectedSpace_of_locJoin`, via Mathlib's
`locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds`). -/
def LocJoin (P : Set E) (p : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ q ∈ P, dist q p < δ → JoinedIn (P ∩ ball p ε) q p

/-- A closed set is locally joinable at every point outside it. -/
lemma locJoin_of_notMem {P : Set E} (hP : IsClosed P) {p : E} (hp : p ∉ P) : LocJoin P p := by
  intro ε _
  obtain ⟨δ, hδ, h⟩ := Metric.isOpen_iff.1 hP.isOpen_compl p hp
  exact ⟨δ, hδ, fun q hq hqp => absurd hq (h (mem_ball.2 hqp))⟩

/-- A closed set locally joinable at its own points is locally joinable everywhere. -/
lemma locJoin_of_isClosed {P : Set E} (hP : IsClosed P) (h : ∀ p ∈ P, LocJoin P p) (p : E) :
    LocJoin P p := by
  by_cases hp : p ∈ P
  · exact h p hp
  · exact locJoin_of_notMem hP hp

/-- Local joinability is preserved by binary unions. -/
lemma LocJoin.union {P Q : Set E} {p : E} (h : LocJoin P p) (h' : LocJoin Q p) :
    LocJoin (P ∪ Q) p := by
  intro ε hε
  obtain ⟨δ, hδ, hP⟩ := h ε hε
  obtain ⟨δ', hδ', hQ⟩ := h' ε hε
  refine ⟨min δ δ', lt_min hδ hδ', fun q hq hqp => ?_⟩
  rcases hq with hq | hq
  · exact (hP q hq (hqp.trans_le (min_le_left _ _))).mono
      (inter_subset_inter_left _ subset_union_left)
  · exact (hQ q hq (hqp.trans_le (min_le_right _ _))).mono
      (inter_subset_inter_left _ subset_union_right)

/-- The empty set is locally joinable everywhere. -/
lemma locJoin_empty (p : E) : LocJoin ∅ p :=
  fun _ _ => ⟨1, one_pos, fun q hq => absurd hq (notMem_empty q)⟩

/-- Local joinability is preserved by finite unions. -/
lemma locJoin_biUnion {ι : Type*} (F : Finset ι) (P : ι → Set E) {p : E}
    (h : ∀ i ∈ F, LocJoin (P i) p) : LocJoin (⋃ i ∈ F, P i) p := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using locJoin_empty p
  | insert i F _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self i F)).union
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- A convex set in a real seminormed space is locally joinable at its points. -/
lemma Convex.locJoin {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V}
    (hP : Convex ℝ P) {p : V} (hp : p ∈ P) : LocJoin P p := by
  intro ε hε
  refine ⟨ε, hε, fun q hq hqp => ?_⟩
  have hp' : p ∈ P ∩ ball p ε := ⟨hp, mem_ball_self hε⟩
  exact ((hP.inter (convex_ball p ε)).isPathConnected ⟨p, hp'⟩).joinedIn q ⟨hq, hqp⟩ p hp'

/-- The image of a `1`-periodic continuous curve which is injective modulo `1` (a simple closed
curve) is locally joinable at each of its points. (Stated in a metric space: the proof uses that
compact sets are closed.) -/
lemma locJoin_range_of_periodic {F : Type*} [MetricSpace F] {γ : ℝ → F} (hγ : Continuous γ)
    (hper : Function.Periodic γ 1)
    (hinj : ∀ t t', γ t = γ t' → ∃ n : ℤ, t = t' + n) (s₀ : ℝ) : LocJoin (range γ) (γ s₀) := by
  intro ε hε
  obtain ⟨η₀, hη₀, hη⟩ := Metric.continuous_iff.1 hγ s₀ ε hε
  set η := min η₀ (1 / 2) with hη_def
  have hηpos : 0 < η := lt_min hη₀ (by norm_num)
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηh : η ≤ 1 / 2 := min_le_right _ _
  set C := γ '' Icc (s₀ + η) (s₀ + 1 - η)
  have hC : IsClosed C := (isCompact_Icc.image hγ).isClosed
  have hpC : γ s₀ ∉ C := by
    rintro ⟨t, ⟨ht1, ht2⟩, he⟩
    obtain ⟨n, hn⟩ := hinj t s₀ he
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have h1' : 0 < n := by exact_mod_cast h1
    have h2' : n < 1 := by exact_mod_cast h2
    omega
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 hC.isOpen_compl _ hpC
  refine ⟨δ, hδ, ?_⟩
  rintro q ⟨t, rfl⟩ hq
  obtain ⟨t', ht', he⟩ := hper.exists_mem_Ico one_pos t s₀
  have : ∃ t'', |t'' - s₀| < η ∧ γ t = γ t'' := by
    have hnC : γ t' ∉ C := fun h => hδC (mem_ball.2 (he ▸ hq)) h
    by_cases h1 : t' < s₀ + η
    · exact ⟨t', by rw [abs_lt]; constructor <;> linarith [ht'.1], he⟩
    · have h2 : s₀ + 1 - η < t' := by
        by_contra! h2; exact hnC ⟨t', ⟨not_lt.1 h1, h2⟩, rfl⟩
      refine ⟨t' - 1, by rw [abs_lt]; constructor <;> linarith [ht'.2], ?_⟩
      rw [he]; exact (hper.sub_eq t').symm
  obtain ⟨t'', ht'', he'⟩ := this
  rw [he']
  have hpc : IsPathConnected (γ '' uIcc s₀ t'') :=
    ((convex_uIcc s₀ t'').isPathConnected nonempty_uIcc).image hγ
  refine (hpc.joinedIn _ (mem_image_of_mem _ right_mem_uIcc) _
    (mem_image_of_mem _ left_mem_uIcc)).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨mem_range_self x, mem_ball.2 (hη x ?_)⟩
  rw [Real.dist_eq]
  exact (abs_sub_left_of_mem_uIcc hx).trans_lt (ht''.trans_le hηη₀)

/-- **Closedness of a union of shrinking pieces.** If `S` is closed and the closed pieces `P i`
lie, apart from finitely many, in arbitrarily small balls about points `b i ∈ S` (the shrinking
hypothesis `hsmall`), then `S ∪ ⋃ i, P i` is closed. -/
lemma isClosed_union_iUnion_of_shrinking {S : Set E} (hS : IsClosed S) {ι : Type*}
    (P : ι → Set E) (hP : ∀ i, IsClosed (P i)) (b : ι → E) (hb : ∀ i, b i ∈ S)
    (hsmall : ∀ ε > 0, {i | ¬ P i ⊆ closedBall (b i) ε}.Finite) :
    IsClosed (S ∪ ⋃ i, P i) := by
  refine isClosed_of_closure_subset fun x hxcl => ?_
  by_contra hx
  have hxS : x ∉ S := fun h => hx (Or.inl h)
  obtain ⟨d, hd, hdS⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hxS
  have hF := hsmall (d / 2) (half_pos hd)
  have hB : IsClosed (⋃ i ∈ {i | ¬ P i ⊆ closedBall (b i) (d / 2)}, P i) :=
    hF.isClosed_biUnion fun i _ => hP i
  have hxB : x ∉ ⋃ i ∈ {i | ¬ P i ⊆ closedBall (b i) (d / 2)}, P i := fun h => by
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 h
    exact hx (Or.inr (mem_iUnion.2 ⟨i, hi⟩))
  obtain ⟨d', hd', hdB⟩ := Metric.isOpen_iff.1 hB.isOpen_compl x hxB
  obtain ⟨y, hyM, hy⟩ := Metric.mem_closure_iff.1 hxcl (min (d / 2) d') (by positivity)
  have hy1 : dist y x < d / 2 := by rw [dist_comm]; exact hy.trans_le (min_le_left _ _)
  have hy2 : dist y x < d' := by rw [dist_comm]; exact hy.trans_le (min_le_right _ _)
  rcases hyM with hyS | hyP
  · exact hdS (mem_ball.2 (by linarith)) hyS
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hyP
    by_cases hiF : i ∈ {i | ¬ P i ⊆ closedBall (b i) (d / 2)}
    · exact hdB (mem_ball.2 hy2) (mem_iUnion₂.2 ⟨i, hiF, hi⟩)
    · have hsub : P i ⊆ closedBall (b i) (d / 2) := not_not.1 hiF
      have h1 : dist y (b i) ≤ d / 2 := hsub hi
      have h2 : dist (b i) x < d := by
        calc dist (b i) x ≤ dist (b i) y + dist y x := dist_triangle _ _ _
          _ < d := by rw [dist_comm]; linarith
      exact hdS (mem_ball.2 h2) (hb i)

/-- **Local joinability of a union of shrinking pieces.** Let `S` and the pieces `P i` be locally
joinable everywhere, every point of `P i` be joined in `P i` to a point `b i ∈ S`, and all but
finitely many pieces lie in arbitrarily small balls about their points `b i` (the shrinking
hypothesis `hsmall`). Then `S ∪ ⋃ i, P i` is locally joinable everywhere. -/
theorem locJoin_union_iUnion_of_shrinking {S : Set E} {ι : Type*} (P : ι → Set E) (b : ι → E)
    (hS : ∀ p, LocJoin S p) (hP : ∀ i p, LocJoin (P i) p) (hb : ∀ i, b i ∈ S)
    (hjoin : ∀ i, ∀ q ∈ P i, JoinedIn (P i) q (b i))
    (hsmall : ∀ ε > 0, {i | ¬ P i ⊆ closedBall (b i) ε}.Finite) (p : E) :
    LocJoin (S ∪ ⋃ i, P i) p := by
  intro ε hε
  obtain ⟨ρ, hρ, hSρ⟩ := hS p ε hε
  set ε' := min (ε / 4) (ρ / 2) with hε'_def
  have hε' : 0 < ε' := by positivity
  have hε'1 : ε' ≤ ε / 4 := min_le_left _ _
  have hε'2 : ε' ≤ ρ / 2 := min_le_right _ _
  set F := (hsmall ε' hε').toFinset
  obtain ⟨δB, hδB, hB⟩ := locJoin_biUnion F P (fun i _ => hP i p) ε hε
  set δ := min δB (min (ρ / 2) (ε / 4)) with hδ_def
  have hδ1 : δ ≤ δB := min_le_left _ _
  have hδ2 : δ ≤ ρ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ ε / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, by positivity, fun q hq hqp => ?_⟩
  have hsub : ∀ T ⊆ S ∪ ⋃ i, P i, T ∩ ball p ε ⊆ (S ∪ ⋃ i, P i) ∩ ball p ε :=
    fun T hT => inter_subset_inter_left _ hT
  rcases hq with hq | hq
  · exact (hSρ q hq (by linarith)).mono (hsub S subset_union_left)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hq
    by_cases hiF : i ∈ F
    · refine (hB q (mem_iUnion₂.2 ⟨i, hiF, hi⟩) (hqp.trans_le hδ1)).mono (hsub _ ?_)
      exact iUnion₂_subset fun j _ => (subset_iUnion P j).trans subset_union_right
    · have hsm : P i ⊆ closedBall (b i) ε' := by simpa [F] using hiF
      have hqb : dist q (b i) ≤ ε' := hsm hi
      have hbp : dist (b i) p < ρ := by
        calc dist (b i) p ≤ dist (b i) q + dist q p := dist_triangle _ _ _
          _ < ρ := by rw [dist_comm]; linarith
      have h1 : JoinedIn (S ∩ ball p ε) (b i) p := hSρ (b i) (hb i) hbp
      have h2 : JoinedIn ((S ∪ ⋃ i, P i) ∩ ball p ε) q (b i) := by
        refine (hjoin i q hi).mono fun x hx => ⟨Or.inr (mem_iUnion.2 ⟨i, hx⟩), ?_⟩
        have hxb : dist x (b i) ≤ ε' := hsm hx
        rw [mem_ball]
        calc dist x p ≤ dist x (b i) + dist (b i) p := dist_triangle _ _ _
          _ ≤ dist x (b i) + (dist (b i) q + dist q p) := by gcongr; exact dist_triangle _ _ _
          _ < ε := by rw [dist_comm (b i) q]; linarith
      exact h2.trans (h1.mono (hsub S subset_union_left))

/-- A space whose underlying set is locally joinable at each of its points (in an ambient
pseudometric space) is locally path-connected. -/
theorem locallyPathConnectedSpace_of_locJoin {M : Set E} (h : ∀ p ∈ M, LocJoin M p) :
    LocallyPathConnectedSpace M := by
  rw [locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds]
  intro x U hU hxU
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
  obtain ⟨δ, hδ, hj⟩ := h x x.2 ε hε
  refine Filter.mem_of_superset (ball_mem_nhds x hδ) fun y hy => ?_
  obtain ⟨γ, hγ⟩ := hj y y.2 hy
  refine JoinedIn.symm ⟨⟨⟨fun t => ⟨γ t, (hγ t).1⟩, ?_⟩, ?_, ?_⟩, fun t => hεU ?_⟩
  · exact (γ.continuous).subtype_mk _
  · ext; simp
  · ext; simp
  · exact (hγ t).2

end LocJoin

/-! ### Null-homotopy through a retraction -/

/-- **Null-homotopy through a retraction of a simply connected set.** Let `W ⊆ X` be simply
connected and `r : W → M` continuous, fixing the points of `M ∩ W`. Then every loop in `M` whose
image lies in `W` is null-homotopic in `M`. (Contract the loop in `W`, then push the contraction
into `M` by `r`.) -/
theorem homotopic_refl_of_retraction_of_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    {M W : Set X} [SimplyConnectedSpace W] (r : X → X) (hr : ContinuousOn r W)
    (hrM : MapsTo r W M) (hfix : ∀ y ∈ W, y ∈ M → r y = y) {x : M} (γ : Path x x)
    (hγ : ∀ t, (γ t : X) ∈ W) : γ.Homotopic (Path.refl x) := by
  have hxW : (x : X) ∈ W := by simpa using hγ 0
  let xW : W := ⟨x, hxW⟩
  let γW : Path xW xW :=
    { toFun := fun t => ⟨γ t, hγ t⟩
      continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _
      source' := Subtype.ext (by simp [xW])
      target' := Subtype.ext (by simp [xW]) }
  let ρ : C(W, M) := ⟨fun y => ⟨r y, hrM y.2⟩,
    (continuousOn_iff_continuous_domRestrict.1 hr).subtype_mk _⟩
  have h := (SimplyConnectedSpace.paths_homotopic γW (Path.refl xW)).map ρ
  have hx : x = ρ xW := Subtype.ext (hfix x hxW x.2).symm
  have e1 : (γW.map ρ.continuous).cast hx hx = γ :=
    Path.ext <| funext fun t => Subtype.ext <| hfix _ (hγ t) (γ t).2
  have e2 : ((Path.refl xW).map ρ.continuous).cast hx hx = Path.refl x :=
    Path.ext <| funext fun t => Subtype.ext <| hfix _ hxW x.2
  rw [← e1, ← e2]
  exact (homotopic_cast_iff _ _ hx hx).2 h

/-- **Null-homotopy through a retraction of a convex set.** Let `W` be a convex set in a real
topological vector space and `r : W → M` continuous, fixing the points of `M ∩ W`. Then every
loop in `M` whose image lies in `W` is null-homotopic in `M`. -/
theorem homotopic_refl_of_retraction {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {M W : Set V}
    (hW : Convex ℝ W) (r : V → V) (hr : ContinuousOn r W) (hrM : MapsTo r W M)
    (hfix : ∀ y ∈ W, y ∈ M → r y = y) {x : M} (γ : Path x x) (hγ : ∀ t, (γ t : V) ∈ W) :
    γ.Homotopic (Path.refl x) := by
  have hxW : (x : V) ∈ W := by simpa using hγ 0
  have : ContractibleSpace W := hW.contractibleSpace ⟨x, hxW⟩
  exact homotopic_refl_of_retraction_of_simplyConnectedSpace r hr hrM hfix γ hγ

end Peano
