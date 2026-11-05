module

public import Peano.Arcs
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The coarsification `𝒞X` and its lifting lemma (§5)

Brazas–Pavešić, §5: the construction, Remark 5.1, Lemma 5.2, Lemma 5.4, Lemma 5.5.

Construction. For the arc `Oᵢ = hᵢ((0,1))` put `Bᵢ = hᵢ((0, ½))`, `Cᵢ = {hᵢ(½)}`,
`Dᵢ = hᵢ((½, 1))`. `𝒞X` is the quotient of `X` collapsing each `Bᵢ` and each `Dᵢ` to a point.
Encoding: the identification is the kernel of the labelling `label : X → X ⊕ (ι × Bool)`, sending
`Bᵢ` to `inr (i, false)`, `Dᵢ` to `inr (i, true)` and every other point `x` to `inl x`; the paper's
`bᵢ, dᵢ` are the classes of `inr (i, false)`, `inr (i, true)`. This avoids proving by hand that the
identification is an equivalence relation. `Coarse S` carries the quotient topology, and
`q : C(X, Coarse S)` is the quotient map. (Collapsing the singletons `Cᵢ` changes nothing.)

The paper identifies `w(X) ∪ {cᵢ}` with its image in `𝒞X`; here `q` is kept explicit.

Proofs (following the repairs of `notes/checks/C.md`). The halves are indexed uniformly by
`p = (i, β) : ι × Bool` (`half p`, parametrised by `halfArc p = hᵢ ∘ (t ↦ (c + t) / 2)`), and
`core` is the set `F = W ∪ {cᵢ}` of points with singleton fibres; `pt p` is `bᵢ` or `dᵢ`. A half is
open as the open arc minus the compact other closed half.
* Lemma 5.2 is proved directly: `q⁻¹(q V)` is `V` together with the halves meeting `V` (Lemma 4.5
  of the paper is not used).
* Lemma 5.4′ is `Φ = (1 - ρ) ψ + ρ / 2` with `ψ` a Tietze extension and `ρ = min 1 (d(·, A))`;
  Lemma 5.4 is a corollary.
* Lemma 5.5: `k` is `f` on `A` and `q|_F⁻¹ ∘ g` on `g⁻¹(q F)`. For each half `p`, `exists_piece`
  gives the half-arc coordinate `Φ p : B → I` with `halfArc p ∘ Φ p = k` on
  `g⁻¹(q B̄) ∩ (A ∪ g⁻¹(q F))` and values in `(0, 1)` elsewhere; the lift is `halfArc p ∘ Φ p` over
  `pt p` and `k` elsewhere. Continuity at points over `q F` uses the null hypothesis with balls
  (finitely many large arcs, handled by continuity of `halfArc p ∘ Φ p` on all of `B`).
-/

@[expose] public section

open Set Filter Topology unitInterval

noncomputable section

namespace Peano

namespace ArcSystem

variable {X : Type*} [MetricSpace X] (S : ArcSystem X)

/-- The first half `Bᵢ = hᵢ((0, ½))` of the `i`-th arc. -/
def firstHalf (i : S.ι) : Set X := S.h i '' {t | (0 : ℝ) < t ∧ (t : ℝ) < 1 / 2}

/-- The second half `Dᵢ = hᵢ((½, 1))` of the `i`-th arc. -/
def secondHalf (i : S.ι) : Set X := S.h i '' {t | (1 / 2 : ℝ) < t ∧ (t : ℝ) < 1}

open Classical in
/-- The labelling whose fibres are the points of `𝒞X`: `Bᵢ ↦ inr (i, false)`,
`Dᵢ ↦ inr (i, true)`, any other `x ↦ inl x`. -/
def label (x : X) : X ⊕ (S.ι × Bool) :=
  if hb : ∃ i, x ∈ S.firstHalf i then .inr (hb.choose, false)
  else if hd : ∃ i, x ∈ S.secondHalf i then .inr (hd.choose, true)
  else .inl x

/-- The coarsification `𝒞X`: the quotient of `X` by the fibres of `label`. -/
def Coarse : Type _ := Quotient (Setoid.ker S.label)

/-- The coarsification carries the quotient topology. -/
instance : TopologicalSpace S.Coarse := inferInstanceAs (TopologicalSpace (Quotient _))

/-- The coarsification map `q : X → 𝒞X`. -/
def q : C(X, S.Coarse) := ⟨Quotient.mk _, continuous_quotient_mk'⟩


/-! ### Halves of an arc

The two halves of the `i`-th arc are indexed uniformly by `p = (i, β) : ι × Bool`, with `β = false`
for `Bᵢ` and `β = true` for `Dᵢ`. The closed half is parametrised by `halfArc p = hᵢ ∘ halfParam β`,
where `halfParam β : t ↦ (c + t) / 2` with `c = 0` or `1`. -/

/-- The offset `c = 0` (first half) or `c = 1` (second half). -/
def halfOffset (β : Bool) : ℝ := if β then 1 else 0

/-- The offset of the first half is `0`. -/
@[simp] lemma halfOffset_false : halfOffset false = 0 := rfl

/-- The offset of the second half is `1`. -/
@[simp] lemma halfOffset_true : halfOffset true = 1 := rfl

/-- The affine map `t ↦ (c + t) / 2` from `I` onto the half `[c / 2, (c + 1) / 2]` of `I`. -/
def halfParam (β : Bool) : C(I, I) where
  toFun t := ⟨(halfOffset β + t) / 2, by
    constructor <;> cases β <;> simp only [halfOffset_false, halfOffset_true] <;>
      linarith [t.2.1, t.2.2]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- `halfParam β t = (c + t) / 2` in real coordinates. -/
@[simp] lemma coe_halfParam (β : Bool) (t : I) :
    ((halfParam β t : I) : ℝ) = (halfOffset β + t) / 2 := rfl

/-- The midpoint `½ ∈ I`. -/
def midI : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- `midI = ½` in real coordinates. -/
@[simp] lemma coe_midI : ((midI : I) : ℝ) = 1 / 2 := rfl

/-- Membership in `openUnit`, in real coordinates. -/
lemma mem_openUnit_iff {u : I} : u ∈ openUnit ↔ (0 : ℝ) < u ∧ (u : ℝ) < 1 := Iff.rfl

/-- `½ ∈ (0, 1)`. -/
lemma midI_mem_openUnit : midI ∈ openUnit := by
  rw [mem_openUnit_iff, coe_midI]; norm_num

/-- A point of `I` outside `(0, 1)` is an end point. -/
lemma eq_zero_or_eq_one_of_notMem_openUnit {u : I} (hu : u ∉ openUnit) : u = 0 ∨ u = 1 := by
  rw [mem_openUnit_iff, not_and_or, not_lt, not_lt] at hu
  rcases hu with hu | hu
  · exact Or.inl (Subtype.ext (le_antisymm hu u.2.1))
  · exact Or.inr (Subtype.ext (le_antisymm u.2.2 hu))

/-- The range of `halfParam β` is `[c / 2, (c + 1) / 2]`. -/
lemma mem_range_halfParam {β : Bool} {u : I} :
    u ∈ range (halfParam β) ↔ halfOffset β / 2 ≤ u ∧ (u : ℝ) ≤ (halfOffset β + 1) / 2 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp only [coe_halfParam]
    constructor <;> linarith [t.2.1, t.2.2]
  · rintro ⟨h1, h2⟩
    refine ⟨⟨2 * u - halfOffset β, ?_, ?_⟩, Subtype.ext ?_⟩
    · cases β <;> simp only [halfOffset_false, halfOffset_true] at h1 h2 ⊢ <;>
        linarith [u.2.1, u.2.2]
    · cases β <;> simp only [halfOffset_false, halfOffset_true] at h1 h2 ⊢ <;>
        linarith [u.2.1, u.2.2]
    · simp only [coe_halfParam]; ring

/-- The image of `(0, 1)` under `halfParam β` is `(c / 2, (c + 1) / 2)`. -/
lemma mem_image_halfParam_openUnit {β : Bool} {u : I} :
    u ∈ halfParam β '' openUnit ↔ halfOffset β / 2 < u ∧ (u : ℝ) < (halfOffset β + 1) / 2 := by
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    simp only [coe_halfParam]
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨⟨2 * u - halfOffset β, ?_, ?_⟩, ⟨?_, ?_⟩, Subtype.ext ?_⟩
    · cases β <;> simp only [halfOffset_false, halfOffset_true] at h1 h2 ⊢ <;>
        linarith [u.2.1, u.2.2]
    · cases β <;> simp only [halfOffset_false, halfOffset_true] at h1 h2 ⊢ <;>
        linarith [u.2.1, u.2.2]
    · show (0 : ℝ) < 2 * u - halfOffset β
      cases β <;> simp only [halfOffset_false, halfOffset_true] at h1 h2 ⊢ <;>
        linarith [u.2.1, u.2.2]
    · show 2 * (u : ℝ) - halfOffset β < 1
      cases β <;> simp only [halfOffset_false, halfOffset_true] at h1 h2 ⊢ <;>
        linarith [u.2.1, u.2.2]
    · simp only [coe_halfParam]; ring

/-- `halfParam β` maps `(0, 1)` into `(0, 1)`. -/
lemma image_halfParam_openUnit_subset (β : Bool) : halfParam β '' openUnit ⊆ openUnit := by
  intro u hu
  rw [mem_image_halfParam_openUnit] at hu
  rw [mem_openUnit_iff]
  cases β <;> simp only [halfOffset_false, halfOffset_true] at hu <;>
    constructor <;> linarith [hu.1, hu.2]

/-- Open arcs avoid `W`. -/
lemma arc_subset_compl_W (i : S.ι) : S.arc i ⊆ S.Wᶜ := by
  rw [← S.iUnion_eq]; exact subset_iUnion (fun j => S.h j '' openUnit) i

/-- Two open arcs sharing a point coincide. -/
lemma eq_of_mem_arc {i j : S.ι} {x : X} (hi : x ∈ S.arc i) (hj : x ∈ S.arc j) : i = j := by
  by_contra hij
  exact (S.disjoint hij).le_bot ⟨hi, hj⟩

/-- `hᵢ` is injective at interior parameters: `hᵢ u = hᵢ v ↔ u = v` for `u ∈ (0, 1)`. -/
lemma h_eq_iff {i : S.ι} {u v : I} (hu : u ∈ openUnit) : S.h i u = S.h i v ↔ u = v := by
  refine ⟨fun huv => ?_, fun huv => huv ▸ rfl⟩
  by_cases hv : v ∈ openUnit
  · exact S.injOn i hu hv huv
  · exfalso
    have hW : S.h i v ∈ S.W := by
      rcases eq_zero_or_eq_one_of_notMem_openUnit hv with rfl | rfl
      exacts [(S.mem_W i).1, (S.mem_W i).2]
    exact S.arc_subset_compl_W i ⟨u, hu, rfl⟩ (huv ▸ hW)

/-- The parametrisation `hᵢ ∘ halfParam β` of the closed half `p = (i, β)`. -/
def halfArc (p : S.ι × Bool) : C(I, X) := (S.h p.1).comp (halfParam p.2)

/-- Unfolding `halfArc`. -/
lemma halfArc_apply (p : S.ι × Bool) (t : I) : S.halfArc p t = S.h p.1 (halfParam p.2 t) := rfl

/-- The open half `p = (i, β)`: `Bᵢ` for `β = false`, `Dᵢ` for `β = true`. -/
def half (p : S.ι × Bool) : Set X := S.halfArc p '' openUnit

/-- The open half `p = (i, β)` is `hᵢ((c / 2, (c + 1) / 2))`. -/
lemma half_eq_image (p : S.ι × Bool) :
    S.half p = S.h p.1 '' (halfParam p.2 '' openUnit) := by
  simp only [half, halfArc, ContinuousMap.coe_comp, image_comp]

/-- `Bᵢ` is the half `(i, false)`. -/
lemma firstHalf_eq_half (i : S.ι) : S.firstHalf i = S.half (i, false) := by
  rw [half_eq_image, firstHalf]
  congr 1
  ext u
  rw [mem_image_halfParam_openUnit, halfOffset_false]
  norm_num

/-- `Dᵢ` is the half `(i, true)`. -/
lemma secondHalf_eq_half (i : S.ι) : S.secondHalf i = S.half (i, true) := by
  rw [half_eq_image, secondHalf]
  congr 1
  ext u
  rw [mem_image_halfParam_openUnit, halfOffset_true]
  norm_num

/-- Each open half lies in its open arc. -/
lemma half_subset_arc (p : S.ι × Bool) : S.half p ⊆ S.arc p.1 := by
  rw [half_eq_image]
  exact image_mono (image_halfParam_openUnit_subset p.2)

/-- `halfArc p` maps `(0, 1)` into the open half `p`. -/
lemma halfArc_mem_half {p : S.ι × Bool} {t : I} (ht : t ∈ openUnit) : S.halfArc p t ∈ S.half p :=
  mem_image_of_mem _ ht

/-- Each closed half lies in its closed arc. -/
lemma range_halfArc_subset (p : S.ι × Bool) : range (S.halfArc p) ⊆ S.closedArc p.1 := by
  rintro _ ⟨t, rfl⟩; exact ⟨_, rfl⟩

/-- Each open half lies in its closed arc. -/
lemma half_subset_closedArc (p : S.ι × Bool) : S.half p ⊆ S.closedArc p.1 :=
  (image_subset_range _ _).trans (S.range_halfArc_subset p)

/-- Distinct halves are disjoint. -/
lemma eq_of_mem_half {p p' : S.ι × Bool} {x : X} (hp : x ∈ S.half p) (hp' : x ∈ S.half p') :
    p = p' := by
  obtain ⟨i, β⟩ := p
  obtain ⟨j, β'⟩ := p'
  have hij : i = j := S.eq_of_mem_arc (S.half_subset_arc _ hp) (S.half_subset_arc _ hp')
  subst hij
  rw [half_eq_image] at hp hp'
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨v, hv, huv⟩ := hp'
  have hu' := image_halfParam_openUnit_subset _ hu
  rw [eq_comm, S.h_eq_iff hu'] at huv
  subst huv
  rw [mem_image_halfParam_openUnit] at hu hv
  cases β <;> cases β' <;> simp only [halfOffset_false, halfOffset_true] at hu hv
  all_goals first | rfl | (exfalso; linarith [hu.1, hu.2, hv.1, hv.2])

/-- The parametrisation of a closed half is injective (so a closed half is an arc). -/
lemma halfArc_injective (p : S.ι × Bool) : Function.Injective (S.halfArc p) := by
  obtain ⟨i, β⟩ := p
  intro s t hst
  rw [halfArc_apply, halfArc_apply] at hst
  have key : halfParam β s = halfParam β t := by
    by_cases hs : halfParam β s ∈ openUnit
    · exact (S.h_eq_iff hs).1 hst
    by_cases ht : halfParam β t ∈ openUnit
    · exact ((S.h_eq_iff ht).1 hst.symm).symm
    rw [mem_openUnit_iff, coe_halfParam, not_and_or, not_lt, not_lt] at hs ht
    apply Subtype.ext
    rw [coe_halfParam, coe_halfParam]
    cases β <;> simp only [halfOffset_false, halfOffset_true] at hs ht ⊢ <;>
      rcases hs with hs | hs <;> rcases ht with ht | ht <;>
      linarith [s.2.1, s.2.2, t.2.1, t.2.2]
  have := congrArg (fun u : I => (u : ℝ)) key
  simp only [coe_halfParam] at this
  exact Subtype.ext (by linarith)

/-- The halves `Bᵢ, Dᵢ` are open in `X`: the half `(i, β)` is the open arc minus the
compact other closed half. -/
lemma isOpen_half (p : S.ι × Bool) : IsOpen (S.half p) := by
  obtain ⟨i, β⟩ := p
  have : S.half (i, β) = S.arc i \ range (S.halfArc (i, !β)) := by
    ext x
    constructor
    · intro hx
      refine ⟨S.half_subset_arc _ hx, ?_⟩
      rintro ⟨v, rfl⟩
      rw [half_eq_image] at hx
      obtain ⟨u, hu, huv⟩ := hx
      have hu' := image_halfParam_openUnit_subset _ hu
      rw [halfArc_apply, S.h_eq_iff hu'] at huv
      rw [mem_image_halfParam_openUnit] at hu
      have hv := (mem_range_halfParam (β := !β)).1 ⟨v, rfl⟩
      rw [← huv] at hv
      cases β <;> simp only [halfOffset_false, halfOffset_true, Bool.not_false,
        Bool.not_true] at hu hv <;> linarith [hu.1, hu.2, hv.1, hv.2]
    · rintro ⟨⟨u, hu, rfl⟩, hx⟩
      rw [half_eq_image]
      refine mem_image_of_mem _ ((mem_image_halfParam_openUnit).2 ?_)
      by_contra hc
      apply hx
      have key : halfOffset (!β) / 2 ≤ (u : ℝ) ∧ (u : ℝ) ≤ (halfOffset (!β) + 1) / 2 := by
        rw [mem_openUnit_iff] at hu
        rw [not_and_or, not_lt, not_lt] at hc
        cases β <;> simp only [halfOffset_false, halfOffset_true, Bool.not_false,
          Bool.not_true] at hc ⊢ <;> rcases hc with hc | hc <;>
          constructor <;> linarith [hu.1, hu.2]
      obtain ⟨v, hv⟩ := (mem_range_halfParam (β := !β)).2 key
      exact ⟨v, by rw [halfArc_apply, hv]⟩
  rw [this]
  exact (S.isOpen_arc i).sdiff (isCompact_range (S.halfArc _).continuous).isClosed


/-! ### The set `F` of points with singleton fibres, and the points of `𝒞X` -/

/-- The points of `X` outside every half, `F = W ∪ {cᵢ}`: the fibres of `q` over them are
singletons. -/
def core : Set X := {x | ∀ p, x ∉ S.half p}

/-- `F` is closed: its complement is the union of the open halves. -/
lemma isClosed_core : IsClosed S.core := by
  have : S.core = (⋃ p, S.half p)ᶜ := by ext x; simp [core]
  rw [this]
  exact (isOpen_iUnion S.isOpen_half).isClosed_compl

/-- Every point lies in `F` or in some half. -/
lemma mem_core_or_mem_half (x : X) : x ∈ S.core ∨ ∃ p, x ∈ S.half p := by
  by_cases hx : x ∈ S.core
  · exact Or.inl hx
  · simp only [core, mem_ofPred_eq, not_forall, not_not] at hx
    exact Or.inr hx

/-- `W ⊆ F`. -/
lemma W_subset_core : S.W ⊆ S.core := fun _ hx p hp =>
  S.arc_subset_compl_W p.1 (S.half_subset_arc p hp) hx

/-- The midpoints `cᵢ = hᵢ(½)` lie in `F`. -/
lemma h_midI_mem_core (i : S.ι) : S.h i midI ∈ S.core := by
  intro ⟨j, β⟩ hx
  have hij : i = j := S.eq_of_mem_arc ⟨midI, midI_mem_openUnit, rfl⟩ (S.half_subset_arc _ hx)
  subst hij
  rw [half_eq_image] at hx
  obtain ⟨u, hu, huv⟩ := hx
  rw [S.h_eq_iff (image_halfParam_openUnit_subset _ hu)] at huv
  rw [mem_image_halfParam_openUnit, huv, coe_midI] at hu
  cases β <;> simp only [halfOffset_false, halfOffset_true] at hu <;> linarith [hu.1, hu.2]

/-- The end points `aᵢ, cᵢ` (resp. `cᵢ, eᵢ`) of a closed half lie in `F`. -/
lemma halfArc_mem_core_of_notMem_openUnit (p : S.ι × Bool) {t : I} (ht : t ∉ openUnit) :
    S.halfArc p t ∈ S.core := by
  obtain ⟨i, β⟩ := p
  rw [halfArc_apply]
  rcases eq_zero_or_eq_one_of_notMem_openUnit ht with rfl | rfl <;> cases β
  · convert S.W_subset_core (S.mem_W i).1
    exact Subtype.ext (by simp)
  · convert S.h_midI_mem_core i
    exact Subtype.ext (by simp)
  · convert S.h_midI_mem_core i
    exact Subtype.ext (by simp)
  · convert S.W_subset_core (S.mem_W i).2
    exact Subtype.ext (by norm_num)

/-- The label of a point of the half `p` is `inr p`. -/
lemma label_of_mem_half {p : S.ι × Bool} {x : X} (hx : x ∈ S.half p) :
    S.label x = .inr p := by
  obtain ⟨i, β⟩ := p
  cases β
  · have hb : ∃ j, x ∈ S.firstHalf j := ⟨i, (S.firstHalf_eq_half i).symm ▸ hx⟩
    have hc := hb.choose_spec
    rw [firstHalf_eq_half] at hc
    have := S.eq_of_mem_half hc hx
    simp only [label, hb, dite_eq_left]
    rw [show hb.choose = i from congrArg Prod.fst this]
  · have hb : ¬ ∃ j, x ∈ S.firstHalf j := by
      rintro ⟨j, hj⟩
      rw [firstHalf_eq_half] at hj
      exact absurd (congrArg Prod.snd (S.eq_of_mem_half hj hx)) (by simp)
    have hd : ∃ j, x ∈ S.secondHalf j := ⟨i, (S.secondHalf_eq_half i).symm ▸ hx⟩
    have hc := hd.choose_spec
    rw [secondHalf_eq_half] at hc
    have := S.eq_of_mem_half hc hx
    simp only [label, hb, hd, dite_eq_left, dite_eq_right, not_false_eq_true]
    rw [show hd.choose = i from congrArg Prod.fst this]

/-- The label of a point `x ∈ F` is `inl x`. -/
lemma label_of_mem_core {x : X} (hx : x ∈ S.core) : S.label x = .inl x := by
  have hb : ¬ ∃ j, x ∈ S.firstHalf j := by
    rintro ⟨j, hj⟩; rw [firstHalf_eq_half] at hj; exact hx _ hj
  have hd : ¬ ∃ j, x ∈ S.secondHalf j := by
    rintro ⟨j, hj⟩; rw [secondHalf_eq_half] at hj; exact hx _ hj
  simp only [label, hb, hd, dite_eq_right, not_false_eq_true]

/-- Unfolding `q`. -/
lemma q_apply (x : X) : S.q x = Quotient.mk _ x := rfl

/-- Two points have the same image in `𝒞X` iff they have the same label. -/
lemma q_eq_q_iff {x y : X} : S.q x = S.q y ↔ S.label x = S.label y := by
  show (Quotient.mk _ x : Quotient (Setoid.ker S.label)) = Quotient.mk _ y ↔ _
  exact Quotient.eq.trans Setoid.ker_def

/-- The coarsification map is surjective. -/
lemma q_surjective : Function.Surjective S.q := Quotient.mk_surjective

/-- The fibre of `q` over a point of `F` is a singleton. -/
lemma eq_of_q_eq_of_mem_core {x y : X} (hx : x ∈ S.core) (h : S.q y = S.q x) : y = x := by
  rw [q_eq_q_iff, S.label_of_mem_core hx] at h
  rcases S.mem_core_or_mem_half y with hy | ⟨p, hy⟩
  · rw [S.label_of_mem_core hy] at h; exact Sum.inl.inj h
  · rw [S.label_of_mem_half hy] at h; exact absurd h (by simp)

/-- The halves are saturated. -/
lemma mem_half_of_q_eq {p : S.ι × Bool} {x y : X} (hx : x ∈ S.half p) (h : S.q y = S.q x) :
    y ∈ S.half p := by
  rw [q_eq_q_iff, S.label_of_mem_half hx] at h
  rcases S.mem_core_or_mem_half y with hy | ⟨p', hy⟩
  · rw [S.label_of_mem_core hy] at h; exact absurd h (by simp)
  · rw [S.label_of_mem_half hy] at h; exact Sum.inr.inj h ▸ hy

/-- Points of the same half have the same image in `𝒞X`. -/
lemma q_eq_q_of_mem_half {p : S.ι × Bool} {x y : X} (hx : x ∈ S.half p) (hy : y ∈ S.half p) :
    S.q x = S.q y := by
  rw [q_eq_q_iff, S.label_of_mem_half hx, S.label_of_mem_half hy]

/-- The point `bᵢ` (for `p = (i, false)`) or `dᵢ` (for `p = (i, true)`) of `𝒞X`. -/
def pt (p : S.ι × Bool) : S.Coarse := S.q (S.halfArc p midI)

/-- `q⁻¹{bᵢ} = Bᵢ` and `q⁻¹{dᵢ} = Dᵢ`, pointwise. -/
lemma q_eq_pt_iff {p : S.ι × Bool} {x : X} : S.q x = S.pt p ↔ x ∈ S.half p :=
  ⟨fun h => S.mem_half_of_q_eq (S.halfArc_mem_half midI_mem_openUnit) h,
    fun h => S.q_eq_q_of_mem_half h (S.halfArc_mem_half midI_mem_openUnit)⟩

/-- `q⁻¹{bᵢ} = Bᵢ` and `q⁻¹{dᵢ} = Dᵢ`. -/
lemma preimage_q_pt (p : S.ι × Bool) : S.q ⁻¹' {S.pt p} = S.half p := by
  ext x; exact S.q_eq_pt_iff

/-- The quotient topology of `𝒞X`. -/
lemma isOpen_coarse_iff {U : Set S.Coarse} : IsOpen U ↔ IsOpen (S.q ⁻¹' U) := Iff.rfl

/-- Closed sets of `𝒞X` are those with closed preimage. -/
lemma isClosed_coarse_iff {U : Set S.Coarse} : IsClosed U ↔ IsClosed (S.q ⁻¹' U) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff, isOpen_coarse_iff, preimage_compl]

/-- `{bᵢ}` and `{dᵢ}` are open in `𝒞X`. -/
lemma isOpen_singleton_pt (p : S.ι × Bool) : IsOpen {S.pt p} := by
  rw [isOpen_coarse_iff, preimage_q_pt]; exact S.isOpen_half p

/-- The points `bᵢ, dᵢ` are pairwise distinct. -/
lemma pt_injective : Function.Injective S.pt := fun p p' h =>
  S.eq_of_mem_half (S.halfArc_mem_half midI_mem_openUnit)
    ((S.q_eq_pt_iff).1 (h ▸ rfl : S.q (S.halfArc p midI) = S.pt p'))

/-- The points `bᵢ, dᵢ` are not images of points of `F`. -/
lemma q_ne_pt {x : X} (hx : x ∈ S.core) (p : S.ι × Bool) : S.q x ≠ S.pt p := fun h =>
  hx p ((S.q_eq_pt_iff).1 h)

/-- Every point of `𝒞X` is the image of a point of `F`, or some `bᵢ` or `dᵢ`. -/
lemma exists_core_or_eq_pt (y : S.Coarse) : (∃ x ∈ S.core, S.q x = y) ∨ ∃ p, y = S.pt p := by
  obtain ⟨x, rfl⟩ := S.q_surjective y
  rcases S.mem_core_or_mem_half x with hx | ⟨p, hx⟩
  · exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr ⟨p, (S.q_eq_pt_iff).2 hx⟩

/-- `F` is saturated. -/
lemma preimage_image_core : S.q ⁻¹' (S.q '' S.core) = S.core := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro y ⟨x, hx, hxy⟩
  exact S.eq_of_q_eq_of_mem_core hx hxy.symm ▸ hx

/-- `q(F)` is closed in `𝒞X`. -/
lemma isClosed_image_core : IsClosed (S.q '' S.core) := by
  rw [isClosed_coarse_iff, preimage_image_core]; exact S.isClosed_core

/-- The closed halves are saturated. -/
lemma preimage_image_range_halfArc (p : S.ι × Bool) :
    S.q ⁻¹' (S.q '' range (S.halfArc p)) = range (S.halfArc p) := by
  refine Subset.antisymm ?_ (subset_preimage_image _ _)
  rintro y ⟨_, ⟨t, rfl⟩, hy⟩
  by_cases ht : t ∈ openUnit
  · exact image_subset_range _ _ (S.mem_half_of_q_eq (S.halfArc_mem_half ht) hy.symm)
  · exact ⟨t, (S.eq_of_q_eq_of_mem_core (S.halfArc_mem_core_of_notMem_openUnit p ht)
      hy.symm).symm⟩

/-- `q(B̄ᵢ) = {aᵢ, bᵢ, cᵢ}` (and likewise `q(D̄ᵢ)`) is closed in `𝒞X`. -/
lemma isClosed_image_range_halfArc (p : S.ι × Bool) :
    IsClosed (S.q '' range (S.halfArc p)) := by
  rw [isClosed_coarse_iff, preimage_image_range_halfArc]
  exact (isCompact_range (S.halfArc p).continuous).isClosed

/-- A point of `q(B̄ᵢ)` outside `q(F)` is `bᵢ` (and likewise for `D̄ᵢ`). -/
lemma eq_pt_of_mem_image_range {p : S.ι × Bool} {y : S.Coarse}
    (hy : y ∈ S.q '' range (S.halfArc p)) (hy' : y ∉ S.q '' S.core) : y = S.pt p := by
  obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hy
  by_cases ht : t ∈ openUnit
  · exact (S.q_eq_pt_iff).2 (S.halfArc_mem_half ht)
  · exact absurd ⟨_, S.halfArc_mem_core_of_notMem_openUnit p ht, rfl⟩ hy'

/-- `bᵢ ∈ q(B̄ᵢ)` and `dᵢ ∈ q(D̄ᵢ)`. -/
lemma pt_mem_image_range (p : S.ι × Bool) : S.pt p ∈ S.q '' range (S.halfArc p) :=
  ⟨_, ⟨midI, rfl⟩, rfl⟩

/-- `bᵢ, dᵢ ∉ q(F)`. -/
lemma pt_notMem_image_core (p : S.ι × Bool) : S.pt p ∉ S.q '' S.core := by
  rintro ⟨x, hx, h⟩; exact S.q_ne_pt hx p h

/-- Lemma 5.4′, proved before the statements of §5 so that Lemma 5.4 can use it. -/
theorem exists_extension_interior_aux {B : Type*} [MetricSpace B] {A : Set B}
    (hA : IsClosed A) (h : C(A, I)) :
    ∃ k : C(B, I), (∀ a : A, k a = h a) ∧ ∀ b ∉ A, k b ∈ openUnit := by
  obtain ⟨ψ, hψ⟩ := ContinuousMap.exists_restrict_eq hA h
  have hψA : ∀ a : A, ψ a = h a := fun a => DFunLike.congr_fun hψ a
  rcases A.eq_empty_or_nonempty with rfl | hne
  · refine ⟨ContinuousMap.const _ midI, fun a => a.2.elim, fun b _ => midI_mem_openUnit⟩
  let ρ : B → ℝ := fun b => min 1 (Metric.infDist b A)
  have hρc : Continuous ρ := continuous_const.min (Metric.continuous_infDist_pt A)
  have hρ0 : ∀ b, 0 ≤ ρ b := fun b => le_min zero_le_one Metric.infDist_nonneg
  have hρ1 : ∀ b, ρ b ≤ 1 := fun b => min_le_left _ _
  have hρA : ∀ b, b ∈ A ↔ ρ b = 0 := by
    intro b
    rw [hA.mem_iff_infDist_zero hne]
    constructor
    · intro h0; simp only [ρ, h0, min_eq_right zero_le_one]
    · intro h0
      rcases min_choice 1 (Metric.infDist b A) with h1 | h1
      · simp only [ρ, h1] at h0; norm_num at h0
      · simpa only [ρ, h1] using h0
  let F : B → ℝ := fun b => (1 - ρ b) * ψ b + ρ b / 2
  have hFc : Continuous F := by
    have : Continuous fun b => ((ψ b : I) : ℝ) := continuous_subtype_val.comp ψ.continuous
    fun_prop
  have hF0 : ∀ b, ρ b / 2 ≤ F b := fun b => by
    have := (ψ b).2.1
    show ρ b / 2 ≤ (1 - ρ b) * ψ b + ρ b / 2
    nlinarith [hρ1 b]
  have hF1 : ∀ b, F b ≤ 1 - ρ b / 2 := fun b => by
    have := (ψ b).2.2
    show (1 - ρ b) * ψ b + ρ b / 2 ≤ 1 - ρ b / 2
    nlinarith [hρ1 b, hρ0 b]
  refine ⟨⟨fun b => ⟨F b, by linarith [hF0 b, hρ0 b], by linarith [hF1 b, hρ0 b]⟩,
    hFc.subtype_mk _⟩, fun a => ?_, fun b hb => ?_⟩
  · apply Subtype.ext
    simp only [ContinuousMap.coe_mk, F, (hρA a).1 a.2, sub_zero, one_mul, zero_div, add_zero]
    rw [hψA a]
  · have hpos : 0 < ρ b := lt_of_le_of_ne (hρ0 b) (fun h => hb ((hρA b).2 h.symm))
    exact ⟨by show 0 < F b; linarith [hF0 b], by show F b < 1; linarith [hF1 b]⟩


/-- Lemma 5.2 without the standing compactness assumptions: `q⁻¹(q V)` is `V` together with the
halves meeting `V`, a union of open sets. -/
theorem isOpenMap_q_aux : IsOpenMap S.q := by
  intro V hV
  rw [isOpen_coarse_iff, isOpen_iff_mem_nhds]
  rintro z ⟨v, hv, hvz⟩
  rcases S.mem_core_or_mem_half z with hz | ⟨p, hz⟩
  · rw [S.eq_of_q_eq_of_mem_core hz hvz] at hv
    exact mem_of_superset (hV.mem_nhds hv) (subset_preimage_image _ _)
  · exact mem_of_superset ((S.isOpen_half p).mem_nhds hz)
      fun w hw => ⟨v, hv, hvz.trans (S.q_eq_q_of_mem_half hz hw)⟩

/-! ### Ingredients of the lifting lemma -/

/-- A chosen preimage under `q`. -/
def rep (y : S.Coarse) : X := (S.q_surjective y).choose

/-- `rep` is a section of `q`. -/
lemma q_rep (y : S.Coarse) : S.q (S.rep y) = y := (S.q_surjective y).choose_spec

/-- A continuous map into a closed half, built from an injective path `θ`: if `k` is continuous on
a closed `T` with values in the range of `θ`, there is `Φ : B → I` with `θ ∘ Φ = k` on `T` and
`Φ` in `(0, 1)` off `T` (Lemma 5.4′ applied to `θ⁻¹ ∘ k`). -/
lemma exists_piece {B : Type*} [MetricSpace B] {θ : C(I, X)} (hθ : Function.Injective θ)
    {T : Set B} (hT : IsClosed T) {k : B → X} (hk : ContinuousOn k T)
    (hkθ : ∀ b ∈ T, k b ∈ range θ) :
    ∃ Φ : C(B, I), (∀ b ∈ T, θ (Φ b) = k b) ∧ ∀ b ∉ T, Φ b ∈ openUnit := by
  have he : Topology.IsEmbedding θ := (θ.continuous.isClosedEmbedding hθ).isEmbedding
  choose φ hφ using hkθ
  let φ' : T → I := fun b => φ b b.2
  have hc : Continuous φ' := by
    rw [he.continuous_iff]
    have : θ ∘ φ' = T.domRestrict k := funext fun b => hφ b b.2
    rw [this]; exact hk.domRestrict
  obtain ⟨Φ, h1, h2⟩ := exists_extension_interior_aux hT ⟨φ', hc⟩
  exact ⟨Φ, fun b hb => by rw [h1 ⟨b, hb⟩]; exact hφ b hb, h2⟩

section Lift

variable {B : Type*} [MetricSpace B] {A : Set B} (f : C(A, X)) (g : C(B, S.Coarse))

open Classical in
/-- The lift `k` on `A ∪ g⁻¹(q F)`: `f` on `A`, and the unique preimage of `g` elsewhere. -/
def liftBase (b : B) : X := if hb : b ∈ A then f ⟨b, hb⟩ else S.rep (g b)

/-- The closed set `A ∪ B₀` with `B₀ = g⁻¹(q F)`, on which `k` is defined. -/
def baseSet (A : Set B) (g : C(B, S.Coarse)) : Set B := A ∪ g ⁻¹' (S.q '' S.core)

/-- `A ∪ g⁻¹(q F)` is closed. -/
lemma isClosed_baseSet (hA : IsClosed A) : IsClosed (S.baseSet A g) :=
  hA.union (S.isClosed_image_core.preimage g.continuous)

/-- `k = f` on `A`. -/
lemma liftBase_of_mem (a : A) : S.liftBase f g a = f a := by
  simp [liftBase, a.2]

variable {f g}

/-- `k` lifts `g` everywhere. -/
lemma q_liftBase (hfg : ∀ a, S.q (f a) = g a) (b : B) : S.q (S.liftBase f g b) = g b := by
  unfold liftBase
  split_ifs with hb
  · exact hfg ⟨b, hb⟩
  · exact S.q_rep _

/-- Over a point `q x` with `x ∈ F`, `k` takes the value `x`. -/
lemma liftBase_eq_of_core (hfg : ∀ a, S.q (f a) = g a) {b : B} {x : X} (hx : x ∈ S.core)
    (hb : g b = S.q x) : S.liftBase f g b = x :=
  S.eq_of_q_eq_of_mem_core hx ((S.q_liftBase hfg b).trans hb)

/-- `k` is continuous on `A ∪ g⁻¹(q F)`: by pasting `f` on `A` with `q|_F⁻¹ ∘ g`, whose
continuity follows from the openness of `q` (images of balls are open). -/
lemma continuousOn_liftBase (hA : IsClosed A) (hfg : ∀ a, S.q (f a) = g a) :
    ContinuousOn (S.liftBase f g) (S.baseSet A g) := by
  refine ContinuousOn.union_of_isClosed ?_ ?_ hA (S.isClosed_image_core.preimage g.continuous)
  · rw [continuousOn_iff_continuous_domRestrict]
    convert f.continuous using 1
    ext a; exact S.liftBase_of_mem f g a
  · rintro b₀ ⟨x, hx, hxq⟩
    rw [ContinuousWithinAt, S.liftBase_eq_of_core hfg hx hxq.symm, Metric.tendsto_nhds]
    intro ε hε
    have hU : IsOpen (S.q '' Metric.ball x ε) := S.isOpenMap_q_aux _ Metric.isOpen_ball
    have h1 : ∀ᶠ b in 𝓝 b₀, g b ∈ S.q '' Metric.ball x ε :=
      g.continuous.continuousAt (hU.mem_nhds ⟨x, Metric.mem_ball_self hε, hxq⟩)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with b hb hbT
    obtain ⟨z, hz, hzq⟩ := hb
    obtain ⟨y, hy, hyq⟩ := hbT
    rw [S.liftBase_eq_of_core hfg hy hyq.symm]
    rw [← S.eq_of_q_eq_of_mem_core hy (hzq.trans hyq.symm)]
    exact hz

open Classical in
/-- The lift: on `g⁻¹{bᵢ}` (resp. `g⁻¹{dᵢ}`) it is `θᵢ ∘ Φᵢ` for the half-arc coordinate `Φᵢ`,
elsewhere it is `k`. -/
def liftFun (Φ : S.ι × Bool → C(B, I)) (k : B → X) (g : C(B, S.Coarse)) (b : B) : X :=
  if hb : ∃ p, g b = S.pt p then S.halfArc hb.choose (Φ hb.choose b) else k b

/-- Over `bᵢ` (resp. `dᵢ`), the lift is the half-arc coordinate map. -/
lemma liftFun_of_eq_pt {Φ : S.ι × Bool → C(B, I)} {k : B → X} {b : B} {p : S.ι × Bool}
    (hb : g b = S.pt p) : S.liftFun Φ k g b = S.halfArc p (Φ p b) := by
  have hex : ∃ p, g b = S.pt p := ⟨p, hb⟩
  have hc : hex.choose = p := S.pt_injective (hex.choose_spec.symm.trans hb)
  simp only [liftFun, hex, dite_eq_left, hc]

/-- Over `q(F)`, the lift is `k`. -/
lemma liftFun_of_mem_core {Φ : S.ι × Bool → C(B, I)} {k : B → X} {b : B}
    (hb : g b ∈ S.q '' S.core) : S.liftFun Φ k g b = k b := by
  have hex : ¬ ∃ p, g b = S.pt p := by
    rintro ⟨p, hp⟩; exact S.pt_notMem_image_core p (hp ▸ hb)
  simp only [liftFun, hex, dite_eq_right, not_false_eq_true]

end Lift

/-- **Remark 5.1.** If `W` is countable then `𝒞X` is countable. The paper's setting (a compact
metric space) is separable; separability is all the proof uses (it makes the family of disjoint
open arcs countable). -/
theorem countable_coarse [TopologicalSpace.SeparableSpace X] (hW : S.W.Countable) :
    Countable S.Coarse := by
  have hι : (univ : Set S.ι).Countable :=
    PairwiseDisjoint.countable_of_isOpen (s := S.arc) (fun i _ j _ hij => S.disjoint hij)
      (fun i _ => S.isOpen_arc i) (fun i _ => ⟨_, midI, midI_mem_openUnit, rfl⟩)
  have : Countable S.ι := countable_univ_iff.1 hι
  have hsub : (univ : Set S.Coarse) ⊆
      (S.q '' S.W ∪ range (fun i => S.q (S.h i midI))) ∪ range S.pt := by
    intro y _
    rcases S.exists_core_or_eq_pt y with ⟨x, hx, rfl⟩ | ⟨p, rfl⟩
    · by_cases hxW : x ∈ S.W
      · exact Or.inl (Or.inl ⟨x, hxW, rfl⟩)
      · have : x ∈ ⋃ i, S.h i '' openUnit := S.iUnion_eq ▸ hxW
        obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.1 this
        rcases lt_trichotomy (u : ℝ) (1 / 2) with h | h | h
        · have hm : S.h i u ∈ S.firstHalf i := mem_image_of_mem _ ⟨hu.1, h⟩
          rw [firstHalf_eq_half] at hm
          exact absurd hm (hx _)
        · exact Or.inl (Or.inr ⟨i, by rw [show u = midI from Subtype.ext h]⟩)
        · have hm : S.h i u ∈ S.secondHalf i := mem_image_of_mem _ ⟨h, hu.2⟩
          rw [secondHalf_eq_half] at hm
          exact absurd hm (hx _)
    · exact Or.inr ⟨p, rfl⟩
  exact countable_univ_iff.1
    ((((hW.image _).union (countable_range _)).union (countable_range _)).mono hsub)

/-- For finitely many arcs and finite `W` the coarsification is finite (the finite-graph case of
Theorem 1.1). -/
theorem finite_coarse [Finite S.ι] (hW : S.W.Finite) : Finite S.Coarse := by
  have hsub : (univ : Set S.Coarse) ⊆
      (S.q '' S.W ∪ range (fun i => S.q (S.h i midI))) ∪ range S.pt := by
    intro y _
    rcases S.exists_core_or_eq_pt y with ⟨x, hx, rfl⟩ | ⟨p, rfl⟩
    · by_cases hxW : x ∈ S.W
      · exact Or.inl (Or.inl ⟨x, hxW, rfl⟩)
      · have : x ∈ ⋃ i, S.h i '' openUnit := S.iUnion_eq ▸ hxW
        obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.1 this
        rcases lt_trichotomy (u : ℝ) (1 / 2) with h | h | h
        · have hm : S.h i u ∈ S.firstHalf i := mem_image_of_mem _ ⟨hu.1, h⟩
          rw [firstHalf_eq_half] at hm
          exact absurd hm (hx _)
        · exact Or.inl (Or.inr ⟨i, by rw [show u = midI from Subtype.ext h]⟩)
        · have hm : S.h i u ∈ S.secondHalf i := mem_image_of_mem _ ⟨h, hu.2⟩
          rw [secondHalf_eq_half] at hm
          exact absurd hm (hx _)
    · exact Or.inr ⟨p, rfl⟩
  exact Set.finite_univ_iff.1
    ((((hW.image _).union (finite_range _)).union (finite_range _)).subset hsub)

/-- **Lemma 5.2.** The coarsification map is open. -/
theorem isOpenMap_q : IsOpenMap S.q := S.isOpenMap_q_aux

/-- **Lemma 5.4** (for metrizable spaces, which are perfectly normal). If `A ⊆ B` is closed and
`h : A → {0, 1}` is continuous, there is `k : B → [0, 1]` extending `h` with `k⁻¹{0, 1} = A`. -/
theorem exists_extension_preimage_eq {B : Type*} [MetricSpace B] {A : Set B} (hA : IsClosed A)
    (h : C(A, I)) (h01 : ∀ a, h a = 0 ∨ h a = 1) :
    ∃ k : C(B, I), (∀ a : A, k a = h a) ∧ {b | k b = 0 ∨ k b = 1} = A := by
  obtain ⟨k, hk, hk'⟩ := exists_extension_interior_aux hA h
  refine ⟨k, hk, Set.ext fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · by_contra hbA
    obtain ⟨h0, h1⟩ := hk' b hbA
    rcases hb with hb | hb <;> simp [hb] at h0 h1
  · show k b = 0 ∨ k b = 1
    rw [hk ⟨b, hb⟩]; exact h01 _

/-- **Lemma 5.4′** (strengthened Lemma 5.4, needed for the repaired proof of Lemma 5.5; see
`notes/checks/C.md`). Every continuous `h : A → [0, 1]` on a closed `A ⊆ B` extends to
`k : B → [0, 1]` taking values in the open interval `(0, 1)` off `A`. -/
theorem exists_extension_interior {B : Type*} [MetricSpace B] {A : Set B} (hA : IsClosed A)
    (h : C(A, I)) : ∃ k : C(B, I), (∀ a : A, k a = h a) ∧ ∀ b ∉ A, k b ∈ openUnit :=
  exists_extension_interior_aux hA h

/-- **Lemma 5.5 (lifting).** Let `B` be a metrizable space and `A ⊆ B` closed. If `f : A → X` and
`g : B → 𝒞X` satisfy `q ∘ f = g|_A`, then `g` has a lift `g̃ : B → X` extending `f` with
`q ∘ g̃ = g`.

Differences from the paper's statement: the paper also assumes `B` locally path-connected, which
its proof never uses (`notes/checks/C.md`), so it is dropped; and the arcs are assumed null
(`hnull`, diameters → 0), which for an arc system in a compact locally path-connected space is
Lemma 4.3 (`tendsto_diam_closedArc`, supplied in `Peano.Main`). Keeping it as a hypothesis makes
§5 independent of the proofs of §4. -/
theorem exists_lift
    (hnull : Tendsto (fun i => Metric.diam (S.closedArc i)) cofinite (𝓝 0))
    {B : Type*} [MetricSpace B] {A : Set B}
    (hA : IsClosed A) (f : C(A, X)) (g : C(B, S.Coarse)) (hfg : ∀ a, S.q (f a) = g a) :
    ∃ G : C(B, X), (∀ a : A, G a = f a) ∧ ∀ b, S.q (G b) = g b := by
  classical
  -- the lift `k` on the closed set `K = A ∪ g⁻¹(q F)`
  set k := S.liftBase f g with hk_def
  set K := S.baseSet A g with hK_def
  have hK : IsClosed K := S.isClosed_baseSet g hA
  have hkc : ContinuousOn k K := S.continuousOn_liftBase hA hfg
  have hkq : ∀ b, S.q (k b) = g b := S.q_liftBase hfg
  -- the closed sets `E p = g⁻¹(q B̄ᵢ)` (resp. `g⁻¹(q D̄ᵢ)`) and the half-arc coordinates `Φ p`
  let E : S.ι × Bool → Set B := fun p => g ⁻¹' (S.q '' range (S.halfArc p))
  have hE : ∀ p, IsClosed (E p) := fun p =>
    (S.isClosed_image_range_halfArc p).preimage g.continuous
  have hpiece : ∀ p, ∃ Φ : C(B, I), (∀ b ∈ E p ∩ K, S.halfArc p (Φ b) = k b) ∧
      ∀ b ∉ E p ∩ K, Φ b ∈ openUnit := fun p =>
    exists_piece (S.halfArc_injective p) ((hE p).inter hK) (hkc.mono inter_subset_right)
      fun b hb => by
        have : k b ∈ S.q ⁻¹' (S.q '' range (S.halfArc p)) := by
          rw [mem_preimage, hkq]; exact hb.1
        rwa [S.preimage_image_range_halfArc] at this
  choose Φ hΦ1 hΦ2 using hpiece
  let H : S.ι × Bool → B → X := fun p b => S.halfArc p (Φ p b)
  have hHc : ∀ p, Continuous (H p) := fun p => (S.halfArc p).continuous.comp (Φ p).continuous
  let G : B → X := S.liftFun Φ k g
  -- `G = k` on `K`
  have hGK : ∀ b ∈ K, G b = k b := by
    intro b hb
    rcases S.exists_core_or_eq_pt (g b) with ⟨x, hx, hxq⟩ | ⟨p, hp⟩
    · exact S.liftFun_of_mem_core ⟨x, hx, hxq⟩
    · rw [show G b = H p b from S.liftFun_of_eq_pt hp]
      exact hΦ1 p b ⟨show g b ∈ _ from hp ▸ S.pt_mem_image_range p, hb⟩
  -- `G = H p` on `E p`
  have hGE : ∀ p, ∀ b ∈ E p, G b = H p b := by
    intro p b hb
    by_cases hc : g b ∈ S.q '' S.core
    · have hbK : b ∈ K := Or.inr hc
      rw [hGK b hbK]; exact (hΦ1 p b ⟨hb, hbK⟩).symm
    · exact S.liftFun_of_eq_pt (S.eq_pt_of_mem_image_range hb hc)
  have hGq : ∀ b, S.q (G b) = g b := by
    intro b
    by_cases hbK : b ∈ K
    · rw [hGK b hbK]; exact hkq b
    · rcases S.exists_core_or_eq_pt (g b) with ⟨x, hx, hxq⟩ | ⟨p, hp⟩
      · exact absurd (Or.inr ⟨x, hx, hxq⟩) hbK
      · rw [show G b = H p b from S.liftFun_of_eq_pt hp, hp]
        exact (S.q_eq_pt_iff).2 (S.halfArc_mem_half (hΦ2 p b fun h => hbK h.2))
  have hGc : Continuous G := by
    refine continuous_iff_continuousAt.2 fun s => ?_
    rcases S.exists_core_or_eq_pt (g s) with ⟨x, hx, hxq⟩ | ⟨p, hp⟩
    · -- `g s ∈ q F`: the null hypothesis controls the arcs near `x = G s`
      have hGs : G s = x := by
        rw [hGK s (Or.inr ⟨x, hx, hxq⟩)]; exact S.liftBase_eq_of_core hfg hx hxq.symm
      rw [ContinuousAt, hGs, Metric.tendsto_nhds]
      intro ε hε
      have hfin : {i | ¬ Metric.diam (S.closedArc i) < ε / 2}.Finite :=
        Filter.eventually_cofinite.1 (hnull (Iio_mem_nhds (half_pos hε)))
      have h1 : ∀ᶠ b in 𝓝 s, g b ∈ S.q '' Metric.ball x (ε / 2) :=
        g.continuous.continuousAt ((S.isOpenMap_q_aux _ Metric.isOpen_ball).mem_nhds
          ⟨x, Metric.mem_ball_self (half_pos hε), hxq⟩)
      have h2 : ∀ᶠ b in 𝓝 s, ∀ i ∈ {i | ¬ Metric.diam (S.closedArc i) < ε / 2}, ∀ β : Bool,
          b ∈ E (i, β) → dist (H (i, β) b) x < ε := by
        refine hfin.eventually_all.2 fun i _ => Filter.eventually_all.2 fun β => ?_
        by_cases hs : s ∈ E (i, β)
        · have hHs : H (i, β) s = x := (hGE _ s hs).symm.trans hGs
          have := (hHc (i, β)).continuousAt.eventually (Metric.ball_mem_nhds (H (i, β) s) hε)
          rw [hHs] at this
          exact this.mono fun b hb _ => hb
        · exact Filter.eventually_of_mem ((hE (i, β)).isOpen_compl.mem_nhds hs)
            fun b hb hb' => absurd hb' hb
      filter_upwards [h1, h2] with b hb hJ
      obtain ⟨z, hz, hzq⟩ := hb
      rw [Metric.mem_ball] at hz
      rcases S.mem_core_or_mem_half z with hzc | ⟨p, hzp⟩
      · rw [show G b = z from (S.liftFun_of_mem_core ⟨z, hzc, hzq⟩).trans
          (S.liftBase_eq_of_core hfg hzc hzq.symm)]
        linarith
      · have hbp : g b = S.pt p := hzq ▸ (S.q_eq_pt_iff).2 hzp
        have hbE : b ∈ E p := show g b ∈ _ from hbp ▸ S.pt_mem_image_range p
        rw [hGE p b hbE]
        by_cases hd : Metric.diam (S.closedArc p.1) < ε / 2
        · have hbd : Bornology.IsBounded (S.closedArc p.1) :=
            (isCompact_range (S.h p.1).continuous).isBounded
          have := Metric.dist_le_diam_of_mem hbd (S.range_halfArc_subset p ⟨Φ p b, rfl⟩)
            (S.half_subset_closedArc p hzp)
          calc dist (H p b) x ≤ dist (H p b) z + dist z x := dist_triangle _ _ _
            _ < ε / 2 + ε / 2 := by
                have : dist (H p b) z ≤ Metric.diam (S.closedArc p.1) := this
                linarith
            _ = ε := add_halves ε
        · exact hJ p.1 hd p.2 hbE
    · -- `g s = bᵢ` or `dᵢ`: near `s`, `G = H p`
      have hev : H p =ᶠ[𝓝 s] G := by
        have hO : IsOpen (g ⁻¹' {S.pt p}) := (S.isOpen_singleton_pt p).preimage g.continuous
        filter_upwards [hO.mem_nhds (show s ∈ g ⁻¹' {S.pt p} from hp)] with b hb
        exact (S.liftFun_of_eq_pt hb).symm
      exact (hHc p).continuousAt.congr hev
  refine ⟨⟨G, hGc⟩, fun a => ?_, hGq⟩
  show G a = f a
  rw [hGK a (Or.inl a.2)]
  exact S.liftBase_of_mem f g a

end ArcSystem

end Peano
