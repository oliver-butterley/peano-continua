module

public import Peano.Thm1_1
public import Peano.Thm1_2
public import Peano.Models
public import Peano.PlaneGeometry

/-!
# Sanity checks: the definitions and main statements are not vacuous

Checks that a definitional slip cannot make the main theorems of the formalisation of
Brazas–Pavešić, *Countable models of one-dimensional Peano continua* (arXiv:2610.35875), vacuous
or trivial.

1. **Weak homotopy equivalences are not trivial.** The constant map from the circle
   `AddCircle 1 = ℝ/ℤ` to a point is not a weak homotopy equivalence
   (`not_isWeakHomotopyEquivalence_addCircle_const`): the winding number detects a loop that a
   weak homotopy equivalence to a point would have to kill.
2. **Theorem 1.1 has non-trivial instances.** There is a one-dimensional Peano continuum whose wild
   set is non-empty and countable, and it has a countable weak model
   (`exists_peano_wildSet_nonempty_countable`, `exists_countable_weq_of_wildSet_nonempty`). The
   example is the planar model `A_K` of `K = Unit` (a segment with one earring attached).
3. **The classification of the paper's Theorem 1.2 fails without non-empty wild sets**
   (`notes/checks/D.md`). The one-point space `Unit` and the planar circle `earringCircle 0 ⊆ ℝ²`
   are one-dimensional Peano continua with empty wild sets and countable (indeed finite) weak
   models, but they are not homotopy equivalent, and neither is homotopy equivalent to a continuum
   with non-empty wild set (`thm1_2_counterexample`), in particular to any of the paper's models
   `A_λ`. So the paper's canonical map `[λ] ↦ Ho(A_λ)` is not a bijection onto the claimed set: it
   misses these homotopy types (the decisive failure). In the other direction, `X ↦ w(X)` does not
   separate them. The cited Theorem 6.6 is false without "non-empty", and the corrected Theorem 1.2
   (`nonempty_homotopyEquiv_iff`) fails without its non-emptiness hypotheses
   (`not_forall_nonempty_homotopyEquiv_iff_wildSet`). (Informal aside, resting on the cited
   results and Mazurkiewicz–Sierpiński: both sets have cardinality `ℵ₁`, so *some* bijection
   exists; it is the canonical one that fails.) Since the point has dimension `0`, the circle alone
   (dimension exactly `1`) already shows non-surjectivity, which rules out reading "one-dimensional"
   as "dimension exactly one" to rescue the statement; `thm1_2_counterexample_dim_one` adds that
   the circle and the planar arc `[0, 1] × {0}` (both of dimension exactly `1`, empty wild sets,
   finite models) are not homotopy equivalent.
4. **The earring** satisfies the hypotheses of Theorem 1.1 and its wild set is exactly the base
   point (`earring_peano`, `wildSet_earring`).
5. **Covering dimension is not trivial**: a connected `T₁` space with two points does not satisfy
   `CoveringDimLE 0` (`not_coveringDimLE_zero`), e.g. the unit interval
   (`not_coveringDimLE_zero_unitInterval`); the circle `C₀` and the planar arc have dimension
   exactly `1` (`coveringDim_earringCircle_zero`, `coveringDim_planarArc`: each is the conjunction
   `CoveringDimLE 1 ∧ ¬ CoveringDimLE 0`).

Not formalised: an instance of the "only if" direction of Theorem 1.1 (a one-dimensional Peano
continuum with uncountable wild set, e.g. the model over a Cantor set): the planar models of
`Peano.Models` are built for countable `K` only.

## Design

The circle used in 3. is the planar circle `earringCircle 0` (centre `(1, 0)`, radius `1`) as a
subtype of `ℝ × ℝ`, so that the textbook axiom `coveringDimLE_one_of_interior_eq_empty` gives its
dimension; its essential loop is the earring loop `ℓ₀`, which stays in this circle. Non-wildness
of its points (and of the non-base points of the earring) is proved with
`homotopic_refl_of_radial_retraction` (radial projection on a ball avoiding the centre). The
geometry of the earring circles (parametrisation, compactness, empty interior, local
joinability) is shared with `Peano.Models` and lives in `Peano.PlaneGeometry`. The fact that
homotopy equivalences preserve non-emptiness of the wild set is proved directly from Lemma 2.5
(`image_wildSet_subset`) and the π₁-bijectivity of homotopy equivalences, without the cited
classification results.

## Axioms

1., 5. (except the upper bounds on dimension), the non-wildness of the circle, the arc and the
non-base points of the earring, the finite models of the point, the circle (its coarsification as
a finite graph, `circleArcSystem`) and the arc, and the non-homotopy-equivalences use no axioms
beyond Lean's. One-dimensionality of the circle, the arc and the earring uses
`coveringDimLE_one_of_interior_eq_empty`; so this is the only axiom of `thm1_2_counterexample` and
`thm1_2_counterexample_dim_one`. The countable weak models of 2. and of the earring come from
Theorem 1.1 ("if" direction, `exists_countable_weq`) and carry its cited axioms.
-/

@[expose] public section

open Set Filter Topology Metric unitInterval

noncomputable section

namespace Peano.Sanity

/-! ### Generalities -/

/-- In a space with at most one point every loop is null-homotopic. -/
theorem homotopic_refl_of_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {x : X}
    (γ : Path x x) : γ.Homotopic (Path.refl x) := by
  have : γ = Path.refl x := by ext t; exact Subsingleton.elim _ _
  rw [this]

/-- A weak homotopy equivalence to a space with at most one point kills every loop. -/
theorem homotopic_refl_of_isWeakHomotopyEquivalence_subsingleton {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Subsingleton Y] {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) {x : X} (γ : Path x x) : γ.Homotopic (Path.refl x) :=
  hf.homotopic_of_map_homotopic (by
    have : γ.map f.continuous = (Path.refl x).map f.continuous := by
      ext t; exact Subsingleton.elim _ _
    rw [this])

/-- **Homotopy equivalences reflect non-emptiness of the wild set**: if `X ≃ₕ Y` and `w(Y) ≠ ∅`
then `w(X) ≠ ∅`. Proof: the homotopy inverse `Y → X` is a weak homotopy equivalence, hence
π₁-injective, so by Lemma 2.5 it maps `w(Y)` into `w(X)`. -/
theorem wildSet_nonempty_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (hY : (wildSet Y).Nonempty) : (wildSet X).Nonempty := by
  have hg := HomotopyEquiv.isWeakHomotopyEquivalence e.symm
  obtain ⟨y, hy⟩ := hY
  exact ⟨_, image_wildSet_subset (f := e.symm.toFun)
    (fun x => (hg.fundamentalGroup_map_bijective x).1) (mem_image_of_mem _ hy)⟩

/-- Homotopy equivalent spaces have empty wild sets simultaneously. -/
theorem wildSet_eq_empty_iff_of_homotopyEquiv {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    wildSet X = ∅ ↔ wildSet Y = ∅ := by
  simp only [← not_nonempty_iff_eq_empty]
  exact ⟨fun h h' => h (wildSet_nonempty_of_homotopyEquiv e h'),
    fun h h' => h (wildSet_nonempty_of_homotopyEquiv e.symm h')⟩

/-! ### 1. Weak homotopy equivalences are not trivial -/

/-- **Non-triviality of `IsWeakHomotopyEquivalence`.** The constant map `ℝ/ℤ → Unit` is not a weak
homotopy equivalence: the standard loop of `ℝ/ℤ` has winding number `1`, so it is not
null-homotopic, while a weak homotopy equivalence to a point would make it null-homotopic. -/
theorem not_isWeakHomotopyEquivalence_addCircle_const :
    ¬ IsWeakHomotopyEquivalence (ContinuousMap.const (AddCircle (1 : ℝ)) ()) := fun hf =>
  unitAddCircleLoop_not_homotopic_refl
    (homotopic_refl_of_isWeakHomotopyEquivalence_subsingleton hf _)

/-- Sanity check in the other direction: the identity of `ℝ/ℤ` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_addCircle_id :
    IsWeakHomotopyEquivalence (ContinuousMap.id (AddCircle (1 : ℝ))) :=
  HomotopyEquiv.isWeakHomotopyEquivalence (ContinuousMap.HomotopyEquiv.refl _)

/-! ### 2. Theorem 1.1 has instances with non-empty wild set -/

/-- **Non-vacuity of the hypotheses of Theorem 1.1 with `w(X) ≠ ∅`.** Some one-dimensional
Peano continuum `X : Type` has non-empty countable wild set (the model `A_K` for `K = Unit`: a
segment with one earring attached; its wild set is a single point). -/
theorem exists_peano_wildSet_nonempty_countable :
    ∃ (X : Type) (_ : MetricSpace X), CompactSpace X ∧ ConnectedSpace X ∧
      LocallyPathConnectedSpace X ∧ CoveringDimLE 1 X ∧ (wildSet X).Nonempty ∧
        (wildSet X).Countable := by
  obtain ⟨X, _, hc, hconn, hlpc, hdim, ⟨φ⟩⟩ := exists_wildSet_homeomorph Unit
  have : Countable (wildSet X) := φ.injective.countable
  exact ⟨X, inferInstance, hc, hconn, hlpc, hdim, ⟨_, (φ.symm ()).2⟩, countable_coe_iff.1 this⟩

/-- **A concrete instance of Theorem 1.1 with non-trivial content.** Some one-dimensional Peano
continuum with non-empty wild set admits a weak homotopy equivalence to a countable space. -/
theorem exists_countable_weq_of_wildSet_nonempty :
    ∃ (X : Type) (_ : MetricSpace X), CompactSpace X ∧ ConnectedSpace X ∧
      LocallyPathConnectedSpace X ∧ CoveringDimLE 1 X ∧ (wildSet X).Nonempty ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
          ∃ f : C(X, Y), IsWeakHomotopyEquivalence f := by
  obtain ⟨X, _, hc, hconn, hlpc, hdim, hne, hcount⟩ := exists_peano_wildSet_nonempty_countable
  exact ⟨X, inferInstance, hc, hconn, hlpc, hdim, hne,
    exists_countable_weq X hdim hcount⟩

/-! ### 3. The classification of the paper's Theorem 1.2 fails without non-empty wild sets

#### The planar circle -/

/-- The equation of the circle `C₀`: centre `(1, 0)`, radius `1`. -/
theorem mem_earringCircle_zero_iff {p : ℝ × ℝ} :
    p ∈ earringCircle 0 ↔ (p.1 - 1) ^ 2 + p.2 ^ 2 = 1 := by
  simp [earringCircle, earringRadius]

/-- The circle `Cₖ` is a compact space. -/
instance compactSpace_earringCircle (k : ℕ) : CompactSpace (earringCircle k) :=
  isCompact_iff_compactSpace.1 (isCompact_earringCircle k)

/-- The circle `Cₖ` is path-connected (as a space). -/
instance pathConnectedSpace_earringCircle (k : ℕ) : PathConnectedSpace (earringCircle k) := by
  have hs : Function.Surjective fun t : ℝ =>
      (⟨earringParam k t, earringParam_mem_earringCircle k t⟩ : earringCircle k) := by
    rintro ⟨p, hp⟩
    obtain ⟨t, -, ht⟩ := exists_earringParam_eq hp
    exact ⟨t, Subtype.ext ht⟩
  exact hs.pathConnectedSpace ((continuous_earringParam k).subtype_mk _)

/-- The circle `Cₖ` is locally path-connected. -/
instance locallyPathConnectedSpace_earringCircle (k : ℕ) :
    LocallyPathConnectedSpace (earringCircle k) :=
  locallyPathConnectedSpace_of_locJoin fun p _ => locJoin_earringCircle k p

/-- The circle `Cₖ` is at most one-dimensional (via the textbook axiom on planar compacta with
empty interior). -/
theorem coveringDimLE_earringCircle (k : ℕ) : CoveringDimLE 1 (earringCircle k) :=
  coveringDimLE_one_of_interior_eq_empty _ (isCompact_earringCircle k) (interior_earringCircle k)

/-- The base point `(0, 0)` of the circle `C₀`. -/
def circleBase : earringCircle 0 := ⟨(0, 0), zero_mem_earringCircle 0⟩

/-- The loop going once around the circle `C₀`, based at `(0, 0)`. -/
def circleLoop₀ : Path circleBase circleBase where
  toFun t := ⟨earringParam 0 t, earringParam_mem_earringCircle 0 t⟩
  continuous_toFun := ((continuous_earringParam 0).comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (by simp [circleBase])
  target' := Subtype.ext (by simp [circleBase])

/-- The inclusion of the circle `C₀` into the earring. -/
def circleIncl : C(earringCircle 0, earring) :=
  ⟨fun p => ⟨p, mem_iUnion.2 ⟨0, p.2⟩⟩, continuous_subtype_val.subtype_mk _⟩

/-- **The planar circle is not simply connected**: the loop around `C₀` is essential (its image in
the earring is the essential loop `ℓ₀`). -/
theorem circleLoop₀_not_homotopic_refl : ¬ circleLoop₀.Homotopic (Path.refl circleBase) :=
  not_homotopic_refl_of_map circleIncl (earringLoop_not_homotopic_refl 0)

/-- **The planar circle has empty wild set.** Every point `x` of `C₀` has the neighbourhood
`B(x, 1/2)` (sup metric), which avoids the centre `(1, 0)`; radial projection from the centre is a
retraction of this convex ball onto the circle, so every loop in it is null-homotopic
(`homotopic_refl_of_radial_retraction`). -/
theorem wildSet_earringCircle_zero : wildSet (earringCircle 0) = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  refine notMem_loopWildSet_of_forall (U := Subtype.val ⁻¹' ball (x : ℝ × ℝ) (1 / 2))
    ((isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self (by norm_num)))
    (fun γ hγ => ?_) (wildSet_subset_loopWildSet _ hx)
  have hxc := mem_earringCircle_zero_iff.1 x.2
  -- radial projection from the centre `(1, 0)` retracts the ball onto `C₀`
  refine homotopic_refl_of_radial_retraction (c := (1, 0)) (ρ := 1) one_pos (convex_ball _ _)
    (fun y hy => sq_add_sq_pos_of_dist_lt (x := (x : ℝ × ℝ)) (ρ := 1) (by simpa using hxc)
      (by simpa using hy))
    (fun y hy => mem_earringCircle_zero_iff.2 (by simpa using hy))
    (fun y _ hyM => by simpa using mem_earringCircle_zero_iff.1 hyM) γ
    fun t => hγ (mem_range_self t)

/-- Two parameters in `(0, 1)` with the same point on the circle `Cₖ` are equal. -/
theorem eq_of_earringParam_eq {k : ℕ} {t t' : ℝ} (ht : 0 < t ∧ t < 1) (ht' : 0 < t' ∧ t' < 1)
    (h : earringParam k t = earringParam k t') : t = t' := by
  obtain ⟨n, hn⟩ := earringParam_eq_earringParam h
  have h1 : (n : ℝ) < 1 := by linarith
  have h2 : (-1 : ℝ) < n := by linarith
  have h1' : n < 1 := by exact_mod_cast h1
  have h2' : -1 < n := by exact_mod_cast h2
  obtain rfl : n = 0 := by omega
  simpa using hn

/-- The loop around `C₀` maps the open interval `(0, 1)` onto the circle minus its base point. -/
theorem image_circleLoop₀_openUnit : circleLoop₀ '' openUnit = {circleBase}ᶜ := by
  ext p
  simp only [mem_image, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩ hp
    have h0 : earringParam 0 (t : ℝ) = earringParam 0 0 := by
      rw [earringParam_zero]; exact congrArg Subtype.val hp
    obtain ⟨n, hn⟩ := earringParam_eq_earringParam h0
    have h1 : (n : ℝ) < 1 := by linarith [ht.2]
    have h2 : (0 : ℝ) < n := by linarith [ht.1]
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : 0 < n := by exact_mod_cast h2
    omega
  · intro hp
    obtain ⟨t, ht, htp⟩ := exists_earringParam_eq p.2
    have hne : ∀ s, earringParam 0 s = (0, 0) → (p : ℝ × ℝ) ≠ earringParam 0 s := by
      intro s hs hps
      exact hp (Subtype.ext (by rw [hps, hs]; rfl))
    have h0 : t ≠ 0 := by rintro rfl; exact hne 0 (earringParam_zero 0) htp.symm
    have h1 : t ≠ 1 := by rintro rfl; exact hne 1 (earringParam_one 0) htp.symm
    refine ⟨⟨t, ht⟩, ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩,
      Subtype.ext htp⟩

/-- **The circle `C₀` as a finite graph**: one vertex `(0, 0)` and one arc, the loop around the
circle. -/
def circleArcSystem : ArcSystem (earringCircle 0) where
  W := {circleBase}
  isClosed_W := isClosed_singleton
  ι := Unit
  h _ := circleLoop₀.toContinuousMap
  injOn _ t ht t' ht' h := Subtype.ext (eq_of_earringParam_eq ht ht' (congrArg Subtype.val h))
  mem_W _ := ⟨circleLoop₀.source, circleLoop₀.target⟩
  disjoint i j hij := (hij (Subsingleton.elim i j)).elim
  iUnion_eq := by
    simp only [iUnion_const]
    exact image_circleLoop₀_openUnit
  isOpen_arc _ := by
    change IsOpen (circleLoop₀ '' openUnit)
    rw [image_circleLoop₀_openUnit]
    exact isOpen_compl_singleton

/-- **The circle `C₀` has a finite weak model**, its coarsification as a finite graph
(`ArcSystem.finite_weq_q_of_finite`), without any cited axiom. -/
theorem earringCircle_zero_finite_weq :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Finite Y ∧
      ∃ f : C(earringCircle 0, Y), IsWeakHomotopyEquivalence f := by
  have : Finite circleArcSystem.ι := inferInstanceAs (Finite Unit)
  obtain ⟨h1, h2⟩ := circleArcSystem.finite_weq_q_of_finite (finite_singleton circleBase)
  exact ⟨_, inferInstance, h1, _, h2⟩

/-! #### The one-point space -/

/-- The one-point space is at most one-dimensional (indeed zero-dimensional): refine any finite
open cover by the single set `univ`. -/
theorem coveringDimLE_unit : CoveringDimLE 1 Unit := by
  intro ι _ U _ hU
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hU ▸ mem_univ ())
  refine ⟨Unit, inferInstance, fun _ => univ, fun _ => isOpen_univ, iUnion_const univ,
    fun _ => ⟨i, fun u _ => by rwa [Subsingleton.elim u ()]⟩, fun x => ?_⟩
  simp [ncard_univ]

/-- The one-point space has empty wild set: all its loops are null-homotopic. -/
theorem wildSet_unit : wildSet Unit = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨_, _, hf⟩ => hf 0 (homotopic_refl_of_subsingleton _)

/-- **The circle and the point are not homotopy equivalent**: a homotopy equivalence
`C₀ → Unit` would be a weak homotopy equivalence, hence π₁-injective, and would make the essential
loop around `C₀` null-homotopic. -/
theorem isEmpty_homotopyEquiv_earringCircle_unit :
    IsEmpty (ContinuousMap.HomotopyEquiv (earringCircle 0) Unit) :=
  ⟨fun e => circleLoop₀_not_homotopic_refl
    (homotopic_refl_of_isWeakHomotopyEquivalence_subsingleton
      (HomotopyEquiv.isWeakHomotopyEquivalence e) _)⟩

/-! #### The counterexample -/

/-- The one-point space is a one-dimensional Peano continuum with empty wild set and a countable
weak model (itself, by the identity). -/
theorem unit_peano :
    CompactSpace Unit ∧ ConnectedSpace Unit ∧ LocallyPathConnectedSpace Unit ∧
      CoveringDimLE 1 Unit ∧ wildSet Unit = ∅ ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
          ∃ f : C(Unit, Y), IsWeakHomotopyEquivalence f :=
  ⟨inferInstance, inferInstance, inferInstance, coveringDimLE_unit, wildSet_unit, Unit,
    inferInstance, inferInstance, ContinuousMap.id Unit,
    HomotopyEquiv.isWeakHomotopyEquivalence (ContinuousMap.HomotopyEquiv.refl Unit)⟩

/-- The planar circle `C₀` is a one-dimensional Peano continuum with empty wild set, and it admits
a weak homotopy equivalence to a countable (indeed finite) space, its coarsification
(`earringCircle_zero_finite_weq`; no cited axiom). -/
theorem earringCircle_zero_peano :
    CompactSpace (earringCircle 0) ∧ ConnectedSpace (earringCircle 0) ∧
      LocallyPathConnectedSpace (earringCircle 0) ∧ CoveringDimLE 1 (earringCircle 0) ∧
        wildSet (earringCircle 0) = ∅ ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
          ∃ f : C(earringCircle 0, Y), IsWeakHomotopyEquivalence f :=
  ⟨inferInstance, inferInstance, inferInstance, coveringDimLE_earringCircle 0,
    wildSet_earringCircle_zero,
    let ⟨Y, _, _, f, hf⟩ := earringCircle_zero_finite_weq
    ⟨Y, inferInstance, Finite.to_countable, f, hf⟩⟩

/-- **Counterexample to Theorem 1.2 as stated in the paper** (`notes/checks/D.md`). The point and
the planar circle `C₀` are one-dimensional Peano continua which admit weak homotopy equivalences to
countable spaces; they are not homotopy equivalent to each other, and neither is homotopy
equivalent to any space with non-empty wild set (in particular to any of the paper's models
`A_λ`, or to any `A_K` of `exists_wildSet_homeomorph`). So the paper's canonical correspondence
between homotopy types of one-dimensional Peano continua with a countable weak model and compact
countable ordinals is not a bijection: `[λ] ↦ Ho(A_λ)` reaches neither homotopy type (and `w` does
not separate them). (Informally, by the cited results, both sets have cardinality `ℵ₁`, so some
bijection exists; it is the canonical one that fails.) Axioms: only
`coveringDimLE_one_of_interior_eq_empty`. -/
theorem thm1_2_counterexample :
    (CompactSpace Unit ∧ ConnectedSpace Unit ∧ LocallyPathConnectedSpace Unit ∧
      CoveringDimLE 1 Unit ∧ wildSet Unit = ∅ ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
          ∃ f : C(Unit, Y), IsWeakHomotopyEquivalence f) ∧
    (CompactSpace (earringCircle 0) ∧ ConnectedSpace (earringCircle 0) ∧
      LocallyPathConnectedSpace (earringCircle 0) ∧ CoveringDimLE 1 (earringCircle 0) ∧
        wildSet (earringCircle 0) = ∅ ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
          ∃ f : C(earringCircle 0, Y), IsWeakHomotopyEquivalence f) ∧
    IsEmpty (ContinuousMap.HomotopyEquiv Unit (earringCircle 0)) ∧
    ∀ (X : Type) [TopologicalSpace X], (wildSet X).Nonempty →
      IsEmpty (ContinuousMap.HomotopyEquiv X Unit) ∧
        IsEmpty (ContinuousMap.HomotopyEquiv X (earringCircle 0)) := by
  refine ⟨unit_peano, earringCircle_zero_peano,
    ⟨fun e => isEmpty_homotopyEquiv_earringCircle_unit.false e.symm⟩, fun X _ hX => ⟨?_, ?_⟩⟩
  · refine ⟨fun e => ?_⟩
    have := wildSet_nonempty_of_homotopyEquiv e.symm hX
    rw [wildSet_unit] at this
    exact not_nonempty_empty this
  · refine ⟨fun e => ?_⟩
    have := wildSet_nonempty_of_homotopyEquiv e.symm hX
    rw [wildSet_earringCircle_zero] at this
    exact not_nonempty_empty this

/-- **The non-emptiness hypotheses of the corrected Theorem 1.2 cannot be dropped.** Without
`w(X) ≠ ∅ ≠ w(Y)`, the statement of `nonempty_homotopyEquiv_iff` ("one-dimensional Peano continua
with countable wild sets are homotopy equivalent iff their wild sets are homeomorphic") is false:
the point and the circle `C₀` have homeomorphic (empty) wild sets but are not homotopy
equivalent. -/
theorem not_forall_nonempty_homotopyEquiv_iff_wildSet :
    ¬ ∀ (X Y : Type) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
      [LocallyPathConnectedSpace X] [MetricSpace Y] [CompactSpace Y] [ConnectedSpace Y]
      [LocallyPathConnectedSpace Y], CoveringDimLE 1 X → CoveringDimLE 1 Y →
        (wildSet X).Countable → (wildSet Y).Countable →
        (Nonempty (ContinuousMap.HomotopyEquiv X Y) ↔ Nonempty (wildSet X ≃ₜ wildSet Y)) := by
  intro h
  have hiff := h Unit (earringCircle 0) coveringDimLE_unit (coveringDimLE_earringCircle 0)
    (by rw [wildSet_unit]; exact countable_empty)
    (by rw [wildSet_earringCircle_zero]; exact countable_empty)
  have : IsEmpty (wildSet Unit) := by rw [wildSet_unit]; infer_instance
  have : IsEmpty (wildSet (earringCircle 0)) := by rw [wildSet_earringCircle_zero]; infer_instance
  obtain ⟨e⟩ := hiff.2 ⟨Homeomorph.empty⟩
  exact isEmpty_homotopyEquiv_earringCircle_unit.false e.symm

/-! ### 4. The earring -/

/-- The earring is locally path-connected. -/
instance locallyPathConnectedSpace_earring : LocallyPathConnectedSpace earring :=
  locallyPathConnectedSpace_of_locJoin fun p _ => locJoin_earring p

/-- The earring is connected: every circle is connected and contains the base point. -/
instance connectedSpace_earring : ConnectedSpace earring := by
  refine isConnected_iff_connectedSpace.1 ?_
  refine ⟨⟨(0, 0), mem_iUnion.2 ⟨0, zero_mem_earringCircle 0⟩⟩,
    isPreconnected_iUnion ⟨(0, 0), mem_iInter.2 zero_mem_earringCircle⟩ fun k => ?_⟩
  rw [← range_earringParam]
  exact isPreconnected_range (continuous_earringParam k)

/-- The earring has empty interior in `ℝ²` (Baire: it is a countable union of closed nowhere dense
circles). -/
theorem interior_earring : interior earring = ∅ := by
  have hM : IsMeagre earring := isMeagre_iUnion fun k => IsNowhereDense.isMeagre
    ((isClosed_earringCircle k).isNowhereDense_iff.2 (interior_earringCircle k))
  by_contra h
  exact not_isMeagre_of_isOpen isOpen_interior (nonempty_iff_ne_empty.2 h)
    (hM.mono interior_subset)

/-- The earring is at most one-dimensional (via the textbook axiom on planar compacta with empty
interior). -/
theorem coveringDimLE_earring : CoveringDimLE 1 earring :=
  coveringDimLE_one_of_interior_eq_empty _ isCompact_earring interior_earring

/-- **The wild set of the earring is its base point.** The base point is wild
(`earringBase_mem_wildSet`). A point `x ≠ b₀` lies on a single circle `Cₖ` near `x`
(`isOpen_preimage_earringCircle_diff`); on a small ball about `x` avoiding the centre of `Cₖ`,
radial projection onto `Cₖ` is a retraction, so small loops at `x` are null-homotopic
(`homotopic_refl_of_radial_retraction`). -/
theorem wildSet_earring : wildSet earring = {earringBase} := by
  refine subset_antisymm (fun x hx => ?_) (singleton_subset_iff.2 earringBase_mem_wildSet)
  by_contra hxb
  obtain ⟨k, hxk⟩ := mem_iUnion.1 x.2
  set ρ := earringRadius k with hρ_def
  have hρ : 0 < ρ := earringRadius_pos k
  obtain ⟨δ₀, hδ₀, hball⟩ :=
    Metric.isOpen_iff.1 (isOpen_preimage_earringCircle_diff k) x ⟨hxk, hxb⟩
  set δ := min δ₀ (ρ / 2) with hδ_def
  have hδ : 0 < δ := lt_min hδ₀ (half_pos hρ)
  set W := ball (x : ℝ × ℝ) δ with hW_def
  have hWM : ∀ y ∈ W, y ∈ earring → y ∈ earringCircle k := fun y hy hyM =>
    (hball (show (⟨y, hyM⟩ : earring) ∈ ball x δ₀ from
      mem_ball.2 ((mem_ball.1 hy).trans_le (min_le_left _ _)))).1
  have hxc : (((x : ℝ × ℝ).1 - ρ) ^ 2 + (x : ℝ × ℝ).2 ^ 2 = ρ ^ 2) := hxk
  refine notMem_loopWildSet_of_forall (U := Subtype.val ⁻¹' W)
    ((isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hδ))
    (fun γ hγ => ?_) (wildSet_subset_loopWildSet _ hx)
  -- radial projection from the centre `(ρ, 0)` retracts `W` onto `Cₖ`
  refine homotopic_refl_of_radial_retraction (c := (ρ, 0)) hρ (convex_ball _ δ)
    (fun y hy => sq_add_sq_pos_of_dist_lt (by simpa using hxc)
      ((mem_ball.1 hy).trans_le (min_le_right _ _)))
    (fun y hy => mem_iUnion.2 ⟨k, (by simpa using hy : (y.1 - ρ) ^ 2 + y.2 ^ 2 = ρ ^ 2)⟩)
    (fun y hy hyM => by
      have h : (y.1 - ρ) ^ 2 + y.2 ^ 2 = ρ ^ 2 := hWM y hy hyM
      simpa using h) γ
    fun t => hγ (mem_range_self t)

/-- **The earring satisfies the hypotheses of Theorem 1.1**, and its wild set is the single point
`b₀`; hence (Theorem 1.1) it admits a weak homotopy equivalence to a countable space. -/
theorem earring_peano :
    CompactSpace earring ∧ ConnectedSpace earring ∧ LocallyPathConnectedSpace earring ∧
      CoveringDimLE 1 earring ∧ wildSet earring = {earringBase} ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Countable Y ∧
          ∃ f : C(earring, Y), IsWeakHomotopyEquivalence f :=
  ⟨inferInstance, inferInstance, inferInstance, coveringDimLE_earring, wildSet_earring,
    exists_countable_weq _ coveringDimLE_earring
      (by rw [wildSet_earring]; exact countable_singleton _)⟩

/-! ### 5. Covering dimension is not trivial; two continua of dimension exactly one -/

/-- **`CoveringDimLE 0` fails for connected spaces with two points.** In a connected `T₁` space
with points `a ≠ b`, the open cover `{X ∖ {a}, X ∖ {b}}` has no finite open refinement of order
`1`: such a refinement consists of pairwise disjoint open sets covering `X`, so each of them is
clopen, and the one containing `a` is all of `X`; but it lies in `X ∖ {a}` or in `X ∖ {b}`. -/
theorem not_coveringDimLE_zero {X : Type*} [TopologicalSpace X] [T1Space X] [ConnectedSpace X]
    {a b : X} (hab : a ≠ b) : ¬ CoveringDimLE 0 X := by
  intro h
  obtain ⟨κ, _, V, hVo, hVU, hVsub, hord⟩ := h Bool (fun i => if i then {a}ᶜ else {b}ᶜ)
    (fun i => by cases i <;> exact isOpen_compl_singleton) (by
      refine eq_univ_of_forall fun x => mem_iUnion.2 ?_
      by_cases hx : x = a
      · exact ⟨false, by simpa [hx] using hab⟩
      · exact ⟨true, by simpa using hx⟩)
  have hdisj : ∀ x j j', x ∈ V j → x ∈ V j' → j = j' := fun x j j' hj hj' =>
    ((ncard_le_one (toFinite _)).1 (hord x)) j hj j' hj'
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hVU ▸ mem_univ a)
  have hcompl : (V j)ᶜ = ⋃ j' : {j' // j' ≠ j}, V j' := by
    ext x
    simp only [mem_compl_iff, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨j', hj'⟩ := mem_iUnion.1 (hVU ▸ mem_univ x)
      exact ⟨⟨j', fun h => hx (h ▸ hj')⟩, hj'⟩
    · rintro ⟨⟨j', hne⟩, hj'⟩ hx
      exact hne (hdisj x j' j hj' hx)
  have hclopen : IsClopen (V j) :=
    ⟨by rw [← isOpen_compl_iff, hcompl]; exact isOpen_iUnion fun j' => hVo j', hVo j⟩
  have huniv := hclopen.eq_univ ⟨a, hj⟩
  obtain ⟨i, hi⟩ := hVsub j
  cases i
  · exact (hi (huniv ▸ mem_univ b) : b ∈ ({b}ᶜ : Set X)) rfl
  · exact (hi hj : a ∈ ({a}ᶜ : Set X)) rfl

/-- **The unit interval is not zero-dimensional** (in the sense of `CoveringDimLE`), so
`CoveringDimLE` is not a trivial notion. -/
theorem not_coveringDimLE_zero_unitInterval : ¬ CoveringDimLE 0 I :=
  not_coveringDimLE_zero (zero_ne_one : (0 : I) ≠ 1)

/-- The planar circle `C₀` has covering dimension exactly `1`. -/
theorem coveringDim_earringCircle_zero :
    CoveringDimLE 1 (earringCircle 0) ∧ ¬ CoveringDimLE 0 (earringCircle 0) := by
  refine ⟨coveringDimLE_earringCircle 0, not_coveringDimLE_zero (a := circleBase)
    (b := ⟨(2, 0), mem_earringCircle_zero_iff.2 (by norm_num)⟩) fun h => ?_⟩
  have := congrArg (fun p : earringCircle 0 => (p : ℝ × ℝ).1) h
  norm_num [circleBase] at this

/-- The planar arc `[0, 1] × {0} ⊆ ℝ²`. -/
def planarArc : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ {0}

/-- The planar arc is convex. -/
theorem convex_planarArc : Convex ℝ planarArc := (convex_Icc 0 1).prod (convex_singleton 0)

/-- The planar arc is compact. -/
theorem isCompact_planarArc : IsCompact planarArc := isCompact_Icc.prod isCompact_singleton

/-- The planar arc is a compact space. -/
instance compactSpace_planarArc : CompactSpace planarArc :=
  isCompact_iff_compactSpace.1 isCompact_planarArc

/-- The planar arc is contractible (it is convex and non-empty). -/
instance contractibleSpace_planarArc : ContractibleSpace planarArc :=
  convex_planarArc.contractibleSpace ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- The planar arc is locally path-connected. -/
instance locallyPathConnectedSpace_planarArc : LocallyPathConnectedSpace planarArc :=
  locallyPathConnectedSpace_of_locJoin fun _ hp => Convex.locJoin convex_planarArc hp

/-- The planar arc has covering dimension exactly `1` (the upper bound via the textbook axiom on
planar compacta with empty interior). -/
theorem coveringDim_planarArc : CoveringDimLE 1 planarArc ∧ ¬ CoveringDimLE 0 planarArc := by
  refine ⟨coveringDimLE_one_of_interior_eq_empty _ isCompact_planarArc ?_,
    not_coveringDimLE_zero (a := ⟨(0, 0), ⟨le_rfl, zero_le_one⟩, rfl⟩)
      (b := ⟨(1, 0), ⟨zero_le_one, le_rfl⟩, rfl⟩) fun h => ?_⟩
  · rw [planarArc, interior_prod_eq, interior_singleton, prod_empty]
  · have := congrArg (fun p : planarArc => (p : ℝ × ℝ).1) h
    norm_num at this

/-- The planar arc has empty wild set: all its loops are null-homotopic. -/
theorem wildSet_planarArc : wildSet planarArc = ∅ :=
  eq_empty_of_forall_notMem fun _ hx =>
    notMem_loopWildSet_of_forall Filter.univ_mem
      (fun _ _ => SimplyConnectedSpace.paths_homotopic _ _) (wildSet_subset_loopWildSet _ hx)

/-- The planar arc has a finite weak model: the constant map to a point is a homotopy
equivalence. -/
theorem planarArc_finite_weq :
    ∃ (Y : Type) (_ : TopologicalSpace Y), Finite Y ∧
      ∃ f : C(planarArc, Y), IsWeakHomotopyEquivalence f := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit planarArc
  exact ⟨Unit, inferInstance, inferInstance, e.toFun, HomotopyEquiv.isWeakHomotopyEquivalence e⟩

/-- No simply connected space is homotopy equivalent to the circle `C₀`. -/
theorem isEmpty_homotopyEquiv_earringCircle_of_simplyConnected (Y : Type*) [TopologicalSpace Y]
    [SimplyConnectedSpace Y] : IsEmpty (ContinuousMap.HomotopyEquiv (earringCircle 0) Y) :=
  ⟨fun e => circleLoop₀_not_homotopic_refl
    ((HomotopyEquiv.isWeakHomotopyEquivalence e).homotopic_of_map_homotopic
      (SimplyConnectedSpace.paths_homotopic _ _))⟩

/-- **Counterexample to Theorem 1.2 as stated, in dimension exactly one.** The planar circle `C₀`
and the planar arc `[0, 1] × {0}` are Peano continua of covering dimension exactly `1`, with empty
wild sets and finite weak models, which are not homotopy equivalent. Axioms: only
`coveringDimLE_one_of_interior_eq_empty` (for the upper bounds on the dimension). -/
theorem thm1_2_counterexample_dim_one :
    (CompactSpace (earringCircle 0) ∧ ConnectedSpace (earringCircle 0) ∧
      LocallyPathConnectedSpace (earringCircle 0) ∧ CoveringDimLE 1 (earringCircle 0) ∧
      ¬ CoveringDimLE 0 (earringCircle 0) ∧ wildSet (earringCircle 0) = ∅ ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Finite Y ∧
          ∃ f : C(earringCircle 0, Y), IsWeakHomotopyEquivalence f) ∧
    (CompactSpace planarArc ∧ ConnectedSpace planarArc ∧ LocallyPathConnectedSpace planarArc ∧
      CoveringDimLE 1 planarArc ∧ ¬ CoveringDimLE 0 planarArc ∧ wildSet planarArc = ∅ ∧
        ∃ (Y : Type) (_ : TopologicalSpace Y), Finite Y ∧
          ∃ f : C(planarArc, Y), IsWeakHomotopyEquivalence f) ∧
    IsEmpty (ContinuousMap.HomotopyEquiv (earringCircle 0) planarArc) :=
  ⟨⟨inferInstance, inferInstance, inferInstance, coveringDim_earringCircle_zero.1,
      coveringDim_earringCircle_zero.2, wildSet_earringCircle_zero, earringCircle_zero_finite_weq⟩,
    ⟨inferInstance, inferInstance, inferInstance, coveringDim_planarArc.1, coveringDim_planarArc.2,
      wildSet_planarArc, planarArc_finite_weq⟩,
    isEmpty_homotopyEquiv_earringCircle_of_simplyConnected planarArc⟩

end Peano.Sanity
