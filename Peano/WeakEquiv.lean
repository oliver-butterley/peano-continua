module

public import Peano.Defs

/-!
# Lifting for cubes gives a Serre fibration and a weak homotopy equivalence

The deduction of Corollary 5.6 from Lemma 5.5 in Brazas–Pavešić ("applying Lemma 5.5 to the pairs
`(Iⁿ⁺¹, Iⁿ × {0})` and `(Iⁿ⁺¹, ∂Iⁿ⁺¹)`"), made independent of the coarsification: a map with the
relative lifting property `HasCubeLifting` for every closed subset of every cube `Iⁿ` is a Serre
fibration and a weak homotopy equivalence. For `n = 0` the cube is a point, so the lifting
property already contains surjectivity.

Also: weak homotopy equivalences compose (used to combine Meilstrup's homotopy equivalence with
the coarsification map).
-/

@[expose] public section

open Set Topology unitInterval
open scoped Topology.Homotopy

noncomputable section

namespace Peano

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- `p` has the relative lifting property for closed subsets of cubes: for every closed
`A ⊆ Iⁿ`, maps `f : A → X` and `g : Iⁿ → Y` with `p ∘ f = g|_A` admit `G : Iⁿ → X` with
`G|_A = f` and `p ∘ G = g`. -/
def HasCubeLifting (p : C(X, Y)) : Prop :=
  ∀ (n : ℕ) (A : Set (Fin n → I)), IsClosed A → ∀ (f : C(A, X)) (g : C(Fin n → I, Y)),
    (∀ a, p (f a) = g a) → ∃ G : C(Fin n → I, X), (∀ a : A, G a = f a) ∧ ∀ z, p (G z) = g z

/-- The boundary of a finite-dimensional cube is closed. -/
theorem isClosed_cube_boundary (N : Type*) [Finite N] : IsClosed (Cube.boundary N) := by
  have : Cube.boundary N = ⋃ i, ({y : N → I | y i = 0} ∪ {y | y i = 1}) := by
    ext y; simp [Cube.boundary]
  rw [this]
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)

/-- `Fin.tail` is continuous on cubes. -/
theorem continuous_cube_tail (n : ℕ) : Continuous (fun z : Fin (n + 1) → I => Fin.tail z) :=
  continuous_pi fun i => continuous_apply i.succ

/-- `Fin.cons` is continuous as a map `Iⁿ × I → Iⁿ⁺¹`. -/
theorem continuous_cube_cons (n : ℕ) :
    Continuous (fun z : (Fin n → I) × I => (Fin.cons z.2 z.1 : Fin (n + 1) → I)) :=
  by fun_prop

/-- Lifting for `(Iⁿ⁺¹, Iⁿ × {0})` gives the homotopy lifting property for cubes. -/
theorem isSerreFibration_of_hasCubeLifting {p : C(X, Y)} (hp : HasCubeLifting p) :
    IsSerreFibration p := by
  intro n F f₀ hf₀
  let A : Set (Fin (n + 1) → I) := {z | z 0 = 0}
  have hA : IsClosed A := isClosed_eq (continuous_apply 0) continuous_const
  let f : C(A, X) := ⟨fun a => f₀ (Fin.tail a.1),
    f₀.continuous.comp ((continuous_cube_tail n).comp continuous_subtype_val)⟩
  let g : C(Fin (n + 1) → I, Y) := ⟨fun z => F (Fin.tail z, z 0),
    F.continuous.comp ((continuous_cube_tail n).prodMk (continuous_apply 0))⟩
  obtain ⟨G, hGA, hGp⟩ := hp (n + 1) A hA f g (fun a => by
    have ha : a.1 0 = 0 := a.2
    simp only [f, g, ContinuousMap.coe_mk]
    rw [hf₀, ha])
  refine ⟨G.comp ⟨_, continuous_cube_cons n⟩, fun y => ?_, fun z => ?_⟩
  · have := hGA ⟨Fin.cons 0 y, by simp [A]⟩
    simpa [f] using this
  · simp [hGp, g]

/-- Lifting for the point `I⁰` relative to `∅` gives surjectivity on `π₀`. -/
theorem HasCubeLifting.zerothHomotopy_map_surjective {p : C(X, Y)} (hp : HasCubeLifting p) :
    Function.Surjective (ZerothHomotopy.map p) := by
  intro q
  induction q using Quotient.ind with | _ y => ?_
  obtain ⟨G, -, hG⟩ := hp 0 ∅ isClosed_empty
    ⟨fun a => absurd a.2 (Set.notMem_empty _), continuous_of_discreteTopology⟩
    (ContinuousMap.const _ y) (fun a => absurd a.2 (Set.notMem_empty _))
  refine ⟨Quotient.mk _ (G default), ?_⟩
  change Quotient.mk _ (p (G default)) = Quotient.mk _ y
  rw [hG]
  rfl

/-- Lifting for `(I, {0, 1})` gives injectivity on `π₀`. -/
theorem HasCubeLifting.zerothHomotopy_map_injective {p : C(X, Y)} (hp : HasCubeLifting p) :
    Function.Injective (ZerothHomotopy.map p) := by
  intro q₀ q₁
  induction q₀ using Quotient.ind with | _ x₀ => ?_
  induction q₁ using Quotient.ind with | _ x₁ => ?_
  intro h
  obtain ⟨γ⟩ : Joined (p x₀) (p x₁) := Quotient.exact h
  let A : Set (Fin 1 → I) := {z | z 0 = 0 ∨ z 0 = 1}
  have hA : IsClosed A := (isClosed_eq (continuous_apply 0) continuous_const).union
    (isClosed_eq (continuous_apply 0) continuous_const)
  have hc : Continuous (fun a : A => if ((a.1 0 : I) : ℝ) ≤ 1 / 2 then x₀ else x₁) := by
    refine Continuous.if_le continuous_const continuous_const
      (continuous_subtype_val.comp ((continuous_apply 0).comp continuous_subtype_val))
      continuous_const ?_
    intro a ha
    rcases (a.2 : a.1 0 = 0 ∨ a.1 0 = 1) with h | h <;> rw [h] at ha <;> norm_num at ha
  let g : C(Fin 1 → I, Y) := ⟨fun z => γ (z 0), by fun_prop⟩
  obtain ⟨G, hGA, hGp⟩ := hp 1 A hA ⟨_, hc⟩ g (fun a => by
    rcases (a.2 : a.1 0 = 0 ∨ a.1 0 = 1) with h | h <;> norm_num [g, h])
  have h0 := hGA ⟨fun _ => 0, Or.inl rfl⟩
  have h1 := hGA ⟨fun _ => 1, Or.inr rfl⟩
  refine Quotient.sound ⟨⟨⟨fun t => G (fun _ => t), by fun_prop⟩, ?_, ?_⟩⟩
  · simpa using h0
  · norm_num at h1
    exact h1

/-- Lifting for `(Iⁿ, ∂Iⁿ)` with constant data on the boundary gives surjectivity on `πₙ`. -/
theorem HasCubeLifting.homotopyGroup_map_surjective {p : C(X, Y)} (hp : HasCubeLifting p)
    (n : ℕ) (x : X) : Function.Surjective (HomotopyGroup.map p n x) := by
  intro q
  induction q using Quotient.ind with | _ γ => ?_
  obtain ⟨G, hGA, hGp⟩ := hp n _ (isClosed_cube_boundary (Fin n)) (ContinuousMap.const _ x) γ.1
    (fun a => (γ.2 a.1 a.2).symm)
  refine ⟨Quotient.mk _ ⟨G, fun y hy => hGA ⟨y, hy⟩⟩, ?_⟩
  change Quotient.mk _ (GenLoop.map p _) = Quotient.mk _ γ
  congr 1
  exact Subtype.ext (ContinuousMap.ext hGp)

/-- Lifting for `(Iⁿ⁺¹, ∂Iⁿ⁺¹)` turns a homotopy rel boundary downstairs into one upstairs,
giving injectivity on `πₙ`. -/
theorem HasCubeLifting.homotopyGroup_map_injective {p : C(X, Y)} (hp : HasCubeLifting p)
    (n : ℕ) (x : X) : Function.Injective (HomotopyGroup.map p n x) := by
  intro q₀ q₁
  induction q₀ using Quotient.ind with | _ γ => ?_
  induction q₁ using Quotient.ind with | _ δ => ?_
  intro h
  obtain ⟨H⟩ : GenLoop.Homotopic (GenLoop.map p γ) (GenLoop.map p δ) := Quotient.exact h
  have hγ : ∀ y ∈ Cube.boundary (Fin n), γ.1 y = x := γ.2
  have hδ : ∀ y ∈ Cube.boundary (Fin n), δ.1 y = x := δ.2
  let A := Cube.boundary (Fin (n + 1))
  have htail : Continuous (fun a : A => Fin.tail a.1) :=
    (continuous_cube_tail n).comp continuous_subtype_val
  have hc : Continuous (fun a : A =>
      if ((a.1 0 : I) : ℝ) ≤ 1 / 2 then γ.1 (Fin.tail a.1) else δ.1 (Fin.tail a.1)) := by
    refine Continuous.if_le (γ.1.continuous.comp htail) (δ.1.continuous.comp htail)
      (continuous_subtype_val.comp ((continuous_apply 0).comp continuous_subtype_val))
      continuous_const ?_
    intro a ha
    obtain ⟨i, hi⟩ := a.2
    cases i using Fin.cases with
    | zero => rcases hi with hi | hi <;> rw [hi] at ha <;> norm_num at ha
    | succ j =>
      have hb : Fin.tail a.1 ∈ Cube.boundary (Fin n) := ⟨j, hi⟩
      rw [hγ _ hb, hδ _ hb]
  let g : C(Fin (n + 1) → I, Y) := ⟨fun z => H (z 0, Fin.tail z),
    (map_continuous H).comp ((continuous_apply 0).prodMk (continuous_cube_tail n))⟩
  obtain ⟨G, hGA, hGp⟩ := hp (n + 1) A (isClosed_cube_boundary _) ⟨_, hc⟩ g (fun a => by
    obtain ⟨i, hi⟩ := a.2
    simp only [ContinuousMap.coe_mk, g]
    cases i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · rw [hi]
        simp
        rfl
      · rw [hi]
        norm_num
        rfl
    | succ j =>
      have hb : Fin.tail a.1 ∈ Cube.boundary (Fin n) := ⟨j, hi⟩
      rw [H.eq_fst _ hb]
      split_ifs
      · rfl
      · change p (δ.1 _) = p (γ.1 _)
        rw [hγ _ hb, hδ _ hb])
  have hGc : Continuous (fun z : I × (Fin n → I) => G (Fin.cons z.1 z.2)) :=
    G.continuous.comp (by fun_prop)
  refine Quotient.sound ⟨⟨⟨⟨_, hGc⟩, fun y => ?_, fun y => ?_⟩, fun t y hy => ?_⟩⟩
  · have := hGA ⟨Fin.cons 0 y, ⟨0, Or.inl rfl⟩⟩
    simpa using this
  · have := hGA ⟨Fin.cons 1 y, ⟨0, Or.inr rfl⟩⟩
    norm_num at this
    exact this
  · obtain ⟨j, hj⟩ := hy
    have hb : (Fin.cons t y : Fin (n + 1) → I) ∈ A := ⟨j.succ, by simpa using hj⟩
    have := hGA ⟨_, hb⟩
    have hy : y ∈ Cube.boundary (Fin n) := ⟨j, hj⟩
    simp only [ContinuousMap.coe_mk, Fin.tail_cons, Fin.cons_zero] at this
    change G (Fin.cons t y) = γ.1 y
    rw [this]
    split_ifs
    · rfl
    · rw [hγ _ hy, hδ _ hy]

/-- Lifting for `(Iⁿ, ∂Iⁿ)` and `(Iⁿ⁺¹, ∂Iⁿ⁺¹)` gives bijections on `π₀` and on every `πₙ`. -/
theorem isWeakHomotopyEquivalence_of_hasCubeLifting {p : C(X, Y)} (hp : HasCubeLifting p) :
    IsWeakHomotopyEquivalence p :=
  ⟨⟨hp.zerothHomotopy_map_injective, hp.zerothHomotopy_map_surjective⟩,
    fun n _ x => ⟨hp.homotopyGroup_map_injective n x, hp.homotopyGroup_map_surjective n x⟩⟩

/-- Functoriality of the induced map on `π₀`. -/
theorem ZerothHomotopy.map_comp (g : C(Y, Z)) (f : C(X, Y)) :
    ZerothHomotopy.map (g.comp f) = ZerothHomotopy.map g ∘ ZerothHomotopy.map f := by
  funext q
  induction q using Quotient.ind
  rfl

/-- Functoriality of the induced map on `πₙ`. -/
theorem HomotopyGroup.map_comp (g : C(Y, Z)) (f : C(X, Y)) (n : ℕ) (x : X) :
    HomotopyGroup.map (g.comp f) n x = HomotopyGroup.map g n (f x) ∘ HomotopyGroup.map f n x := by
  funext q
  induction q using Quotient.ind
  rfl

/-- Weak homotopy equivalences are closed under composition. -/
theorem IsWeakHomotopyEquivalence.comp {g : C(Y, Z)} {f : C(X, Y)}
    (hg : IsWeakHomotopyEquivalence g) (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (g.comp f) := by
  refine ⟨?_, fun n hn x => ?_⟩
  · rw [ZerothHomotopy.map_comp]
    exact hg.1.comp hf.1
  · rw [HomotopyGroup.map_comp]
    exact (hg.2 n hn (f x)).comp (hf.2 n hn x)

end Peano
