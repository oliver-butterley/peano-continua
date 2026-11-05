module

public import Peano.Defs
public import Peano.WeakEquiv

/-!
# Homotopy equivalences are weak homotopy equivalences

Proves `HomotopyEquiv.isWeakHomotopyEquivalence`: a homotopy equivalence `X ≃ₕ Y` induces
bijections on `π₀` and on every `πₙ(X, x)`, `n ≥ 1` (Hatcher, *Algebraic Topology*,
Proposition 1.18 and §4.1). (History: this fact was first assumed as an axiom of
`Peano.Axioms.Standard` under the same name; it is now proved here.) Consequences: homotopic maps
are weak homotopy equivalences simultaneously (`isWeakHomotopyEquivalence_iff_of_homotopic`), and
homeomorphisms are weak homotopy equivalences (`Homeomorph.isWeakHomotopyEquivalence`).

Also: change of base point as an equivalence (`HomotopyGroup.changeBaseEquiv`); the bridge between
`HomotopyGroup.map f 1 x` and Mathlib's `FundamentalGroup.map f x` and its consequences for loops;
the group isomorphism `π₁(X, x) ≃* π₁(Y, f x)` of a weak homotopy equivalence
(`IsWeakHomotopyEquivalence.fundamentalGroupEquiv`).

## Route

Mathlib has no change of base point for `πₙ`, `n ≥ 2`; it is built here for generalised loops.

* `CollarLoop.collarLoop p γ`, for `p : Path x y` and `γ ∈ Ωⁿ(X, y)`: `γ` shrunk affinely onto the
  inner cube `[1/4, 3/4]ⁿ` and the collar filled with `p`, parametrised by the sup-norm distance
  `d` to the centre (`p 0 = x` at `d = 1/2`, `p 1 = y` at `d = 1/4`).
* The design choice that keeps the proofs short: the shrinking is the *clamped* stretch
  `cubeStretch 1 t = clamp (2t - 1/2)` (coordinatewise), which maps the collar onto `∂Iⁿ`. Hence
  for any `Φ : I × Iⁿ → X` with `Φ (s, ∂Iⁿ) = p s` the single formula
  `t ↦ Φ (collarParam t, cubeStretch 1 t)` equals `collarLoop p (Φ (1, ·))`, and the homotopy
  `(r, t) ↦ Φ (r · collarParam t, cubeStretch r t)` (no case split) connects it to `Φ (0, ·)`
  rel `∂Iⁿ`: this is the moving-base-point lemma `CollarLoop.homotopic_collarLoop`.
* Case splits occur only in the private gluing `CollarLoop.glue` (inner cube versus collar, by
  `d ≤ 1/4`), whose continuity is proved once, for families over a parameter space.
* From the moving-base-point lemma: the collar loop along a constant path is homotopic to the
  loop; along `p` then `p.symm` it is homotopic to the loop (apply the lemma to the family of
  collar loops along final segments of `p`); so `HomotopyGroup.changeBase p` is a bijection, with
  inverse `changeBase p.symm` (`HomotopyGroup.changeBaseEquiv`).
  For a homotopy `H : f₀ ≃ f₁`, applying the lemma to `(s, t) ↦ H (s, γ t)` gives
  `f₀# = changeBase (H.evalAt x) ∘ f₁#`. The standard two-out-of-six argument then finishes.
* Only the induced functions are used (bijectivity is what `IsWeakHomotopyEquivalence` asks);
  that `changeBase` is a group homomorphism is not proved.
-/

@[expose] public section

open Set Topology unitInterval
open scoped Topology.Homotopy

noncomputable section

namespace Peano

namespace CollarLoop

variable {n : ℕ}

/-- Sup-norm distance of a point of `Iⁿ` from the centre `(1/2, …, 1/2)`. -/
def cubeDist (t : Fin n → I) : ℝ := ‖fun i => (t i : ℝ) - 1 / 2‖

/-- The collar parameter `clamp (2 - 4 d(t))`: `0` on `∂Iⁿ`, `1` on the inner cube
`[1/4, 3/4]ⁿ`. -/
def collarParam (t : Fin n → I) : I := projIcc (0 : ℝ) 1 zero_le_one (2 - 4 * cubeDist t)

/-- The stretch `t ↦ clamp ((1 + r) t - r / 2)` coordinatewise: the identity for `r = 0`, and for
`r = 1` the affine map of the inner cube `[1/4, 3/4]ⁿ` onto `Iⁿ`, collapsing the collar onto
`∂Iⁿ`. -/
def cubeStretch (r : I) (t : Fin n → I) : Fin n → I :=
  fun i => projIcc (0 : ℝ) 1 zero_le_one ((1 + r) * t i - r / 2)

/-- `cubeDist` is continuous. -/
theorem continuous_cubeDist : Continuous (cubeDist (n := n)) := by
  unfold cubeDist; fun_prop

/-- `collarParam` is continuous. -/
theorem continuous_collarParam : Continuous (collarParam (n := n)) :=
  continuous_projIcc.comp (by unfold cubeDist; fun_prop)

/-- `cubeStretch` is jointly continuous in the parameter and the point. -/
theorem continuous_cubeStretch :
    Continuous (fun q : I × (Fin n → I) => cubeStretch q.1 q.2) :=
  continuous_pi fun i => continuous_projIcc.comp (by fun_prop)

/-- `cubeStretch 0` is the identity. -/
@[simp] theorem cubeStretch_zero (t : Fin n → I) : cubeStretch 0 t = t := by
  funext i
  simp [cubeStretch, projIcc_of_mem _ (t i).2]

/-- `cubeStretch r` maps `∂Iⁿ` into `∂Iⁿ`. -/
theorem cubeStretch_mem_boundary (r : I) {t : Fin n → I} (ht : t ∈ Cube.boundary (Fin n)) :
    cubeStretch r t ∈ Cube.boundary (Fin n) := by
  obtain ⟨i, hi | hi⟩ := ht
  · refine ⟨i, Or.inl ?_⟩
    simp only [cubeStretch, hi, Icc.coe_zero, mul_zero, zero_sub]
    exact projIcc_of_le_left _ (by linarith [r.2.1])
  · refine ⟨i, Or.inr ?_⟩
    simp only [cubeStretch, hi, Icc.coe_one, mul_one]
    exact projIcc_of_right_le _ (by linarith [r.2.1])

/-- `cubeStretch 1` maps the closed collar `{t | 1/4 ≤ cubeDist t}` into `∂Iⁿ`. -/
theorem cubeStretch_one_mem_boundary {t : Fin n → I} (h : 1 / 4 ≤ cubeDist t) :
    cubeStretch 1 t ∈ Cube.boundary (Fin n) := by
  by_contra hb
  have hlt : ∀ i, |(t i : ℝ) - 1 / 2| < 1 / 4 := by
    intro i
    have h0 : cubeStretch 1 t i ≠ 0 := fun h' => hb ⟨i, Or.inl h'⟩
    have h1 : cubeStretch 1 t i ≠ 1 := fun h' => hb ⟨i, Or.inr h'⟩
    simp only [cubeStretch, Icc.coe_one] at h0 h1
    have a : 0 < (1 + 1) * (t i : ℝ) - 1 / 2 := by
      by_contra ha
      exact h0 (projIcc_of_le_left _ (by linarith))
    have b : (1 + 1) * (t i : ℝ) - 1 / 2 < 1 := by
      by_contra hb'
      exact h1 (projIcc_of_right_le _ (by linarith))
    rw [abs_lt]; constructor <;> linarith
  have : cubeDist t < 1 / 4 :=
    (pi_norm_lt_iff (by norm_num)).2 fun i => by simpa [Real.norm_eq_abs] using hlt i
  linarith

/-- `collarParam` is `1` on the inner cube. -/
theorem collarParam_eq_one {t : Fin n → I} (h : cubeDist t ≤ 1 / 4) : collarParam t = 1 := by
  unfold collarParam
  exact projIcc_of_right_le _ (by linarith)

/-- Points of `∂Iⁿ` are at sup-distance at least `1/2` from the centre. -/
theorem half_le_cubeDist {t : Fin n → I} (ht : t ∈ Cube.boundary (Fin n)) :
    1 / 2 ≤ cubeDist t := by
  obtain ⟨i, hi⟩ := ht
  have := norm_le_pi_norm (fun i => (t i : ℝ) - 1 / 2) i
  rcases hi with hi | hi <;> simp [hi, Real.norm_eq_abs] at this <;> norm_num at this ⊢ <;>
    exact this

/-- `collarParam` is `0` on `∂Iⁿ`. -/
theorem collarParam_eq_zero {t : Fin n → I} (ht : t ∈ Cube.boundary (Fin n)) :
    collarParam t = 0 := by
  unfold collarParam
  exact projIcc_of_le_left _ (by linarith [half_le_cubeDist ht])

variable {X : Type*} [TopologicalSpace X]

/-- Gluing a family of paths `P (z, ·)` (on the collar, by `collarParam`) and a family of maps
`D (z, ·)` of the cube (on the inner cube, by `cubeStretch 1`). Continuous when
`D (z, ∂Iⁿ) = P (z, 1)`, see `continuous_glue`. -/
private def glue {Z : Type*} (P : Z × I → X) (D : Z × (Fin n → I) → X) (q : Z × (Fin n → I)) : X :=
  if cubeDist q.2 ≤ 1 / 4 then D (q.1, cubeStretch 1 q.2) else P (q.1, collarParam q.2)

omit [TopologicalSpace X] in
/-- On `∂Iⁿ` the glued map is the path at time `0`. -/
private theorem glue_of_mem_boundary {Z : Type*} (P : Z × I → X) (D : Z × (Fin n → I) → X) (z : Z)
    {t : Fin n → I} (ht : t ∈ Cube.boundary (Fin n)) : glue P D (z, t) = P (z, 0) := by
  have : ¬ cubeDist t ≤ 1 / 4 := by linarith [half_le_cubeDist ht]
  rw [glue, ite_eq_right this, collarParam_eq_zero ht]

/-- The glued map is continuous when the two pieces match along the boundary of the inner
cube. -/
private theorem continuous_glue {Z : Type*} [TopologicalSpace Z] (P : C(Z × I, X))
    (D : C(Z × (Fin n → I), X)) (h : ∀ z, ∀ u ∈ Cube.boundary (Fin n), D (z, u) = P (z, 1)) :
    Continuous (glue P D) := by
  refine Continuous.if_le ?_ ?_ (continuous_cubeDist.comp continuous_snd) continuous_const ?_
  · exact D.continuous.comp (continuous_fst.prodMk
      (continuous_cubeStretch.comp (continuous_const.prodMk continuous_snd)))
  · exact P.continuous.comp (continuous_fst.prodMk (continuous_collarParam.comp continuous_snd))
  · intro q hq
    rw [h _ _ (cubeStretch_one_mem_boundary hq.ge), collarParam_eq_one hq.le]

/-- The generalised loop at `x` obtained from `γ` at `y` by shrinking `γ` onto the inner cube
`[1/4, 3/4]ⁿ` and filling the collar with `p`, parametrised by the sup-norm distance to the
centre (`p 0 = x` on `∂Iⁿ`, `p 1 = y` on the boundary of the inner cube). -/
def collarLoop {x y : X} (p : Path x y) (γ : Ω^ (Fin n) X y) : Ω^ (Fin n) X x :=
  ⟨⟨fun t => if cubeDist t ≤ 1 / 4 then γ (cubeStretch 1 t) else p (collarParam t), by
    have := (continuous_glue (p.toContinuousMap.comp ContinuousMap.snd)
      ((γ : C(Fin n → I, X)).comp ContinuousMap.snd)
      (fun (_ : Unit) u hu => by simp [γ.2 u hu])).comp
      ((continuous_const : Continuous fun _ : Fin n → I => ()).prodMk continuous_id)
    exact this⟩,
    fun t ht => by
      have : ¬ cubeDist t ≤ 1 / 4 := by linarith [half_le_cubeDist ht]
      change (if cubeDist t ≤ 1 / 4 then γ (cubeStretch 1 t) else p (collarParam t)) = x
      split_ifs
      rw [collarParam_eq_zero ht, Path.source]⟩

/-- Pointwise formula for `collarLoop`. -/
theorem collarLoop_apply {x y : X} (p : Path x y) (γ : Ω^ (Fin n) X y) (t : Fin n → I) :
    collarLoop p γ t =
      if cubeDist t ≤ 1 / 4 then γ (cubeStretch 1 t) else p (collarParam t) := rfl

/-- **Moving the base point.** If `Φ : I × Iⁿ → X` maps `{s} × ∂Iⁿ` to `p s` for every `s`, then
`Φ (0, ·)` is homotopic rel `∂Iⁿ` to the collar loop of `Φ (1, ·)` along `p`. The homotopy is
`(r, t) ↦ Φ (r · collarParam t, cubeStretch r t)`. -/
theorem homotopic_collarLoop {x y : X} (p : Path x y) (Φ : C(I × (Fin n → I), X))
    (hΦ : ∀ s, ∀ t ∈ Cube.boundary (Fin n), Φ (s, t) = p s)
    (γ₀ : Ω^ (Fin n) X x) (γ₁ : Ω^ (Fin n) X y) (h₀ : ∀ t, γ₀ t = Φ (0, t))
    (h₁ : ∀ t, γ₁ t = Φ (1, t)) :
    GenLoop.Homotopic γ₀ (collarLoop p γ₁) := by
  have hc : Continuous
      (fun q : I × (Fin n → I) => Φ (q.1 * collarParam q.2, cubeStretch q.1 q.2)) :=
    Φ.continuous.comp ((continuous_fst.mul (continuous_collarParam.comp continuous_snd)).prodMk
      continuous_cubeStretch)
  refine ⟨⟨⟨⟨_, hc⟩, fun t => ?_, fun t => ?_⟩, fun r t ht => ?_⟩⟩
  · simp [h₀]
  · change Φ (1 * collarParam t, cubeStretch 1 t) = collarLoop p γ₁ t
    rw [one_mul, collarLoop_apply]
    split_ifs with h
    · rw [collarParam_eq_one h, h₁]
    · rw [hΦ _ _ (cubeStretch_one_mem_boundary (le_of_not_ge h))]
  · simp only [ContinuousMap.coe_mk, collarParam_eq_zero ht, mul_zero]
    rw [hΦ _ _ (cubeStretch_mem_boundary r ht), γ₀.2 t ht, p.source]

/-- `collarLoop p` respects homotopy rel `∂Iⁿ`. -/
theorem collarLoop_homotopic {x y : X} (p : Path x y) {γ δ : Ω^ (Fin n) X y}
    (h : GenLoop.Homotopic γ δ) : GenLoop.Homotopic (collarLoop p γ) (collarLoop p δ) := by
  obtain ⟨H⟩ := h
  have hc := continuous_glue (p.toContinuousMap.comp ContinuousMap.snd) H.toContinuousMap
    (fun z u hu => by simp [H.eq_fst z hu, γ.2 u hu])
  refine ⟨⟨⟨⟨_, hc⟩, fun t => ?_, fun t => ?_⟩, fun r t ht => ?_⟩⟩
  · simp [glue, collarLoop_apply]
  · simp [glue, collarLoop_apply]
  · change glue (fun q : I × I => p q.2) (fun q => H q) (r, t) = collarLoop p γ t
    rw [glue_of_mem_boundary _ _ _ ht, GenLoop.boundary _ t ht]
    exact p.source

/-- The collar loop along a constant path is homotopic to the original loop. -/
theorem homotopic_collarLoop_refl {y : X} (γ : Ω^ (Fin n) X y) :
    GenLoop.Homotopic γ (collarLoop (Path.refl y) γ) :=
  homotopic_collarLoop (Path.refl y) ((γ : C(Fin n → I, X)).comp ContinuousMap.snd)
    (fun _ t ht => by simp [γ.2 t ht]) γ γ (fun _ => rfl) (fun _ => rfl)

/-- The map `(s, r) ↦ 1 - s + s r` of `I × I` into `I`; for fixed `s` it parametrises the final
segment `[1 - s, 1]`. -/
private def finalSegment : C(I × I, I) :=
  ⟨fun q => ⟨1 - q.1 + q.1 * q.2, by
    constructor <;> nlinarith [q.1.2.1, q.1.2.2, q.2.2.1, q.2.2.2]⟩, by fun_prop⟩

/-- Going along `p` and back is homotopic to going along the constant path. -/
theorem homotopic_collarLoop_symm {x y : X} (p : Path x y) (α : Ω^ (Fin n) X y) :
    GenLoop.Homotopic (collarLoop (Path.refl y) α) (collarLoop p.symm (collarLoop p α)) := by
  have hc := continuous_glue (p.toContinuousMap.comp finalSegment)
    ((α : C(Fin n → I, X)).comp ContinuousMap.snd)
    (fun z u hu => by
      have : finalSegment (z, 1) = 1 := by ext; simp [finalSegment]
      simp [α.2 u hu, this])
  refine homotopic_collarLoop p.symm ⟨_, hc⟩ (fun s t ht => ?_) _ _ (fun t => ?_) (fun t => ?_)
  · have hs : finalSegment (s, 0) = σ s := by
      ext; simp [finalSegment]
    change glue _ _ (s, t) = _
    rw [glue_of_mem_boundary _ _ _ ht]
    simp [hs]
  · have hs : ∀ r, finalSegment (0, r) = 1 := fun r => by ext; simp [finalSegment]
    simp only [ContinuousMap.coe_mk, glue, ContinuousMap.comp_apply, collarLoop_apply]
    split_ifs <;> simp [hs]
  · have hs : ∀ r, finalSegment (1, r) = r := fun r => by ext; simp [finalSegment]
    simp only [ContinuousMap.coe_mk, glue, ContinuousMap.comp_apply, collarLoop_apply]
    split_ifs <;> simp [hs]

end CollarLoop

/-! ### Change of base point -/

open CollarLoop

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Change of base point along a path `p : x ⟶ y`: the map `πₙ(X, y) → πₙ(X, x)` induced by
`collarLoop p`. -/
def HomotopyGroup.changeBase {x y : X} (p : Path x y) (n : ℕ) : π_ n X y → π_ n X x :=
  Quotient.map (collarLoop p) fun _ _ h => collarLoop_homotopic p h

/-- Change of base point along `p.symm` undoes change of base point along `p`. -/
theorem HomotopyGroup.changeBase_symm_changeBase {x y : X} (p : Path x y) (n : ℕ)
    (q : π_ n X y) : changeBase p.symm n (changeBase p n q) = q := by
  induction q using Quotient.ind with | _ α => ?_
  exact Quotient.sound ((homotopic_collarLoop_refl α).trans (homotopic_collarLoop_symm p α)).symm


/-- **Change of base point as an equivalence** `πₙ(X, y) ≃ πₙ(X, x)`, for a path `p : x ⟶ y`; the
inverse is change of base point along `p.symm`.

Direction: for `n = 1` this sends the class of a loop `γ` at `y` to the class of `p γ p⁻` at `x`,
i.e. it goes *against* the path. Mathlib's `FundamentalGroup.fundamentalGroupMulEquivOfPath p`
(`π₁(X, x) ≃* π₁(X, y)`, `[γ] ↦ [p⁻ γ p]`) and the change of base point `φ_α([γ]) = [α⁻ γ α]`
along `α : g b₀ ⟶ x₀` in the Eda axiom `eda_exists_map_earring` go *along* the path: they
correspond to `changeBaseEquiv p.symm` (up to `HomotopyGroup.pi1EquivFundamentalGroup`, which is
not proved here). Only the bijection is constructed; that it is a group isomorphism is not
needed. -/
def HomotopyGroup.changeBaseEquiv {x y : X} (p : Path x y) (n : ℕ) : π_ n X y ≃ π_ n X x where
  toFun := changeBase p n
  invFun := changeBase p.symm n
  left_inv := changeBase_symm_changeBase p n
  right_inv q := by simpa using changeBase_symm_changeBase p.symm n q

/-- `changeBaseEquiv p n` is `changeBase p n`. -/
@[simp] theorem HomotopyGroup.changeBaseEquiv_apply {x y : X} (p : Path x y) (n : ℕ)
    (q : π_ n X y) : changeBaseEquiv p n q = changeBase p n q :=
  rfl

/-- The inverse of `changeBaseEquiv p n` is change of base point along `p.symm`. -/
@[simp] theorem HomotopyGroup.changeBaseEquiv_symm_apply {x y : X} (p : Path x y) (n : ℕ)
    (q : π_ n X x) : (changeBaseEquiv p n).symm q = changeBase p.symm n q :=
  rfl

/-- Change of base point along a path is a bijection. -/
theorem HomotopyGroup.changeBase_bijective {x y : X} (p : Path x y) (n : ℕ) :
    Function.Bijective (changeBase p n) :=
  (changeBaseEquiv p n).bijective

/-- For a homotopy `H : f₀ ≃ f₁`, `f₀#` is `f₁#` followed by change of base point along the track
`s ↦ H (s, x)` of the base point. -/
theorem HomotopyGroup.map_eq_changeBase_comp {f₀ f₁ : C(X, Y)} (H : f₀.Homotopy f₁) (n : ℕ)
    (x : X) : map f₀ n x = changeBase (H.evalAt x) n ∘ map f₁ n x := by
  funext q
  induction q using Quotient.ind with | _ γ => ?_
  exact Quotient.sound (homotopic_collarLoop (H.evalAt x)
    ⟨fun q => H (q.1, γ q.2), by fun_prop⟩ (fun s t ht => by simp [GenLoop.boundary γ t ht]) _ _
    (fun t => (H.apply_zero (γ t)).symm) (fun t => (H.apply_one (γ t)).symm))

/-- Homotopic maps induce bijections on `πₙ` simultaneously. -/
theorem HomotopyGroup.bijective_map_iff_of_homotopic {f₀ f₁ : C(X, Y)} (h : f₀.Homotopic f₁)
    (n : ℕ) (x : X) :
    Function.Bijective (map f₀ n x) ↔ Function.Bijective (map f₁ n x) := by
  obtain ⟨H⟩ := h
  rw [map_eq_changeBase_comp H]
  exact ⟨fun h => (Function.Bijective.of_comp_iff' (changeBase_bijective _ n) _).1 h,
    fun h => (changeBase_bijective _ n).comp h⟩

/-- The identity induces the identity on `πₙ`. -/
theorem HomotopyGroup.map_id (n : ℕ) (x : X) : map (ContinuousMap.id X) n x = id := by
  funext q
  induction q using Quotient.ind
  rfl

/-- The identity induces the identity on `π₀`. -/
theorem ZerothHomotopy.map_id : ZerothHomotopy.map (ContinuousMap.id X) = id := by
  funext q
  induction q using Quotient.ind
  rfl

/-- Homotopic maps induce the same map on `π₀`. -/
theorem ZerothHomotopy.map_eq_of_homotopic {f₀ f₁ : C(X, Y)} (h : f₀.Homotopic f₁) :
    ZerothHomotopy.map f₀ = ZerothHomotopy.map f₁ := by
  obtain ⟨H⟩ := h
  funext q
  induction q using Quotient.ind with | _ x => ?_
  exact Quotient.sound ⟨H.evalAt x⟩

/-- **A homotopy equivalence is a weak homotopy equivalence.** -/
theorem HomotopyEquiv.isWeakHomotopyEquivalence (e : ContinuousMap.HomotopyEquiv X Y) :
    IsWeakHomotopyEquivalence e.toFun := by
  set f := e.toFun
  set g := e.invFun
  refine ⟨?_, fun n _ x => ?_⟩
  · have hgf : Function.Bijective (ZerothHomotopy.map g ∘ ZerothHomotopy.map f) := by
      rw [← ZerothHomotopy.map_comp, ZerothHomotopy.map_eq_of_homotopic e.left_inv,
        ZerothHomotopy.map_id]
      exact Function.bijective_id
    have hfg : Function.Bijective (ZerothHomotopy.map f ∘ ZerothHomotopy.map g) := by
      rw [← ZerothHomotopy.map_comp, ZerothHomotopy.map_eq_of_homotopic e.right_inv,
        ZerothHomotopy.map_id]
      exact Function.bijective_id
    exact ⟨hgf.1.of_comp, hfg.2.of_comp⟩
  · have hgf : Function.Bijective (HomotopyGroup.map g n (f x) ∘ HomotopyGroup.map f n x) := by
      rw [← HomotopyGroup.map_comp, HomotopyGroup.bijective_map_iff_of_homotopic e.left_inv,
        HomotopyGroup.map_id]
      exact Function.bijective_id
    have hfg : Function.Bijective
        (HomotopyGroup.map f n (g (f x)) ∘ HomotopyGroup.map g n (f x)) := by
      rw [← HomotopyGroup.map_comp, HomotopyGroup.bijective_map_iff_of_homotopic e.right_inv,
        HomotopyGroup.map_id]
      exact Function.bijective_id
    have hg : Function.Bijective (HomotopyGroup.map g n (f x)) := ⟨hfg.1.of_comp, hgf.2.of_comp⟩
    exact (Function.Bijective.of_comp_iff' hg _).1 hgf

/-- **Homotopy invariance**: homotopic maps are weak homotopy equivalences simultaneously. -/
theorem isWeakHomotopyEquivalence_iff_of_homotopic {f₀ f₁ : C(X, Y)} (h : f₀.Homotopic f₁) :
    IsWeakHomotopyEquivalence f₀ ↔ IsWeakHomotopyEquivalence f₁ := by
  unfold IsWeakHomotopyEquivalence
  rw [ZerothHomotopy.map_eq_of_homotopic h]
  simp only [HomotopyGroup.bijective_map_iff_of_homotopic h]

/-- A map homotopic to a weak homotopy equivalence is a weak homotopy equivalence. -/
theorem IsWeakHomotopyEquivalence.of_homotopic {f₀ f₁ : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f₀) (h : f₀.Homotopic f₁) : IsWeakHomotopyEquivalence f₁ :=
  (isWeakHomotopyEquivalence_iff_of_homotopic h).1 hf

/-- **A homeomorphism is a weak homotopy equivalence.** -/
theorem Homeomorph.isWeakHomotopyEquivalence (e : X ≃ₜ Y) :
    IsWeakHomotopyEquivalence (e : C(X, Y)) :=
  HomotopyEquiv.isWeakHomotopyEquivalence e.toHomotopyEquiv

/-! ### The fundamental group -/

/-- Under `π₁(X, x) ≃ FundamentalGroup X x`, the map `f#` on `π₁` is Mathlib's
`FundamentalGroup.map f x`. -/
theorem HomotopyGroup.pi1EquivFundamentalGroup_map (f : C(X, Y)) (x : X) (q : π_ 1 X x) :
    HomotopyGroup.pi1EquivFundamentalGroup (map f 1 x q) =
      FundamentalGroup.map f x (HomotopyGroup.pi1EquivFundamentalGroup q) := by
  induction q using Quotient.ind
  -- definitional: both sides are the class of the loop `t ↦ f (q t)`; Mathlib has no `simp` API
  -- for `homotopyGroupEquivFundamentalGroupOfUnique`
  rfl

/-- `FundamentalGroup.map` on the class of a loop. -/
theorem fundamentalGroup_map_fromPath (f : C(X, Y)) {x : X} (γ : Path x x) :
    FundamentalGroup.map f x (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.map f.continuous⟧ := by
  ext
  simp [Path.Homotopic.Quotient.mk_map]

/-- Two loops have the same class in the fundamental group iff they are homotopic. -/
theorem fundamentalGroup_fromPath_eq_iff {x : X} (γ δ : Path x x) :
    FundamentalGroup.fromPath ⟦γ⟧ = FundamentalGroup.fromPath ⟦δ⟧ ↔ γ.Homotopic δ := by
  constructor
  · intro h
    exact Quotient.exact (congrArg FundamentalGroup.toPath h)
  · intro h
    exact congrArg _ (Quotient.sound h)

/-- `FundamentalGroup.map f x` is the conjugate of `f#` on `π₁` by
`HomotopyGroup.pi1EquivFundamentalGroup`. -/
theorem fundamentalGroup_map_eq (f : C(X, Y)) (x : X) :
    ⇑(FundamentalGroup.map f x) = HomotopyGroup.pi1EquivFundamentalGroup ∘
      HomotopyGroup.map f 1 x ∘ HomotopyGroup.pi1EquivFundamentalGroup.symm := by
  funext a
  simp [HomotopyGroup.pi1EquivFundamentalGroup_map]

/-- `f#` is bijective on `π₁(X, x)` iff `FundamentalGroup.map f x` is. -/
theorem fundamentalGroup_map_bijective_iff (f : C(X, Y)) (x : X) :
    Function.Bijective (FundamentalGroup.map f x) ↔
      Function.Bijective (HomotopyGroup.map f 1 x) := by
  rw [fundamentalGroup_map_eq, Function.Bijective.of_comp_iff' (Equiv.bijective _),
    Function.Bijective.of_comp_iff _ (Equiv.bijective _)]

/-- A weak homotopy equivalence induces isomorphisms of fundamental groups. -/
theorem IsWeakHomotopyEquivalence.fundamentalGroup_map_bijective {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) (x : X) :
    Function.Bijective (FundamentalGroup.map f x) :=
  (fundamentalGroup_map_bijective_iff f x).2 (hf.2 1 le_rfl x)

/-- If `f` is injective on `π₁(X, x)`, loops at `x` whose images are homotopic are homotopic. -/
theorem homotopic_of_map_homotopic {f : C(X, Y)} {x : X}
    (hf : Function.Injective (FundamentalGroup.map f x)) {γ δ : Path x x}
    (h : (γ.map f.continuous).Homotopic (δ.map f.continuous)) : γ.Homotopic δ := by
  rw [← fundamentalGroup_fromPath_eq_iff] at h ⊢
  rw [← fundamentalGroup_map_fromPath, ← fundamentalGroup_map_fromPath] at h
  exact hf h

/-- If `f` is surjective on `π₁(X, x)`, every loop at `f x` is homotopic to the image of a loop
at `x`. -/
theorem exists_map_homotopic {f : C(X, Y)} {x : X}
    (hf : Function.Surjective (FundamentalGroup.map f x)) (δ : Path (f x) (f x)) :
    ∃ γ : Path x x, (γ.map f.continuous).Homotopic δ := by
  obtain ⟨a, ha⟩ := hf (FundamentalGroup.fromPath ⟦δ⟧)
  obtain ⟨γ, hγ⟩ := Quotient.exists_rep (FundamentalGroup.toPath a)
  have hγa : FundamentalGroup.fromPath ⟦γ⟧ = a := by rw [hγ]
  refine ⟨γ, (fundamentalGroup_fromPath_eq_iff _ _).1 ?_⟩
  rw [← fundamentalGroup_map_fromPath, hγa, ha]

/-- For a weak homotopy equivalence, loops at `x` whose images are homotopic are homotopic. -/
theorem IsWeakHomotopyEquivalence.homotopic_of_map_homotopic {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) {x : X} {γ δ : Path x x}
    (h : (γ.map f.continuous).Homotopic (δ.map f.continuous)) : γ.Homotopic δ :=
  Peano.homotopic_of_map_homotopic (hf.fundamentalGroup_map_bijective x).1 h

/-- For a weak homotopy equivalence, every loop at `f x` is homotopic to the image of a loop at
`x`. -/
theorem IsWeakHomotopyEquivalence.exists_map_homotopic {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) {x : X} (δ : Path (f x) (f x)) :
    ∃ γ : Path x x, (γ.map f.continuous).Homotopic δ :=
  Peano.exists_map_homotopic (hf.fundamentalGroup_map_bijective x).2 δ

/-! ### Inverting the induced map on `π₁` -/

/-- A bijective induced map `f# : π₁(X, x) → π₁(Y, f x)` as a group isomorphism. -/
def fundamentalGroupMapEquiv (f : C(X, Y)) (x : X)
    (hf : Function.Bijective (FundamentalGroup.map f x)) :
    FundamentalGroup X x ≃* FundamentalGroup Y (f x) :=
  MulEquiv.ofBijective (FundamentalGroup.map f x) hf

/-- `fundamentalGroupMapEquiv f x hf` is `FundamentalGroup.map f x`. -/
@[simp] theorem fundamentalGroupMapEquiv_apply (f : C(X, Y)) (x : X)
    (hf : Function.Bijective (FundamentalGroup.map f x)) (a : FundamentalGroup X x) :
    fundamentalGroupMapEquiv f x hf a = FundamentalGroup.map f x a :=
  rfl

/-- A weak homotopy equivalence induces group isomorphisms of fundamental groups. -/
def IsWeakHomotopyEquivalence.fundamentalGroupEquiv {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (f x) :=
  fundamentalGroupMapEquiv f x (hf.fundamentalGroup_map_bijective x)

/-- `hf.fundamentalGroupEquiv x` is `FundamentalGroup.map f x`. -/
@[simp] theorem IsWeakHomotopyEquivalence.fundamentalGroupEquiv_apply {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) (x : X) (a : FundamentalGroup X x) :
    hf.fundamentalGroupEquiv x a = FundamentalGroup.map f x a :=
  rfl

end Peano
