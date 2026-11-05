module

public import Peano.Earring
public import Peano.HomotopyEquiv

/-!
# Operations on maps from the earring

Reusable API around the gluing lemma `Peano.earringMap` (`Peano.Earring`), used for §6 of
Brazas–Pavešić (arXiv:2610.35875), in particular for the proofs of Lemma 6.2 and Lemma 6.4 in
`Peano.OnlyIf`.

* **Shrinking loop families** (`LoopsShrinkTo`, defined in `Peano.Earring`). The property is
  preserved by post-composition with a map (`LoopsShrinkTo.map`), by passing to a subsequence along
  `ν → ∞` (`LoopsShrinkTo.comp_tendsto`), by interleaving two families (`LoopsShrinkTo.interleave`)
  and by casting the base point (`LoopsShrinkTo.cast`).
* **Extensionality and composition.** Maps from the earring agreeing on all loops `ℓₖ` are equal
  (`earring_ext`); `g ∘ earringMap y γ` and `earringMap y γ ∘ earringSub ν` are again `earringMap`s
  (`comp_earringMap`, `earringMap_comp_earringSub`).
* **Interleaving.** `earringInterleave f₀ f₁ h`, for maps `f₀ f₁ : 𝔼 → Y` with
  `f₀ b₀ = f₁ b₀`, sends `ℓ_{2k}` to `f₀ ∘ ℓₖ` and `ℓ_{2k+1}` to `f₁ ∘ ℓₖ`; precomposed with the
  sub-earring maps `earringSub (2·)` and `earringSub (2·+1)` it gives back `f₀` and `f₁`.
* **Full essentiality of glued maps** (`fullyEssential_earringMap_iff`).
* **`FundamentalGroup.mapOfEq`** (the map `π₁(X, x) → π₁(Y, y)` induced by `f` with `f x = y`) on
  the class of a loop (`fundamentalGroup_mapOfEq_fromPath`).

## Design

Statements are about `Path.Homotopic` rather than about elements of fundamental groups wherever
possible; homotopy classes of loops at a point that equals the base point only propositionally
(e.g. `earringMap y γ h earringBase = y`) are compared through `Path.cast` (the cast lemmas
`homotopic_cast_iff`, `cast_homotopic_refl_iff`, `path_cast_cast` are in `Peano.Earring`). The
interleaved family is `k ↦ if k % 2 = 0 then γ₀ (k / 2) else γ₁ (k / 2)` (`interleaveSeq`), so
that its values at `2k` and `2k + 1` reduce by `simp`.
-/

@[expose] public section

open Set Filter Topology unitInterval

noncomputable section

namespace Peano

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ### Shrinking loop families -/

namespace LoopsShrinkTo

variable {y : Y} {γ : ℕ → Path y y}

/-- The images of shrinking loops under a map shrink to the image of the base point. -/
theorem map (h : LoopsShrinkTo y γ) (g : C(Y, Z)) :
    LoopsShrinkTo (g y) (fun k => (γ k).map g.continuous) := by
  intro U hU
  filter_upwards [h _ (g.continuous.continuousAt hU)] with k hk
  rw [Path.map_coe, range_comp]
  exact image_subset_iff.2 hk

/-- A subsequence (along `ν → ∞`) of a shrinking family shrinks. -/
theorem comp_tendsto (h : LoopsShrinkTo y γ) {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) :
    LoopsShrinkTo y (fun k => γ (ν k)) :=
  fun U hU => hν.eventually (h U hU)

/-- Casting the base point of a shrinking family along an equality gives a shrinking family. -/
theorem cast (h : LoopsShrinkTo y γ) {y' : Y} (e : y' = y) :
    LoopsShrinkTo y' (fun k => (γ k).cast e e) := by
  subst e
  exact h

end LoopsShrinkTo

/-! ### Interleaving two sequences -/

/-- Interleaving of two sequences: `interleaveSeq a b (2k) = a k`,
`interleaveSeq a b (2k + 1) = b k`. -/
def interleaveSeq {α : Sort*} (a b : ℕ → α) (k : ℕ) : α :=
  if k % 2 = 0 then a (k / 2) else b (k / 2)

/-- The even terms of an interleaved sequence. -/
@[simp] theorem interleaveSeq_two_mul {α : Sort*} (a b : ℕ → α) (k : ℕ) :
    interleaveSeq a b (2 * k) = a k := by
  simp [interleaveSeq]

/-- The odd terms of an interleaved sequence. -/
@[simp] theorem interleaveSeq_two_mul_add_one {α : Sort*} (a b : ℕ → α) (k : ℕ) :
    interleaveSeq a b (2 * k + 1) = b k := by
  simp only [interleaveSeq, show (2 * k + 1) % 2 ≠ 0 by omega, ↓reduceIte,
    show (2 * k + 1) / 2 = k by omega]

/-- `k ↦ 2k` tends to infinity. -/
theorem tendsto_nat_two_mul_atTop : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
  tendsto_atTop_mono (fun k => by simp only [id]; omega) tendsto_id

/-- `k ↦ 2k + 1` tends to infinity. -/
theorem tendsto_nat_two_mul_add_one_atTop : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
  tendsto_atTop_mono (fun k => by simp only [id]; omega) tendsto_id

/-- Interleaving two shrinking families gives a shrinking family. -/
theorem LoopsShrinkTo.interleave {y : Y} {γ₀ γ₁ : ℕ → Path y y} (h₀ : LoopsShrinkTo y γ₀)
    (h₁ : LoopsShrinkTo y γ₁) : LoopsShrinkTo y (Peano.interleaveSeq γ₀ γ₁) := by
  intro U hU
  have hd : Tendsto (fun k : ℕ => k / 2) atTop atTop := Nat.tendsto_div_const_atTop two_ne_zero
  filter_upwards [hd.eventually (h₀ U hU), hd.eventually (h₁ U hU)] with k hk₀ hk₁
  unfold Peano.interleaveSeq
  split_ifs
  · exact hk₀
  · exact hk₁

/-! ### Extensionality and composition -/

/-- Two maps from the earring that agree on every loop `ℓₖ` are equal (both are the glued map of
the loops of `g`, by uniqueness in the gluing lemma). -/
theorem earring_ext {f g : C(earring, Y)} (h : ∀ k t, f (earringLoop k t) = g (earringLoop k t)) :
    f = g :=
  (earringMap_unique (loopsShrinkTo_map_earringLoop g) f h).trans
    (earringMap_unique (loopsShrinkTo_map_earringLoop g) g fun _ _ => rfl).symm

section earringMap

variable {y : Y} {γ : ℕ → Path y y} (h : LoopsShrinkTo y γ)

/-- Every map from the earring is the glued map of its own loops `f ∘ ℓₖ`. -/
theorem eq_earringMap (f : C(earring, Y)) :
    f = earringMap (f earringBase) (fun k => (earringLoop k).map f.continuous)
      (loopsShrinkTo_map_earringLoop f) :=
  earringMap_unique _ f fun _ _ => rfl

/-- Post-composing a glued map with `g` glues the images of the loops under `g`. -/
theorem comp_earringMap (g : C(Y, Z)) :
    g.comp (earringMap y γ h) =
      earringMap (g y) (fun k => (γ k).map g.continuous) (h.map g) :=
  earringMap_unique _ _ fun k t => by simp

/-- Precomposing a glued map with the sub-earring map `earringSub ν` glues the subfamily
`γ ∘ ν`. -/
theorem earringMap_comp_earringSub {ν : ℕ → ℕ} (hν : Tendsto ν atTop atTop) :
    (earringMap y γ h).comp (earringSub ν hν) =
      earringMap y (fun k => γ (ν k)) (h.comp_tendsto hν) :=
  earringMap_unique _ _ fun k t => by simp

/-- **Full essentiality of a glued map**: `earringMap y γ h` is fully essential iff no `γ k` is
null-homotopic. -/
theorem fullyEssential_earringMap_iff :
    FullyEssential (earringMap y γ h) ↔ ∀ k, ¬ (γ k).Homotopic (Path.refl y) := by
  refine forall_congr' fun k => not_congr ?_
  rw [earringLoop_map_earringMap, cast_homotopic_refl_iff]

end earringMap

/-! ### Interleaving two maps from the earring -/

/-- The interleaving of two maps `f₀ f₁ : 𝔼 → Y` with `f₀ b₀ = f₁ b₀`: the map sending the even
loop `ℓ_{2k}` to `f₀ ∘ ℓₖ` and the odd loop `ℓ_{2k+1}` to `f₁ ∘ ℓₖ`, based at `f₀ b₀`. -/
def earringInterleave (f₀ f₁ : C(earring, Y)) (h : f₀ earringBase = f₁ earringBase) :
    C(earring, Y) :=
  earringMap (f₀ earringBase)
    (interleaveSeq (fun k => (earringLoop k).map f₀.continuous)
      (fun k => ((earringLoop k).map f₁.continuous).cast h h))
    ((loopsShrinkTo_map_earringLoop f₀).interleave ((loopsShrinkTo_map_earringLoop f₁).cast h))

section earringInterleave

variable (f₀ f₁ : C(earring, Y)) (h : f₀ earringBase = f₁ earringBase)

/-- The interleaved map sends the base point to `f₀ b₀`. -/
@[simp] theorem earringInterleave_base : earringInterleave f₀ f₁ h earringBase = f₀ earringBase :=
  earringMap_base _

/-- The interleaved map on an even loop. -/
@[simp] theorem earringInterleave_earringLoop_two_mul (k : ℕ) (t : I) :
    earringInterleave f₀ f₁ h (earringLoop (2 * k) t) = f₀ (earringLoop k t) := by
  simp [earringInterleave]

/-- The interleaved map on an odd loop. -/
@[simp] theorem earringInterleave_earringLoop_two_mul_add_one (k : ℕ) (t : I) :
    earringInterleave f₀ f₁ h (earringLoop (2 * k + 1) t) = f₁ (earringLoop k t) := by
  simp [earringInterleave]

/-- The even loops of the interleaved map are the loops of `f₀` (up to the cast of the base
point). -/
theorem earringLoop_map_earringInterleave_two_mul (k : ℕ) :
    (earringLoop (2 * k)).map (earringInterleave f₀ f₁ h).continuous =
      ((earringLoop k).map f₀.continuous).cast (earringInterleave_base f₀ f₁ h)
        (earringInterleave_base f₀ f₁ h) := by
  ext t
  simp

/-- The odd loops of the interleaved map are the loops of `f₁` (up to the cast of the base
point). -/
theorem earringLoop_map_earringInterleave_two_mul_add_one (k : ℕ) :
    (earringLoop (2 * k + 1)).map (earringInterleave f₀ f₁ h).continuous =
      ((earringLoop k).map f₁.continuous).cast ((earringInterleave_base f₀ f₁ h).trans h)
        ((earringInterleave_base f₀ f₁ h).trans h) := by
  ext t
  simp

/-- The interleaved map restricted to the even sub-earring is `f₀`. -/
theorem earringInterleave_comp_two_mul :
    (earringInterleave f₀ f₁ h).comp (earringSub (fun k => 2 * k) tendsto_nat_two_mul_atTop) =
      f₀ :=
  earring_ext fun k t => by simp

/-- The interleaved map restricted to the odd sub-earring is `f₁`. -/
theorem earringInterleave_comp_two_mul_add_one :
    (earringInterleave f₀ f₁ h).comp
        (earringSub (fun k => 2 * k + 1) tendsto_nat_two_mul_add_one_atTop) = f₁ :=
  earring_ext fun k t => by simp

end earringInterleave

/-! ### `FundamentalGroup.mapOfEq` -/

/-- `FundamentalGroup.mapOfEq f h` on the class of a loop `γ` is the class of the cast of
`f ∘ γ`. -/
theorem fundamentalGroup_mapOfEq_fromPath (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (γ : Path x x) :
    FundamentalGroup.mapOfEq f h (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦(γ.map f.continuous).cast h.symm h.symm⟧ := by
  rw [FundamentalGroup.mapOfEq_apply]
  ext
  simp [Path.Homotopic.Quotient.mk_map]

end Peano
