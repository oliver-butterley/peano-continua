module

public import Peano.Defs

/-!
# Reduced paths and 0-forms (Definitions 2.6 and 3.1)

Definitions needed to state the cited inputs of Part A of Brazas–Pavešić (arXiv:2610.35875):
Cannon–Conner's reduced representatives (Remark 2.7) and Eda's zero-form lemma (Lemma 3.2).

* **Subpaths.** `subpathMap β a b : C(I, X)` is `β` restricted to `[a, b]` and rescaled linearly
  to `I` (`s ↦ β (a + s (b - a))`); for `a > b` it runs backwards, which is never used.
* **Reduced path** (Definition 2.6, with the repair of `notes/checks/A.md`, A-2.6-1: the interval
  must be non-degenerate, otherwise no non-constant path would be reduced). `β` is reduced if it is
  constant, or no subpath on `[a, b]` with `a < b` and `β a = β b` is null-homotopic rel `{0, 1}`.
* **Reparametrisation.** `IsReparam f g`: `f = g ∘ h` for an increasing homeomorphism `h` of `I`.
* **0-form** (Definition 3.1, in the form used by Lemma 3.2). The paper asks for a 0-form whose
  concatenation is a reduced representative of a loop. Rather than concatenating a list of paths
  (whose parametrisation the paper never fixes), `IsZeroFormCut ρ` says that the path `ρ` can be cut
  at parameters `0 = t₀ < t₁ < ⋯ < t_{m} = 1` into non-constant pieces, paired by a fixed-point-free
  involution `τ` of the pieces, each piece equal to the reverse of its partner up to an increasing
  reparametrisation (the convention `≡` recommended in `notes/checks/A.md`, A-3.1-1). The pieces of
  a reduced path are reduced, so this is Definition 3.1 for the pieces of `ρ`.
-/

@[expose] public section

open Set Topology unitInterval

noncomputable section

namespace Peano

variable {X : Type*} [TopologicalSpace X]

/-- The affine map `s ↦ a + s (b - a)` from `I` to `I`, running from `a` to `b`. Its values lie
between `a` and `b` (in `[a, b]` for `a ≤ b`; for `a > b` it runs backwards, with values in
`[b, a]`), so they always lie in `I` and the projection `Set.projIcc` onto `I`, needed only to type
the map, never clamps anything. -/
def affineI (a b : I) : C(I, I) where
  toFun s := Set.projIcc 0 1 zero_le_one ((a : ℝ) + s * ((b : ℝ) - a))
  continuous_toFun := continuous_projIcc.comp (by fun_prop)

/-- The subpath of `β : C(I, X)` on `[a, b]`, rescaled to `I`. -/
def subpathMap (β : C(I, X)) (a b : I) : C(I, X) := β.comp (affineI a b)

/-- **Definition 2.6** (reduced path), with a non-degenerate interval: `β` is constant, or there
is no `a < b` with `β a = β b` such that `β|[a, b]` is null-homotopic relative to its end points. -/
def IsReducedPath {x y : X} (β : Path x y) : Prop :=
  (∀ t, β t = x) ∨ ∀ a b : I, a < b → β a = β b →
    ¬ (subpathMap (β : C(I, X)) a b).HomotopicRel (ContinuousMap.const I (β a)) {0, 1}

/-- `f` is a reparametrisation of `g` by an increasing homeomorphism of `I`. -/
def IsReparam (f g : C(I, X)) : Prop :=
  ∃ h : I ≃ₜ I, StrictMono h ∧ ∀ s, f s = g (h s)

/-- **0-form** (Definition 3.1, for the pieces of one path): `ρ` can be cut at
`0 = t 0 < t 1 < ⋯ < t m = 1` (`m ≥ 1`) into non-constant pieces `ρ|[t i, t (i+1)]`, paired by a
fixed-point-free involution `τ`, each piece a reparametrisation of the reverse of its partner. -/
def IsZeroFormCut (ρ : C(I, X)) : Prop :=
  ∃ (m : ℕ) (t : Fin (m + 2) → I) (τ : Fin (m + 1) → Fin (m + 1)),
    StrictMono t ∧ t 0 = 0 ∧ t (Fin.last _) = 1 ∧ (∀ i, τ (τ i) = i) ∧ (∀ i, τ i ≠ i) ∧
    (∀ i : Fin (m + 1), ∃ s₁ s₂, subpathMap ρ (t i.castSucc) (t i.succ) s₁ ≠
      subpathMap ρ (t i.castSucc) (t i.succ) s₂) ∧
    ∀ i : Fin (m + 1), IsReparam (subpathMap ρ (t (τ i).castSucc) (t (τ i).succ))
      ((subpathMap ρ (t i.castSucc) (t i.succ)).comp ⟨σ, continuous_symm⟩)

end Peano
