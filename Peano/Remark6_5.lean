module

public import Peano.Sanity

/-!
# Remark 6.5: the injection of Lemma 6.4 need not be a bijection

Brazas–Pavešić (arXiv:2610.35875), Remark 6.5. Lemma 6.4 (`Peano.injOn_wildSet`) says that a map
`f : X → Y` from a one-dimensional Peano continuum inducing bijections on all fundamental groups
restricts to an injection `w(X) → w(Y)`. This injection need not be surjective when `Y` is not
one-dimensional: for the earring `𝔼` and `Y = 𝔼 × I`,

* the inclusion `ι : 𝔼 → 𝔼 × I`, `x ↦ (x, 0)`, is a homotopy equivalence (with homotopy inverse
  the projection; `earringProdHomotopyEquiv`), hence a weak homotopy equivalence and bijective on
  all fundamental groups;
* every `(b₀, t)` is a wild point of `𝔼 × I` (`mk_earringBase_mem_wildSet_prod`): the map
  `x ↦ (x, t)` is fully essential, since composed with the projection it is the identity of `𝔼`,
  which is fully essential;
* so `ι` maps `w(𝔼) = {b₀}` (`Peano.Sanity.wildSet_earring`) onto `{(b₀, 0)}`, a proper subset of
  `w(𝔼 × I)` (`not_surjOn_wildSet_earringProdHomotopyEquiv`), and `w(𝔼 × I)` is even uncountable
  (`not_countable_wildSet_earring_prod`).

A further comment (not in the paper's remark; `notes/checks/D.md` notes the example is
Brazas–Fischer's
Remark 9.16): one-dimensionality of *both* spaces matters in Brazas–Fischer,
Theorem 9.15 (`Peano.nonempty_homeomorph_loopWildSet`, proved in `Peano.BrazasFischer`: homotopy
equivalent
one-dimensional Peano continua have homeomorphic wild sets): `𝔼` and `𝔼 × I` are homotopy
equivalent Peano continua whose wild sets are not even equinumerous. (That `𝔼 × I` is a Peano
continuum of dimension `2` is not formalised: Mathlib has neither products of locally
path-connected spaces as an instance nor covering dimension.)

All statements here use only the standard axioms.
-/

@[expose] public section

open Set Topology unitInterval

noncomputable section

namespace Peano.Remark6_5

/-- The slice `𝔼 → 𝔼 × I`, `x ↦ (x, t)`. -/
def earringSlice (t : I) : C(earring, earring × I) :=
  ⟨fun x => (x, t), by fun_prop⟩

/-- The deformation `(s, (x, t)) ↦ (x, s t)` of `𝔼 × I` onto `𝔼 × {0}`. -/
def prodDeformation :
    ContinuousMap.Homotopy ((earringSlice 0).comp ContinuousMap.fst)
      (ContinuousMap.id (earring × I)) where
  toFun p := (p.2.1, p.1 * p.2.2)
  continuous_toFun := by fun_prop
  map_zero_left p := by simp [earringSlice]
  map_one_left p := by simp

/-- **The inclusion `𝔼 → 𝔼 × I`, `x ↦ (x, 0)`, is a homotopy equivalence**, with homotopy inverse
the projection. -/
def earringProdHomotopyEquiv : ContinuousMap.HomotopyEquiv earring (earring × I) where
  toFun := earringSlice 0
  invFun := ContinuousMap.fst
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨prodDeformation⟩

/-- `earringProdHomotopyEquiv` is `x ↦ (x, 0)`. -/
@[simp] theorem earringProdHomotopyEquiv_apply (x : earring) :
    earringProdHomotopyEquiv x = (x, 0) :=
  rfl

/-- The inclusion `𝔼 → 𝔼 × I` is a weak homotopy equivalence (so Lemma 6.4 applies to it). -/
theorem isWeakHomotopyEquivalence_earringProdHomotopyEquiv :
    IsWeakHomotopyEquivalence earringProdHomotopyEquiv.toFun :=
  HomotopyEquiv.isWeakHomotopyEquivalence _

/-- Every slice `x ↦ (x, t)` is fully essential: composed with the projection it is the identity
of the earring. -/
theorem fullyEssential_earringSlice (t : I) : FullyEssential (earringSlice t) := fun k =>
  not_homotopic_refl_of_map ContinuousMap.fst (fullyEssential_id k)

/-- **Every `(b₀, t)` is a wild point of `𝔼 × I`.** -/
theorem mk_earringBase_mem_wildSet_prod (t : I) : (earringBase, t) ∈ wildSet (earring × I) :=
  ⟨earringSlice t, rfl, fullyEssential_earringSlice t⟩

/-- `{b₀} × I ⊆ w(𝔼 × I)`. -/
theorem singleton_prod_subset_wildSet : {earringBase} ×ˢ univ ⊆ wildSet (earring × I) := by
  rintro ⟨x, t⟩ ⟨hx, -⟩
  obtain rfl : x = earringBase := hx
  exact mk_earringBase_mem_wildSet_prod t

/-- **Remark 6.5.** The inclusion `𝔼 → 𝔼 × I` (a homotopy equivalence) does not map `w(𝔼)` onto
`w(𝔼 × I)`: the injection of Lemma 6.4 need not be a bijection. -/
theorem not_surjOn_wildSet_earringProdHomotopyEquiv :
    ¬ SurjOn earringProdHomotopyEquiv (wildSet earring) (wildSet (earring × I)) := by
  intro h
  obtain ⟨x, hx, hx1⟩ := h (mk_earringBase_mem_wildSet_prod 1)
  rw [earringProdHomotopyEquiv_apply, Prod.ext_iff] at hx1
  exact zero_ne_one hx1.2

/-- **The wild set of `𝔼 × I` is uncountable** (it contains `{b₀} × I`), whereas `w(𝔼) = {b₀}`;
hence the homotopy equivalent spaces `𝔼` and `𝔼 × I` do not have homeomorphic wild sets. -/
theorem not_countable_wildSet_earring_prod : ¬ (wildSet (earring × I)).Countable := by
  intro hc
  have : Countable (wildSet (earring × I)) := hc.to_subtype
  have hI : Countable I :=
    Function.Injective.countable (f := fun t : I =>
      (⟨(earringBase, t), mk_earringBase_mem_wildSet_prod t⟩ : wildSet (earring × I)))
      fun s t hst => (Prod.ext_iff.1 (Subtype.ext_iff.1 hst)).2
  have h2 := Cardinal.mk_le_aleph0 (α := I)
  rw [show Cardinal.mk I = Cardinal.mk (Icc (0 : ℝ) 1) from rfl,
    Cardinal.mk_Icc_real (zero_lt_one' ℝ)] at h2
  exact not_le.2 Cardinal.aleph0_lt_continuum h2

/-- **Remark 6.5**, summary: the inclusion `ι : 𝔼 → 𝔼 × I`, `x ↦ (x, 0)`, is a homotopy
equivalence, `w(𝔼) = {b₀}`, but `w(𝔼 × I)` contains `{b₀} × I`, is uncountable, and is not the
image of `w(𝔼)` under `ι`. -/
theorem remark6_5 :
    (∀ x, earringProdHomotopyEquiv x = (x, 0)) ∧ wildSet earring = {earringBase} ∧
      {earringBase} ×ˢ univ ⊆ wildSet (earring × I) ∧
      ¬ SurjOn earringProdHomotopyEquiv (wildSet earring) (wildSet (earring × I)) ∧
      ¬ (wildSet (earring × I)).Countable :=
  ⟨earringProdHomotopyEquiv_apply, Sanity.wildSet_earring, singleton_prod_subset_wildSet,
    not_surjOn_wildSet_earringProdHomotopyEquiv, not_countable_wildSet_earring_prod⟩

end Peano.Remark6_5
