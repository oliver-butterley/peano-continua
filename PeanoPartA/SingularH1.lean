module

public import PeanoPartA.Homology
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Naturality

/-!
# Genuine singular `H₁` and the class of a loop (bridge to Tau Ceti's Hurewicz theorem)

Part A of Brazas–Pavešić (arXiv:2610.35875) works with the first singular homology group
`H₁(X) = H₁(X; ℤ)`. The engine of the formalisation (`PeanoPartA.Homology`, `PeanoPartA.Lemmas`)
works with the abelianised fundamental group: "`[α]_h = 0`" is
`FundamentalGroup.fromPath ⟦α⟧ ∈ commutator (FundamentalGroup X x)`, and `IsHomologous`,
`homologyClass` live in `Additive (Abelianization (FundamentalGroup X x))`. This file connects that
model to genuine singular homology, through the degree-one Hurewicz theorem of Tau Ceti
(`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv : π₁(X, x)^ab ≃+ H₁(X; ℤ)` for path-connected `X`).

## Encoding

* **`H₁`.** `Peano.singularH1 X` is `((TauCeti.singularChains ℤ).obj (TopCat.of X)).homology 1`:
  the homology in degree `1` of Mathlib's singular chain complex
  (`singularChainComplexFunctor (ModuleCat ℤ)` evaluated at `ℤ`) of `X`, an object of
  `ModuleCat ℤ`. This is Mathlib's singular homology; Tau Ceti only supplies the element-level
  interface and the Hurewicz theorem. Spaces are `X : Type` (universe `0`), as everywhere in
  Part A.
* **Class of a loop.** `Peano.h1Class γ` is the class of the singular `1`-cycle of a loop `γ`
  (Tau Ceti's `loopClass`, transported along `H₁AddEquivHomology` from the explicit
  cycles-mod-boundaries model to the homology of the complex). It needs no base point and no
  path-connectedness.
* **Induced maps.** A continuous map `g : C(X, Y)` acts by `ContinuousMap.singularHomologyMap ℤ 1 g`
  (`homologyMap` of the induced chain map), and sends `h1Class γ` to `h1Class (γ.map _)`
  (`singularHomologyMap_h1Class`). For a subspace `A ⊆ X` the map `H₁(A) → H₁(X)` is
  `singularHomologyMap ℤ 1 ⟨Subtype.val, continuous_subtype_val⟩`.

## The bridge

* `h1Class_eq_zero_of_mem_commutator` (any space): a loop in the commutator subgroup has class `0`.
* `h1Class_eq_zero_iff` (path-connected `X`): `h1Class γ = 0 ↔ fromPath ⟦γ⟧ ∈ commutator`.
* `hurewiczHomologyAddEquiv_homologyClass`: the Hurewicz isomorphism sends Part A's
  `homologyClass x γ` to `h1Class γ`; hence `homologyClass` is genuine singular homology, read in
  `π₁(X, x)^ab`.
* `isHomologous_iff_h1Class_eq` (path-connected `X`): `IsHomologous α β ↔ h1Class α = h1Class β`.
* Algebra of classes: `h1Class_refl`, `h1Class_trans`, `h1Class_symm`, `h1Class_conj`
  (independence of base point), `h1Class_eq_of_homotopic`.
-/

@[expose] public section

open CategoryTheory TauCeti TauCeti.HurewiczOne

noncomputable section

namespace Peano

/-- The first singular homology group `H₁(X; ℤ)` of a space `X : Type`, the homology in degree `1`
of Mathlib's singular chain complex of `X` with integer coefficients (as an object of
`ModuleCat ℤ`). -/
abbrev singularH1 (X : Type) [TopologicalSpace X] : ModuleCat ℤ :=
  ((singularChains ℤ).obj (TopCat.of X)).homology 1

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The class `[γ]_h ∈ H₁(X; ℤ)` of a loop `γ`: the homology class of its singular `1`-cycle. -/
def h1Class {x : X} (γ : Path x x) : singularH1 X :=
  H₁AddEquivHomology (TopCat.of X) (loopClass (X := TopCat.of X) γ)

/-- The class of a loop, unfolded to Tau Ceti's `loopClass`. -/
theorem h1Class_def {x : X} (γ : Path x x) :
    h1Class γ = H₁AddEquivHomology (TopCat.of X) (loopClass (X := TopCat.of X) γ) := rfl

/-- **Naturality**: the map induced on `H₁` by a continuous map sends the class of a loop to the
class of its image. -/
theorem singularHomologyMap_h1Class (g : C(X, Y)) {x : X} (γ : Path x x) :
    ContinuousMap.singularHomologyMap ℤ 1 g (h1Class γ) = h1Class (γ.map g.continuous) :=
  ContinuousMap.singularHomologyMap_loopClass g γ

/-- Loops with the same values have the same class. -/
theorem h1Class_eq_of_apply_eq {x y : X} (γ : Path x x) (δ : Path y y) (h : ∀ t, γ t = δ t) :
    h1Class γ = h1Class δ := by
  rw [h1Class, h1Class, loopClass_eq_of_apply_eq (X := TopCat.of X) γ δ h]

/-- The constant loop has class `0`. -/
@[simp]
theorem h1Class_refl (x : X) : h1Class (Path.refl x) = 0 := by
  rw [h1Class, loopClass_refl (X := TopCat.of X), map_zero]

/-- The class of a concatenation of loops is the sum of the classes. -/
theorem h1Class_trans {x : X} (γ δ : Path x x) :
    h1Class (γ.trans δ) = h1Class γ + h1Class δ := by
  rw [h1Class, loopClass_trans (X := TopCat.of X), map_add]
  rfl

/-- The class of a loop through Tau Ceti's Hurewicz map `hurewicz₁` (no path-connectedness). -/
private theorem h1Class_eq_hurewicz₁ {x : X} (γ : Path x x) :
    h1Class γ = H₁AddEquivHomology (TopCat.of X) (Multiplicative.toAdd
      (hurewicz₁ (TopCat.of X) x (FundamentalGroup.fromPath ⟦γ⟧))) := by
  rw [h1Class]
  congr 1
  exact (congrArg Multiplicative.toAdd (hurewicz₁_mk (X := TopCat.of X) γ)).symm

/-- Homotopic loops have the same class. -/
theorem h1Class_eq_of_homotopic {x : X} {γ δ : Path x x} (h : γ.Homotopic δ) :
    h1Class γ = h1Class δ := by
  rw [h1Class_eq_hurewicz₁, h1Class_eq_hurewicz₁,
    show (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦δ⟧ from Quotient.sound h]

/-- The reversed loop has the negative class. -/
theorem h1Class_symm {x : X} (γ : Path x x) : h1Class γ.symm = -h1Class γ := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← h1Class_trans,
    ← h1Class_eq_of_homotopic ⟨Path.Homotopy.reflTransSymm γ⟩, h1Class_refl]

/-- **Independence of the base point**: the conjugate `p γ p⁻¹` of a loop `γ` by a path `p` has
the same class as `γ`. -/
theorem h1Class_conj {x y : X} (p : Path x y) (γ : Path y y) :
    h1Class ((p.trans γ).trans p.symm) = h1Class γ := by
  rw [h1Class_eq_hurewicz₁, h1Class_eq_hurewicz₁,
    ← hurewicz₁_fundamentalGroupMulEquivOfPath (X := TopCat.of X) p.symm]
  congr 3
  rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  show _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _)
  simp only [Path.symm_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  congr 1
  show Path.Homotopic.Quotient.mk _ = _
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

/-- A loop whose class in `π₁` lies in the commutator subgroup has class `0` in `H₁` (any
space). -/
theorem h1Class_eq_zero_of_mem_commutator {x : X} (γ : Path x x)
    (h : FundamentalGroup.fromPath ⟦γ⟧ ∈ commutator (FundamentalGroup X x)) :
    h1Class γ = 0 := by
  rw [mem_commutator_iff_abelianization_of_eq_one] at h
  have := hurewiczAb_ofMul_of_mk (X := TopCat.of X) x γ
  rw [h1Class, ← this]
  have h' : (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk γ))) : Additive (Abelianization (FundamentalGroup X x))) = 0 :=
    congrArg Additive.ofMul h
  exact (congrArg (fun a => H₁AddEquivHomology (TopCat.of X) (hurewiczAb (X := TopCat.of X) x a))
    h').trans (by rw [map_zero, map_zero])

/-- In a path-connected space the Hurewicz isomorphism sends the abelianised class of a loop at
the base point to its class in `H₁`. -/
theorem hurewiczHomologyAddEquiv_ofMul_of_fromPath [PathConnectedSpace X] {x : X}
    (γ : Path x x) :
    hurewiczHomologyAddEquiv (X := TopCat.of X) x
      (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath ⟦γ⟧))) = h1Class γ :=
  hurewiczHomologyAddEquiv_ofMul_of_mk (X := TopCat.of X) γ

/-- **Bridge**: in a path-connected space, the Hurewicz isomorphism `π₁(X, x)^ab ≃+ H₁(X; ℤ)`
sends Part A's homology class `homologyClass x γ` of a loop `γ` (at any point) to its genuine
singular homology class `h1Class γ`. -/
theorem hurewiczHomologyAddEquiv_homologyClass [PathConnectedSpace X] (x : X) {y : X}
    (γ : Path y y) :
    hurewiczHomologyAddEquiv (X := TopCat.of X) x (homologyClass x γ) = h1Class γ := by
  rw [homologyClass_eq x (PathConnectedSpace.somePath x y),
    show (Path.Homotopic.Quotient.mk _ : Path.Homotopic.Quotient x x) = ⟦_⟧ from rfl,
    hurewiczHomologyAddEquiv_ofMul_of_fromPath, h1Class_conj]

/-- **Bridge**: in a path-connected space, a loop has class `0` in `H₁(X; ℤ)` iff its class in
`π₁` lies in the commutator subgroup (the abelianisation model of `[γ]_h = 0`). -/
theorem h1Class_eq_zero_iff [PathConnectedSpace X] {x : X} (γ : Path x x) :
    h1Class γ = 0 ↔ FundamentalGroup.fromPath ⟦γ⟧ ∈ commutator (FundamentalGroup X x) := by
  rw [← homologyClass_eq_zero_iff x, ← hurewiczHomologyAddEquiv_homologyClass x,
    AddEquiv.map_eq_zero_iff]

/-- **Bridge**: in a path-connected space, Part A's `homologyClass` agrees iff the singular
classes agree. -/
theorem homologyClass_eq_iff_h1Class_eq [PathConnectedSpace X] (x : X) {x₀ x₁ : X}
    (α : Path x₀ x₀) (β : Path x₁ x₁) :
    homologyClass x α = homologyClass x β ↔ h1Class α = h1Class β := by
  rw [← hurewiczHomologyAddEquiv_homologyClass x, ← hurewiczHomologyAddEquiv_homologyClass x,
    EmbeddingLike.apply_eq_iff_eq]

/-- **Bridge**: in a path-connected space, two loops are homologous (`IsHomologous`, the
abelianisation model) iff they have the same class in `H₁(X; ℤ)`. -/
theorem isHomologous_iff_h1Class_eq [PathConnectedSpace X] {x₀ x₁ : X} (α : Path x₀ x₀)
    (β : Path x₁ x₁) : IsHomologous α β ↔ h1Class α = h1Class β := by
  rw [isHomologous_iff_homologyClass_eq x₀, homologyClass_eq_iff_h1Class_eq]

end Peano
