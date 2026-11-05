module

public import PeanoPartA.Reduced
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Topology.Subpath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Convex.PathConnected

/-!
# First homology through the abelianised fundamental group; 0-forms are null-homologous

Infrastructure for Part A (§3) of Brazas–Pavešić (arXiv:2610.35875).

* **Homology model.** The paper's `H₁` is first singular homology with integer coefficients. It is
  formalised as such in `PeanoPartA.SingularH1` (`Peano.singularH1`, the class `Peano.h1Class` of a
  loop), through Tau Ceti's degree-one Hurewicz theorem `π₁(X, x)^ab ≃+ H₁(X; ℤ)`; the Part A
  lemmas are restated there with genuine singular homology (`PeanoPartA.SingularH1Lemmas`). The
  *working model* of the proofs, set up in this file, is the abelianised fundamental group:
  "`[α]_h = 0`" for a loop `α` at `x` is
  `FundamentalGroup.fromPath ⟦α⟧ ∈ commutator (FundamentalGroup X x)`, equivalently
  `Abelianization.of (fromPath ⟦α⟧) = 1` (`mem_commutator_iff_abelianization_of_eq_one`), and
  agrees with `h1Class α = 0` for path-connected `X` (`Peano.h1Class_eq_zero_iff`); this is also
  the form in which the cited axiom `Peano.eda_zeroForm` is stated.
* **Different base points.** Loops `α` at `x₀` and `β` at `x₁` are `IsHomologous` if, for some path
  `p : x₀ → x₁`, `α` and the conjugate `p β p⁻¹` have the same image in the abelianisation at `x₀`.
  The choice of `p` does not matter (`abelianization_of_conj_eq`): two choices differ by
  conjugation by a loop at `x₀`, which is invisible in the abelian quotient
  (`IsHomologous.forall`). The relation is reflexive, symmetric and transitive
  (`IsHomologous.refl`, `.symm`, `.trans`). It is `False` for base points in different path
  components (there is no path `p`), unlike equality of classes in singular `H₁`; every use is in a
  path-connected space, where it is equality of homology classes in `H₁(X)`
  (`isHomologous_iff_homologyClass_eq`; in singular `H₁`, `Peano.isHomologous_iff_h1Class_eq`).
  Conjugation `p γ p⁻¹` is Mathlib's change of base point
  `fundamentalGroupMulEquivOfPath p⁻¹` (`fundamentalGroupMulEquivOfPath_symm_fromPath`), a group
  isomorphism, so it preserves and reflects membership in the commutator subgroup
  (`conj_mem_commutator_iff`).
* **Order of multiplication.** Mathlib's `FundamentalGroup` multiplies in the *reverse* order of
  concatenation: `fromPath (P.trans Q) = fromPath Q * fromPath P`
  (`fundamentalGroup_fromPath_trans`, by `rfl`). Nothing here depends on this: the commutator
  subgroup and the abelianisation are invariant under passing to the opposite group, and all
  computations below happen in the abelianisation.
* **The abelian line integral** `PeanoPartA.Homology.abLine x`, in a path-connected space: fixing a
path
  `c u` from the base point `x` to every point `u` (`PathConnectedSpace.somePath`), a path class
  `P : u → v` is sent to the class of `c u · P · (c v)⁻¹` in the abelianisation. It is
  multiplicative under concatenation (`abLine_trans`), inverts under reversal (`abLine_symm`), is a
  homotopy invariant (it is defined on classes), and on loops at `x` it is the abelianisation map
  (`abLine_loop`).
* **Homology class of a loop.** `homologyClass x γ ∈ Additive (π₁(X, x)^ab)` is the line integral
  of a loop `γ` at any point, written additively; it may be computed with any connecting path
  (`homologyClass_eq`), vanishes iff `γ` is null-homologous (`homologyClass_eq_zero_iff`), is
  additive (`homologyClass_trans_conj`, `homologyClass_symm`), and two loops are homologous iff
  their classes agree (`isHomologous_iff_homologyClass_eq`). The Hurewicz isomorphism sends it to
  the singular class `h1Class γ` (`Peano.hurewiczHomologyAddEquiv_homologyClass`).
* **0-forms are null-homologous in any space** (`fromPath_mem_commutator_of_isZeroFormCut`; the
  direction of Lemma 3.2 that the paper uses as "obvious", see `notes/checks/A.md`, A-3.1).
  First in a path-connected space: the line integral is invariant under increasing
  reparametrisation. Splitting a loop `ρ` at the cut points `t i` of the 0-form, Mathlib's
  `Path.subpath` gives the telescoping identity `∏ abLine (ρ|[tᵢ, tᵢ₊₁]) = abLine ρ`, and the
  pairing `τ` makes the product `1` (`Finset.prod_ninvolution`). For a general space, the loop is
  first moved into its own image, which is path-connected, and the result pushed forward along the
  inclusion.
* **Paths in subspaces.** `Peano.pathIn γ S h` is a path `γ` whose values lie in `S`, as a path in
  the subtype `S`; `Peano.homotopic_of_map_mem` builds a homotopy in `S` from a homotopy in `X`
  whose values lie in `S`.

The pieces of a 0-form are given by `Peano.subpathMap` (`PeanoPartA.Reduced`), which agrees
pointwise
with Mathlib's `Path.subpath` (`subpathMap_apply_eq_subpath`).
-/

@[expose] public section

open Set Topology unitInterval

noncomputable section

namespace Peano

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The unit interval is path-connected (it is convex). Mathlib has no such instance; it is used
through `isPathConnected_range`, to see that the image of a path is path-connected. -/
instance pathConnectedSpace_unitInterval : PathConnectedSpace I :=
  isPathConnected_iff_pathConnectedSpace.1
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, left_mem_Icc.2 zero_le_one⟩)

/-! ### Commutator subgroups and the abelianisation -/

/-- An element lies in the commutator subgroup iff it maps to `1` in the abelianisation. -/
theorem mem_commutator_iff_abelianization_of_eq_one {G : Type*} [Group G] (g : G) :
    g ∈ commutator G ↔ Abelianization.of g = 1 := by
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]

/-- A group homomorphism maps commutator subgroup elements to commutator subgroup elements. -/
theorem monoidHom_map_mem_commutator {G H : Type*} [Group G] [Group H] (f : G →* H) {g : G}
    (hg : g ∈ commutator G) : f g ∈ commutator H := by
  rw [mem_commutator_iff_abelianization_of_eq_one] at hg ⊢
  rw [← Abelianization.map_of, hg, map_one]

/-- A group isomorphism preserves and reflects membership in the commutator subgroup. -/
theorem mulEquiv_map_mem_commutator_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) {g : G} :
    e g ∈ commutator H ↔ g ∈ commutator G := by
  refine ⟨fun h => ?_, fun h => monoidHom_map_mem_commutator e.toMonoidHom h⟩
  simpa using monoidHom_map_mem_commutator e.symm.toMonoidHom h

/-! ### Fundamental group: products and changes of base point -/

/-- Mathlib's fundamental group multiplies in the reverse order of concatenation. -/
theorem fundamentalGroup_fromPath_trans {x : X} (P Q : Path.Homotopic.Quotient x x) :
    FundamentalGroup.fromPath (P.trans Q) =
      FundamentalGroup.fromPath Q * FundamentalGroup.fromPath P := rfl

/-- The class of the reversed loop is the inverse. -/
theorem fundamentalGroup_fromPath_symm {x : X} (P : Path.Homotopic.Quotient x x) :
    FundamentalGroup.fromPath P.symm = (FundamentalGroup.fromPath P)⁻¹ := rfl

/-- The class of the constant loop is the identity. -/
theorem fundamentalGroup_fromPath_refl (x : X) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.refl x) = 1 := rfl

/-- Two loops with the same values (at a priori different base points) have the same
commutator-membership. -/
theorem fromPath_mem_commutator_congr {x y : X} (p : Path x x) (q : Path y y)
    (h : ∀ t, p t = q t) :
    FundamentalGroup.fromPath ⟦p⟧ ∈ commutator (FundamentalGroup X x) ↔
      FundamentalGroup.fromPath ⟦q⟧ ∈ commutator (FundamentalGroup X y) := by
  obtain rfl : x = y := by simpa using h 0
  obtain rfl : p = q := Path.ext (funext h)
  rfl

/-- Mathlib's change of base point along `p⁻¹`, for `p : x → y`, sends the class of a loop `γ`
at `y` to the class of the conjugate `p γ p⁻¹` at `x`. -/
theorem fundamentalGroupMulEquivOfPath_symm_fromPath {x y : X} (p : Path x y) (γ : Path y y) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p.symm (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦(p.trans γ).trans p.symm⟧ := by
  ext1
  simp [FundamentalGroup.fundamentalGroupMulEquivOfPath, CategoryTheory.Iso.conj_apply_asHom,
    FundamentalGroupoid.comp_eq]
  congr 1
  rw [← CategoryTheory.Groupoid.inv_eq_inv, ← Path.Homotopic.Quotient.mk_symm]
  show Path.Homotopic.Quotient.mk p.symm.symm = _
  rw [Path.symm_symm]

/-- Conjugating a loop `γ` at `y` by a path `p : x → y` does not change whether its class lies in
the commutator subgroup. -/
theorem conj_mem_commutator_iff {x y : X} (p : Path x y) (γ : Path y y) :
    FundamentalGroup.fromPath ⟦(p.trans γ).trans p.symm⟧ ∈ commutator (FundamentalGroup X x) ↔
      FundamentalGroup.fromPath ⟦γ⟧ ∈ commutator (FundamentalGroup X y) := by
  rw [← mulEquiv_map_mem_commutator_iff
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p.symm),
    fundamentalGroupMulEquivOfPath_symm_fromPath]

/-- Cancellation `P⁻¹ (P R) = R` in the fundamental groupoid. -/
private theorem quotient_symm_trans_cancel {x y z : X} (P : Path.Homotopic.Quotient x y)
    (R : Path.Homotopic.Quotient y z) : P.symm.trans (P.trans R) = R := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- In the abelianisation, conjugation by a loop is trivial. -/
theorem abelianization_of_conj_loop {x : X} (P Q : Path.Homotopic.Quotient x x) :
    Abelianization.of (FundamentalGroup.fromPath ((P.trans Q).trans P.symm)) =
      Abelianization.of (FundamentalGroup.fromPath Q) := by
  rw [fundamentalGroup_fromPath_trans, fundamentalGroup_fromPath_trans, map_mul, map_mul, mul_comm,
    mul_assoc, ← map_mul, ← fundamentalGroup_fromPath_trans, Path.Homotopic.Quotient.symm_trans,
    fundamentalGroup_fromPath_refl, map_one, mul_one]

/-- The image in the abelianisation of the conjugate `p β p⁻¹` of a loop `β` at `x₁` by a path
`p : x₀ → x₁` does not depend on `p`. -/
theorem abelianization_of_conj_eq {x₀ x₁ : X} (p q : Path x₀ x₁) (β : Path x₁ x₁) :
    Abelianization.of (FundamentalGroup.fromPath ⟦(p.trans β).trans p.symm⟧) =
      Abelianization.of (FundamentalGroup.fromPath ⟦(q.trans β).trans q.symm⟧) := by
  have : (Path.Homotopic.Quotient.mk ((q.trans β).trans q.symm)) =
      ((Path.Homotopic.Quotient.mk (q.trans p.symm)).trans
        (.mk ((p.trans β).trans p.symm))).trans
        (Path.Homotopic.Quotient.mk (q.trans p.symm)).symm := by
    rw [← Path.Homotopic.Quotient.mk_symm (q.trans p.symm), Path.trans_symm, Path.symm_symm]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc, quotient_symm_trans_cancel]
  exact ((congrArg (fun P => Abelianization.of (FundamentalGroup.fromPath P)) this).trans
    (abelianization_of_conj_loop _ _)).symm

/-- Conjugation by a path `p : x → y` respects equality of images in the abelianisation: if loops
`γ`, `δ` at `y` have the same image in `π₁(X, y)^ab`, then `p γ p⁻¹` and `p δ p⁻¹` have the same
image in `π₁(X, x)^ab`. -/
theorem abelianization_of_conj_congr {x y : X} (p : Path x y) {γ δ : Path y y}
    (h : Abelianization.of (FundamentalGroup.fromPath ⟦γ⟧) =
      Abelianization.of (FundamentalGroup.fromPath ⟦δ⟧)) :
    Abelianization.of (FundamentalGroup.fromPath ⟦(p.trans γ).trans p.symm⟧) =
      Abelianization.of (FundamentalGroup.fromPath ⟦(p.trans δ).trans p.symm⟧) := by
  have := congrArg (Abelianization.map
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p.symm).toMonoidHom) h
  simpa only [Abelianization.map_of, MulEquiv.coe_toMonoidHom,
    fundamentalGroupMulEquivOfPath_symm_fromPath] using this

/-! ### Homologous loops -/

/-- Loops `α` at `x₀` and `β` at `x₁` are *homologous*: for some path `p : x₀ → x₁`, `α` and
`p β p⁻¹` have the same image in the abelianisation of `π₁(X, x₀)` (by
`abelianization_of_conj_eq` the path does not matter). For path-connected `X` this is equality
of the classes `[α]_h = [β]_h` in `H₁(X) ≅ π₁(X, x₀)^ab` (`isHomologous_iff_homologyClass_eq`).
Unlike equality in singular `H₁`, the relation is `False` when `x₀` and `x₁` lie in different path
components; all uses are in path-connected spaces. -/
def IsHomologous {x₀ x₁ : X} (α : Path x₀ x₀) (β : Path x₁ x₁) : Prop :=
  ∃ p : Path x₀ x₁, Abelianization.of (FundamentalGroup.fromPath ⟦α⟧) =
    Abelianization.of (FundamentalGroup.fromPath ⟦(p.trans β).trans p.symm⟧)

/-- `IsHomologous α β` holds for one connecting path iff it holds for all of them. -/
theorem IsHomologous.forall {x₀ x₁ : X} {α : Path x₀ x₀} {β : Path x₁ x₁}
    (h : IsHomologous α β) (q : Path x₀ x₁) :
    Abelianization.of (FundamentalGroup.fromPath ⟦α⟧) =
      Abelianization.of (FundamentalGroup.fromPath ⟦(q.trans β).trans q.symm⟧) := by
  obtain ⟨p, hp⟩ := h
  rw [hp, abelianization_of_conj_eq p q]

/-- Two loops at the same point with the same image in the abelianisation are homologous. -/
theorem IsHomologous.of_abelianization_eq {x : X} {α β : Path x x}
    (h : Abelianization.of (FundamentalGroup.fromPath ⟦α⟧) =
      Abelianization.of (FundamentalGroup.fromPath ⟦β⟧)) : IsHomologous α β := by
  refine ⟨Path.refl x, h.trans ?_⟩
  congr 2
  show Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  rw [Path.refl_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]

/-- Being homologous is reflexive. -/
theorem IsHomologous.refl {x : X} (α : Path x x) : IsHomologous α α :=
  .of_abelianization_eq rfl

/-- The conjugate `p γ p⁻¹` of a loop `γ` by a path `p` is homologous to `γ`. -/
theorem isHomologous_conj {x y : X} (p : Path x y) (γ : Path y y) :
    IsHomologous ((p.trans γ).trans p.symm) γ :=
  ⟨p, rfl⟩

/-- Being homologous is symmetric. -/
theorem IsHomologous.symm {x₀ x₁ : X} {α : Path x₀ x₀} {β : Path x₁ x₁}
    (h : IsHomologous α β) : IsHomologous β α := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.symm, ?_⟩
  rw [abelianization_of_conj_congr p.symm hp]
  show Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)) =
    Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((p.symm.trans ((p.trans β).trans p.symm)).trans p.symm.symm)))
  rw [Path.symm_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, quotient_symm_trans_cancel,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]

/-- Being homologous is transitive. -/
theorem IsHomologous.trans {x₀ x₁ x₂ : X} {α : Path x₀ x₀} {β : Path x₁ x₁} {γ : Path x₂ x₂}
    (h₁ : IsHomologous α β) (h₂ : IsHomologous β γ) : IsHomologous α γ := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p.trans q, ?_⟩
  rw [hp, abelianization_of_conj_congr p hq]
  congr 2
  show Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm, Path.trans_symm,
    Path.Homotopic.Quotient.trans_assoc]

/-! ### Paths in subspaces -/

/-- A path whose values lie in `S`, as a path in the subtype `S`. -/
def pathIn {a b : X} (γ : Path a b) (S : Set X) (h : ∀ t, γ t ∈ S) :
    Path (⟨a, γ.source ▸ h 0⟩ : S) ⟨b, γ.target ▸ h 1⟩ where
  toFun t := ⟨γ t, h t⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

/-- The values of `pathIn γ S h` are those of `γ`. -/
@[simp] theorem pathIn_apply {a b : X} (γ : Path a b) (S : Set X) (h : ∀ t, γ t ∈ S) (t : I) :
    pathIn γ S h t = ⟨γ t, h t⟩ := rfl

/-- `pathIn γ S h` followed by the inclusion is `γ`. -/
@[simp] theorem pathIn_map_val {a b : X} (γ : Path a b) (S : Set X) (h : ∀ t, γ t ∈ S) :
    (pathIn γ S h).map continuous_subtype_val = γ := by
  ext; rfl

/-- A continuous map `I × I → X` with values in `S` that is a homotopy rel end points between the
images of two paths in `S` gives a homotopy in `S`. -/
theorem homotopic_of_map_mem {S : Set X} {a b : S}
    {p q : Path a b} (G : C(I × I, X)) (h0 : ∀ t, G (0, t) = p t) (h1 : ∀ t, G (1, t) = q t)
    (hs0 : ∀ s, G (s, 0) = a) (hs1 : ∀ s, G (s, 1) = b) (hS : ∀ z, G z ∈ S) :
    p.Homotopic q :=
  ⟨{ toFun := fun z => ⟨G z, hS z⟩
     continuous_toFun := by fun_prop
     map_zero_left := fun t => Subtype.ext (h0 t)
     map_one_left := fun t => Subtype.ext (h1 t)
     prop' := fun s t ht => by
       rcases ht with rfl | rfl
       · exact Subtype.ext ((hs0 s).trans (by simp))
       · exact Subtype.ext ((hs1 s).trans (by simp)) }⟩

/-! ### Subpaths -/

/-- The affine map of `Peano.affineI` is Mathlib's convex combination in `I`. -/
theorem affineI_eq_convexComb (a b s : I) : affineI a b s = Set.Icc.convexComb a b s := by
  have e : (a : ℝ) + s * (b - a) = (Set.Icc.convexComb a b s : ℝ) := by
    rw [Set.Icc.coe_convexComb]; ring
  show Set.projIcc 0 1 zero_le_one ((a : ℝ) + s * (b - a)) = _
  rw [e, Set.projIcc_val]

/-- `Peano.subpathMap` agrees pointwise with Mathlib's `Path.subpath`. -/
theorem subpathMap_apply_eq_subpath {u v : X} (γ : Path u v) (a b s : I) :
    subpathMap (γ : C(I, X)) a b s = γ.subpath a b s := by
  simp only [subpathMap, ContinuousMap.comp_apply, affineI_eq_convexComb]
  rfl

/-! ### The abelian line integral -/

namespace Homology

variable [PathConnectedSpace X] (x : X)

/-- The abelian "line integral" of a path class `P : u → v`: the class of the loop
`c u · P · (c v)⁻¹` at `x` in the abelianisation of `π₁(X, x)`, where `c w` is the fixed path
`PathConnectedSpace.somePath x w` from `x` to `w`. -/
def abLine {u v : X} (P : Path.Homotopic.Quotient u v) : Abelianization (FundamentalGroup X x) :=
  Abelianization.of (FundamentalGroup.fromPath
    (((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x u)).trans P).trans
      (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x v)).symm))

/-- The line integral is multiplicative under concatenation. -/
theorem abLine_trans {u v w : X} (P : Path.Homotopic.Quotient u v)
    (Q : Path.Homotopic.Quotient v w) : abLine x (P.trans Q) = abLine x P * abLine x Q := by
  simp only [abLine]
  rw [mul_comm, ← map_mul, ← fundamentalGroup_fromPath_trans]
  congr 2
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x v)).symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The line integral of a constant path is `1`. -/
theorem abLine_refl (u : X) : abLine x (Path.Homotopic.Quotient.refl u) = 1 := by
  simp only [abLine, Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm,
    fundamentalGroup_fromPath_refl, map_one]

/-- The line integral inverts under reversal. -/
theorem abLine_symm {u v : X} (P : Path.Homotopic.Quotient u v) :
    abLine x P.symm = (abLine x P)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, mul_comm, ← abLine_trans, Path.Homotopic.Quotient.trans_symm,
    abLine_refl]

/-- On loops at the base point the line integral is the abelianisation map. -/
theorem abLine_loop (P : Path.Homotopic.Quotient x x) :
    abLine x P = Abelianization.of (FundamentalGroup.fromPath P) :=
  abelianization_of_conj_loop _ _

/-- The line integral only depends on the values of a path. -/
theorem abLine_congr {u v u' v' : X} (p : Path u v) (q : Path u' v') (h : ∀ t, p t = q t) :
    abLine x (.mk p) = abLine x (.mk q) := by
  obtain rfl : u = u' := by simpa using h 0
  obtain rfl : v = v' := by simpa using h 1
  obtain rfl : p = q := Path.ext (funext h)
  rfl

/-- A map `I → X` as a path between its values at `0` and `1`. -/
private def pathOfMap (f : C(I, X)) : Path (f 0) (f 1) where
  toContinuousMap := f
  source' := rfl
  target' := rfl

/-- The line integral of a map `I → X`, seen as a path. -/
private def abLineMap (f : C(I, X)) : Abelianization (FundamentalGroup X x) :=
  abLine x (.mk (pathOfMap f))

/-- The line integral is invariant under increasing reparametrisation. -/
private theorem abLineMap_eq_of_isReparam {f g : C(I, X)} (h : IsReparam f g) :
    abLineMap x f = abLineMap x g := by
  obtain ⟨h, hh, hfg⟩ := h
  -- an increasing homeomorphism of `I` is an order isomorphism, so it fixes `0 = ⊥` and `1 = ⊤`
  set e := hh.orderIsoOfSurjective h h.surjective
  have := abLine_congr x (pathOfMap f)
    ((pathOfMap g).reparam h h.continuous e.map_bot e.map_top) hfg
  rw [abLineMap, this, abLineMap]
  exact congrArg _ (Quotient.sound ⟨(Path.Homotopy.reparam _ _ _ _ _).symm⟩)

/-- The line integral of a map composed with the reversal of `I` is the inverse. -/
private theorem abLineMap_comp_symm (f : C(I, X)) :
    abLineMap x (f.comp ⟨σ, continuous_symm⟩) = (abLineMap x f)⁻¹ := by
  rw [abLineMap, abLineMap, ← abLine_symm]
  exact abLine_congr x _ (pathOfMap f).symm (fun t => rfl)

/-- The line integral of a piece `subpathMap γ a b` is that of `γ.subpath a b`. -/
private theorem abLineMap_subpathMap {u v : X} (γ : Path u v) (a b : I) :
    abLineMap x (subpathMap (γ : C(I, X)) a b) = abLine x (.mk (γ.subpath a b)) :=
  abLine_congr x _ _ (subpathMap_apply_eq_subpath γ a b)

end Homology

open Homology

/-! ### The homology class of a loop -/

section HomologyClass

variable [PathConnectedSpace X]

/-- The homology class `[γ]_h ∈ H₁(X) ≅ π₁(X, x)^ab` of a loop `γ` at `y`, written additively: the
line integral of `γ`, i.e. the class of the conjugate `P γ P⁻¹` for the chosen path
`P = somePath x y`. -/
def homologyClass (x : X) {y : X} (γ : Path y y) :
    Additive (Abelianization (FundamentalGroup X x)) :=
  Additive.ofMul (abLine x (.mk γ))

/-- The homology class may be computed with any path from the base point. -/
theorem homologyClass_eq (x : X) {y : X} (p : Path x y) (γ : Path y y) :
    homologyClass x γ = Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (.mk ((p.trans γ).trans p.symm)))) :=
  congrArg Additive.ofMul (abelianization_of_conj_eq _ p γ)

/-- A loop has zero homology class iff its class in `π₁(X, y)` lies in the commutator subgroup
(`[γ]_h = 0`). -/
theorem homologyClass_eq_zero_iff (x : X) {y : X} (γ : Path y y) :
    homologyClass x γ = 0 ↔ FundamentalGroup.fromPath ⟦γ⟧ ∈ commutator (FundamentalGroup X y) := by
  rw [homologyClass_eq x (PathConnectedSpace.somePath x y), ← ofMul_one,
    Additive.ofMul.apply_eq_iff_eq, ← mem_commutator_iff_abelianization_of_eq_one]
  exact conj_mem_commutator_iff _ γ

/-- The class of `α · (p β p⁻¹)` is `[α]_h + [β]_h`. -/
theorem homologyClass_trans_conj (x : X) {y z : X} (α : Path y y) (p : Path y z)
    (β : Path z z) :
    homologyClass x (α.trans ((p.trans β).trans p.symm)) =
      homologyClass x α + homologyClass x β := by
  simp only [homologyClass, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    abLine_trans, abLine_symm, ← ofMul_mul]
  congr 1
  rw [mul_right_comm, mul_inv_cancel, one_mul]

/-- The class of the reversed loop is the negative. -/
theorem homologyClass_symm (x : X) {y : X} (γ : Path y y) :
    homologyClass x γ.symm = -homologyClass x γ := by
  simp only [homologyClass, Path.Homotopic.Quotient.mk_symm, abLine_symm, ofMul_inv]

/-- In a path-connected space, two loops are homologous iff they have the same homology class. -/
theorem isHomologous_iff_homologyClass_eq (x : X) {x₀ x₁ : X} {α : Path x₀ x₀}
    {β : Path x₁ x₁} : IsHomologous α β ↔ homologyClass x α = homologyClass x β := by
  set P := PathConnectedSpace.somePath x x₀
  set Q := PathConnectedSpace.somePath x x₁
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h
    rw [homologyClass_eq x P, homologyClass_eq x (P.trans p)]
    refine congrArg Additive.ofMul ((abelianization_of_conj_congr P hp).trans ?_)
    congr 2
    show Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm, Path.trans_symm,
      Path.Homotopic.Quotient.trans_assoc]
  · intro h
    rw [homologyClass_eq x P, homologyClass_eq x Q] at h
    exact ((isHomologous_conj P α).symm.trans
      (IsHomologous.of_abelianization_eq (Additive.ofMul.injective h))).trans
      (isHomologous_conj Q β)

end HomologyClass

/-! ### 0-forms are null-homologous -/

/-- **0-forms are null-homologous**, in a path-connected space: a loop that can be cut into the
pieces of a 0-form has its class in the commutator subgroup. -/
theorem fromPath_mem_commutator_of_isZeroFormCut_of_pathConnected [PathConnectedSpace X] {x : X}
    (ρ : Path x x) (h : IsZeroFormCut (ρ : C(I, X))) :
    FundamentalGroup.fromPath ⟦ρ⟧ ∈ commutator (FundamentalGroup X x) := by
  rw [mem_commutator_iff_abelianization_of_eq_one]
  show Abelianization.of (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ρ)) = 1
  rw [← abLine_loop]
  obtain ⟨m, t, τ, -, h0, hl, hinv, hfix, -, hrep⟩ := h
  set F : I → Abelianization (FundamentalGroup X x) := fun s => abLine x (.mk (ρ.subpath 0 s))
    with hF
  have key : ∀ a b, abLine x (.mk (ρ.subpath a b)) = F b / F a := by
    intro a b
    rw [eq_div_iff_mul_eq', mul_comm]
    simp only [hF]
    rw [← abLine_trans, Path.Homotopic.mk_subpath_trans_mk_subpath]
  have hprod : ∏ i : Fin (m + 1), abLineMap x (subpathMap (ρ : C(I, X)) (t i.castSucc) (t i.succ))
      = 1 := by
    apply Finset.prod_ninvolution τ
    · intro i
      rw [abLineMap_eq_of_isReparam x (hrep i), abLineMap_comp_symm, mul_inv_cancel]
    · intro i _
      exact hfix i
    · simp
    · exact hinv
  simp_rw [abLineMap_subpathMap, key] at hprod
  -- telescoping
  have htel :
      ∏ i : Fin (m + 1), F (t i.succ) / F (t i.castSucc) = F (t (Fin.last _)) / F (t 0) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff_mul_eq_mul, mul_comm,
      ← Fin.prod_univ_succ (fun i => F (t i)), Fin.prod_univ_castSucc (fun i => F (t i)), mul_comm]
  rw [htel, h0, hl] at hprod
  have hF0 : F 0 = 1 := by
    simp only [hF, Path.subpath_self, Path.Homotopic.Quotient.mk_refl, abLine_refl]
  have hF1 : F 1 = abLine x (.mk ρ) := abLine_congr x _ _ (fun s => by simp)
  rw [hF0, div_one, hF1] at hprod
  exact hprod

/-- A 0-form cut transfers back along an injective map. -/
theorem IsZeroFormCut.of_comp {f : C(Y, X)} (hf : Function.Injective f) {ρ : C(I, Y)}
    (h : IsZeroFormCut (f.comp ρ)) : IsZeroFormCut ρ := by
  obtain ⟨m, t, τ, ht, h0, hl, hinv, hfix, hnc, hrep⟩ := h
  refine ⟨m, t, τ, ht, h0, hl, hinv, hfix, fun i => ?_, fun i => ?_⟩
  · obtain ⟨s₁, s₂, hs⟩ := hnc i
    exact ⟨s₁, s₂, fun he => hs (congrArg f he)⟩
  · obtain ⟨h, hh, he⟩ := hrep i
    exact ⟨h, hh, fun s => hf (he s)⟩

/-- **0-forms are null-homologous in any space** (the "if" direction of Lemma 3.2, which holds
without hypotheses on the space): a loop that can be cut into the pieces of a 0-form has its
class in the commutator subgroup. The loop is moved into its image (path-connected), where
`fromPath_mem_commutator_of_isZeroFormCut_of_pathConnected` applies, and the result is pushed
forward along the inclusion. -/
theorem fromPath_mem_commutator_of_isZeroFormCut {x : X} (ρ : Path x x)
    (h : IsZeroFormCut (ρ : C(I, X))) :
    FundamentalGroup.fromPath ⟦ρ⟧ ∈ commutator (FundamentalGroup X x) := by
  have hmem : ∀ t, ρ t ∈ range ρ := fun t => ⟨t, rfl⟩
  have : PathConnectedSpace (range ρ) :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_range ρ.continuous)
  have h' : IsZeroFormCut ((pathIn ρ (range ρ) hmem : C(I, range ρ))) :=
    IsZeroFormCut.of_comp (f := ⟨Subtype.val, continuous_subtype_val⟩) Subtype.val_injective h
  exact monoidHom_map_mem_commutator
    (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ _)
    (fromPath_mem_commutator_of_isZeroFormCut_of_pathConnected _ h')

end Peano
