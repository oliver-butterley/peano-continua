module

import Peano

/-!
# Audit: the definitions in the main statements

`recall` checks theorem statements, but a change to a definition silently changes what they mean.
This file prints every definition the main statements depend on, so that a reviewer can compare
them with the paper (Definitions 2.1, 2.2, 2.4, 4.1, the introduction's wild points, and the
standard notions). See `notes/checks/definitions-review.md`.
-/

/--
info: def Peano.CoveringDimLE.{u_1} : ℕ → (X : Type u_1) → [TopologicalSpace X] → Prop :=
fun n X [TopologicalSpace X] =>
  ∀ (ι : Type) [Finite ι] (U : ι → Set X),
    (∀ (i : ι), IsOpen (U i)) →
      ⋃ i, U i = Set.univ →
        ∃ κ,
          ∃ (_ : Finite κ),
            ∃ V,
              (∀ (j : κ), IsOpen (V j)) ∧
                ⋃ j, V j = Set.univ ∧ (∀ (j : κ), ∃ i, V j ⊆ U i) ∧ ∀ (x : X), {j | x ∈ V j}.ncard ≤ n + 1
-/
#guard_msgs in
#print Peano.CoveringDimLE
/--
info: def Peano.earringRadius : ℕ → ℝ :=
fun k => 1 / (↑k + 1)
-/
#guard_msgs in
#print Peano.earringRadius
/--
info: def Peano.earringCircle : ℕ → Set (ℝ × ℝ) :=
fun k => {p | (p.1 - Peano.earringRadius k) ^ 2 + p.2 ^ 2 = Peano.earringRadius k ^ 2}
-/
#guard_msgs in
#print Peano.earringCircle
/--
info: def Peano.earring : Set (ℝ × ℝ) :=
⋃ k, Peano.earringCircle k
-/
#guard_msgs in
#print Peano.earring
/--
info: def Peano.earringBase : ↑Peano.earring :=
⟨(0, 0), Peano.earringBase._proof_1⟩
-/
#guard_msgs in
#print Peano.earringBase
/--
info: def Peano.earringParam : ℕ → ℝ → ℝ × ℝ :=
fun k t =>
  (Peano.earringRadius k - Peano.earringRadius k * Real.cos (2 * Real.pi * t),
    Peano.earringRadius k * Real.sin (2 * Real.pi * t))
-/
#guard_msgs in
#print Peano.earringParam
/--
info: def Peano.earringLoop : ℕ → Path Peano.earringBase Peano.earringBase :=
fun k => { toFun := fun t => ⟨Peano.earringParam k ↑t, ⋯⟩, continuous_toFun := ⋯, source' := ⋯, target' := ⋯ }
-/
#guard_msgs in
#print Peano.earringLoop
/--
info: def Peano.FullyEssential.{u_1} : {X : Type u_1} → [inst : TopologicalSpace X] → C(↑Peano.earring, X) → Prop :=
fun {X} [TopologicalSpace X] f => ∀ (k : ℕ), ¬((Peano.earringLoop k).map ⋯).Homotopic (Path.refl (f Peano.earringBase))
-/
#guard_msgs in
#print Peano.FullyEssential
/--
info: def Peano.wildSet.{u_1} : (X : Type u_1) → [TopologicalSpace X] → Set X :=
fun X [TopologicalSpace X] => {x | ∃ f, f Peano.earringBase = x ∧ Peano.FullyEssential f}
-/
#guard_msgs in
#print Peano.wildSet
/--
info: def Peano.loopWildSet.{u_1} : (X : Type u_1) → [TopologicalSpace X] → Set X :=
fun X [TopologicalSpace X] => {x | ∀ U ∈ nhds x, ∃ γ, Set.range ⇑γ ⊆ U ∧ ¬γ.Homotopic (Path.refl x)}
-/
#guard_msgs in
#print Peano.loopWildSet
/--
info: def Peano.GenLoop.map.{u_1, u_2, u_3} : {X : Type u_1} →
  {Y : Type u_2} →
    [inst : TopologicalSpace X] →
      [inst_1 : TopologicalSpace Y] →
        {N : Type u_3} → (f : C(X, Y)) → {x : X} → ↑(GenLoop N X x) → ↑(GenLoop N Y (f x)) :=
fun {X} {Y} [TopologicalSpace X] [TopologicalSpace Y] {N} f {x} γ => ⟨f.comp ↑γ, ⋯⟩
-/
#guard_msgs in
#print Peano.GenLoop.map
/--
info: def Peano.HomotopyGroup.map.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} →
    [inst : TopologicalSpace X] →
      [inst_1 : TopologicalSpace Y] →
        (f : C(X, Y)) → (n : ℕ) → (x : X) → HomotopyGroup.Pi n X x → HomotopyGroup.Pi n Y (f x) :=
fun {X} {Y} [TopologicalSpace X] [TopologicalSpace Y] f n x => Quotient.map (Peano.GenLoop.map f) ⋯
-/
#guard_msgs in
#print Peano.HomotopyGroup.map
/--
info: def Peano.ZerothHomotopy.map.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} →
    [inst : TopologicalSpace X] → [inst_1 : TopologicalSpace Y] → C(X, Y) → ZerothHomotopy X → ZerothHomotopy Y :=
fun {X} {Y} [TopologicalSpace X] [TopologicalSpace Y] f => Quotient.map ⇑f ⋯
-/
#guard_msgs in
#print Peano.ZerothHomotopy.map
/--
info: def Peano.IsWeakHomotopyEquivalence.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : TopologicalSpace Y] → C(X, Y) → Prop :=
fun {X} {Y} [TopologicalSpace X] [TopologicalSpace Y] f =>
  Function.Bijective (Peano.ZerothHomotopy.map f) ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (x : X), Function.Bijective (Peano.HomotopyGroup.map f n x)
-/
#guard_msgs in
#print Peano.IsWeakHomotopyEquivalence
/--
info: def Peano.IsSerreFibration.{u_1, u_2} : {X : Type u_1} →
  {Y : Type u_2} → [inst : TopologicalSpace X] → [inst_1 : TopologicalSpace Y] → C(X, Y) → Prop :=
fun {X} {Y} [TopologicalSpace X] [TopologicalSpace Y] p =>
  ∀ (n : ℕ) (F : C((Fin n → ↑unitInterval) × ↑unitInterval, Y)) (f₀ : C(Fin n → ↑unitInterval, X)),
    (∀ (y : Fin n → ↑unitInterval), p (f₀ y) = F (y, 0)) →
      ∃ G,
        (∀ (y : Fin n → ↑unitInterval), G (y, 0) = f₀ y) ∧
          ∀ (z : (Fin n → ↑unitInterval) × ↑unitInterval), p (G z) = F z
-/
#guard_msgs in
#print Peano.IsSerreFibration
/--
info: def Peano.openUnit : Set ↑unitInterval :=
{t | 0 < ↑t ∧ ↑t < 1}
-/
#guard_msgs in
#print Peano.openUnit
/--
info: def Peano.IsStandardForm.{u_3} : (X : Type u_3) → [TopologicalSpace X] → Prop :=
fun X [TopologicalSpace X] =>
  ∃ ι h,
    (∀ (i : ι), Set.InjOn (⇑(h i)) Peano.openUnit) ∧
      (∀ (i : ι), (h i) 0 ∈ Peano.wildSet X ∧ (h i) 1 ∈ Peano.wildSet X) ∧
        (Pairwise fun i j => Disjoint (⇑(h i) '' Peano.openUnit) (⇑(h j) '' Peano.openUnit)) ∧
          ⋃ i, ⇑(h i) '' Peano.openUnit = (Peano.wildSet X)ᶜ ∧
            ∀ (i : ι), IsOpen (Subtype.val ⁻¹' ⇑(h i) '' Peano.openUnit)
-/
#guard_msgs in
#print Peano.IsStandardForm
/--
info: structure Peano.ArcSystem.{u_1} (X : Type u_1) [TopologicalSpace X] : Type (max 1 u_1)
number of parameters: 2
fields:
  Peano.ArcSystem.W : Set X
  Peano.ArcSystem.isClosed_W : IsClosed self.W
  Peano.ArcSystem.ι : Type
  Peano.ArcSystem.h : self.ι → C(↑unitInterval, X)
  Peano.ArcSystem.injOn : ∀ (i : self.ι), Set.InjOn (⇑(self.h i)) Peano.openUnit
  Peano.ArcSystem.mem_W : ∀ (i : self.ι), (self.h i) 0 ∈ self.W ∧ (self.h i) 1 ∈ self.W
  Peano.ArcSystem.disjoint : Pairwise fun i j =>
      Disjoint (⇑(self.h i) '' Peano.openUnit) (⇑(self.h j) '' Peano.openUnit)
  Peano.ArcSystem.iUnion_eq : ⋃ i, ⇑(self.h i) '' Peano.openUnit = self.Wᶜ
  Peano.ArcSystem.isOpen_arc : ∀ (i : self.ι), IsOpen (⇑(self.h i) '' Peano.openUnit)
constructor:
  Peano.ArcSystem.mk.{u_1} {X : Type u_1} [TopologicalSpace X] (W : Set X) (isClosed_W : IsClosed W) (ι : Type)
    (h : ι → C(↑unitInterval, X)) (injOn : ∀ (i : ι), Set.InjOn (⇑(h i)) Peano.openUnit)
    (mem_W : ∀ (i : ι), (h i) 0 ∈ W ∧ (h i) 1 ∈ W)
    (disjoint : Pairwise fun i j => Disjoint (⇑(h i) '' Peano.openUnit) (⇑(h j) '' Peano.openUnit))
    (iUnion_eq : ⋃ i, ⇑(h i) '' Peano.openUnit = Wᶜ) (isOpen_arc : ∀ (i : ι), IsOpen (⇑(h i) '' Peano.openUnit)) :
    Peano.ArcSystem X
-/
#guard_msgs in
#print Peano.ArcSystem
