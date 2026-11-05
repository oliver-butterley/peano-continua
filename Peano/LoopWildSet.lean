module

public import Peano.Defs

/-!
# The wild set through small essential loops

The introduction of Brazas–Pavešić (arXiv:2610.35875), and the papers it cites (Brazas–Fischer
2020, Brazas–Pavešić arXiv:2510.22901 Def. 3.5), define a *wild point* `x` by small loops: every
neighbourhood of `x` contains the image of a loop based at `x` that is essential in `X`. The paper
works with Definition 2.2 instead (`Peano.wildSet`, through fully essential maps from the earring)
and remarks that the two agree for first-countable spaces.

This file only records the loop definition, `loopWildSet`, so that axioms quoting sources which use
it can be stated literally. The comparison with `wildSet` is proved in `Peano.WildSet`.
-/

@[expose] public section

open Set Topology

namespace Peano

/-- The *loop wild set*: points `x` such that every neighbourhood of `x` contains the image of a
loop based at `x` that is not null-homotopic (rel end points) in `X`. -/
def loopWildSet (X : Type*) [TopologicalSpace X] : Set X :=
  {x | ∀ U ∈ 𝓝 x, ∃ γ : Path x x, range γ ⊆ U ∧ ¬ γ.Homotopic (Path.refl x)}

end Peano
