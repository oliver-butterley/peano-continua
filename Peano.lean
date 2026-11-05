module

public import Peano.Defs
public import Peano.Arcs
public import Peano.StandardForm
public import Peano.Coarsify
public import Peano.WeakEquiv
public import Peano.Axioms.Cited
public import Peano.Axioms.Standard
public import Peano.Main

/-!
# Countable models of one-dimensional Peano continua

Formalisation of the core of Brazas–Pavešić, *Countable models of one-dimensional Peano
continua* (arXiv:2610.35875): §4–§5 and the "if" direction of Theorem 1.1. Notes, checks and the
lemma map are in `notes/`. The audit files `Peano/Audit/*.lean` are not imported here; build them
with `lake build Peano.Audit.<Name>`.
-/
