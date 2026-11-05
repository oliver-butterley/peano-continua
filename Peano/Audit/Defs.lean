module

import Peano

/-!
# Audit: the definitions in the main statements

`recall` checks theorem statements, but a change to a definition silently changes what they mean.
This file prints every definition the main statements depend on, so that a reviewer can compare
them with the paper (Definitions 2.1, 2.2, 2.4, 4.1, the introduction's wild points, and the
standard notions). See `notes/checks/definitions-review.md`.
-/

#print Peano.CoveringDimLE
#print Peano.earringRadius
#print Peano.earringCircle
#print Peano.earring
#print Peano.earringBase
#print Peano.earringParam
#print Peano.earringLoop
#print Peano.FullyEssential
#print Peano.wildSet
#print Peano.loopWildSet
#print Peano.GenLoop.map
#print Peano.HomotopyGroup.map
#print Peano.ZerothHomotopy.map
#print Peano.IsWeakHomotopyEquivalence
#print Peano.IsSerreFibration
#print Peano.openUnit
#print Peano.IsStandardForm
#print Peano.ArcSystem
#print Peano.IsReducedPath
#print Peano.IsReparam
#print Peano.IsZeroFormCut
