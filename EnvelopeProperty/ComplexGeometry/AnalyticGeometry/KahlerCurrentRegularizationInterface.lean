import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.DemaillyRegularizedMaxBergmanDataInterface

set_option autoImplicit false

/-!
# Demailly regularization of Kähler currents: the Bergman chart-frame package

This module imports the finite regularized-max Bergman chart-frame package of
`DemaillyRegularizedMaxBergmanDataInterface`, so that its structures, which other modules
use, are reachable from `KahlerCurrentRegularization`.  The Kähler-current consequence
`KahlerCurrentRegularization.exists_kahlerCurrent_poleSet_subset_lelongNumber_pos`
is proved from Demailly's approximation theorem
(`KahlerCurrentRegularizationAlgebraicApproximation`).
-/
