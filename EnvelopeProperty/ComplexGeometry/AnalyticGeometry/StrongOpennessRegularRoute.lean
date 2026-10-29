import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.StrongOpennessFromRegularOhsawaTakegoshi
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.OhsawaTakegoshiRegularProof

set_option autoImplicit false

/-!
# Strong openness from the proved regular Ohsawa--Takegoshi theorem

The route to `IncreasingStrongOpenness n` is

  `OhsawaTakegoshiHyperplaneRegular`  (bounded convex domains, weights smooth and
                                       plurisubharmonic near the closure)
      ⟹ `OhsawaTakegoshiHyperplane`   (`AnalyticGeometry.StrongOpennessFromRegularOhsawaTakegoshi`)
      ⟹ `IncreasingStrongOpenness n` (`AnalyticGeometry.StrongOpennessFromOhsawaTakegoshi`)

and the regular case is now a theorem, `ohsawaTakegoshiHyperplaneRegular_proved`
(`AnalyticGeometry.OhsawaTakegoshiRegularProof`): Hörmander's `L²` estimate for `∂̄` on convex domains
with three weights (`AnalyticGeometry.HormanderL2Theorem`) and B.-Y. Chen's derivation of the
Ohsawa--Takegoshi extension from it (`AnalyticGeometry.OTRegularFromHormander`).  This module contains no
`sorry`.
-/

namespace ComplexGeometry.AnalyticGeometry

/-- The Ohsawa--Takegoshi theorem, regular case. -/
theorem ohsawaTakegoshiHyperplaneRegular : OhsawaTakegoshiHyperplaneRegular :=
  ohsawaTakegoshiHyperplaneRegular_proved

/-- Strong openness for increasing sequences in every dimension. -/
theorem increasingStrongOpenness_ofRegularRoute (n : ℕ) : IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_ohsawaTakegoshiRegular ohsawaTakegoshiHyperplaneRegular n

end ComplexGeometry.AnalyticGeometry
