import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.OTRegularFromHormander
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.HormanderL2Theorem

set_option autoImplicit false

/-!
# The regular Ohsawa--Takegoshi theorem

`ohsawaTakegoshiHyperplaneRegular_proved` combines Hörmander's `L²` estimate
(`Hormander.hormanderL2Estimate`, `AnalyticGeometry.HormanderL2Theorem`) with Chen's derivation of the
Ohsawa--Takegoshi extension theorem from it (`ohsawaTakegoshiHyperplaneRegular_of_hormander`,
`AnalyticGeometry.OTRegularFromHormander`). The Weyl lemma for `∂̄` enters through
`AnalyticGeometry.WeakDbarWeyl`.
-/

namespace ComplexGeometry.AnalyticGeometry

/-- **The Ohsawa--Takegoshi theorem, regular case.** -/
theorem ohsawaTakegoshiHyperplaneRegular_proved : OhsawaTakegoshiHyperplaneRegular :=
  ohsawaTakegoshiHyperplaneRegular_of_hormander Hormander.hormanderL2Estimate

end ComplexGeometry.AnalyticGeometry
