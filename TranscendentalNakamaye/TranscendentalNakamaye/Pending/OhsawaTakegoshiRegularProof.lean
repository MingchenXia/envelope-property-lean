import TranscendentalNakamaye.Pending.OTRegularFromHormander
import TranscendentalNakamaye.Pending.HormanderL2Theorem

set_option autoImplicit false

/-!
# The regular Ohsawa--Takegoshi theorem, unconditionally

`ohsawaTakegoshiHyperplaneRegular_proved` combines Hörmander's `L²` estimate
(`Hormander.hormanderL2Estimate`, `Pending.HormanderL2Theorem`) with Chen's derivation of the
Ohsawa--Takegoshi extension theorem from it (`ohsawaTakegoshiHyperplaneRegular_of_hormander`,
`Pending.OTRegularFromHormander`).  The Weyl lemma for `∂̄` enters through
`Pending.WeakDbarWeyl`.
-/

namespace TranscendentalNakamaye.Pending

/-- **The Ohsawa--Takegoshi theorem, regular case.** -/
theorem ohsawaTakegoshiHyperplaneRegular_proved : OhsawaTakegoshiHyperplaneRegular :=
  ohsawaTakegoshiHyperplaneRegular_of_hormander Hormander.hormanderL2Estimate

end TranscendentalNakamaye.Pending
