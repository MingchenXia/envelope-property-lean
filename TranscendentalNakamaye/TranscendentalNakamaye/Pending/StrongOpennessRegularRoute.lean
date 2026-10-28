import TranscendentalNakamaye.Pending.StrongOpennessFromRegularOhsawaTakegoshi
import TranscendentalNakamaye.Pending.OhsawaTakegoshiRegularProof

set_option autoImplicit false

/-!
# Strong openness from the proved regular Ohsawa--Takegoshi theorem

The route to `IncreasingStrongOpenness n` is

  `OhsawaTakegoshiHyperplaneRegular`  (bounded convex domains, weights smooth and
                                       plurisubharmonic near the closure)
      ⟹ `OhsawaTakegoshiHyperplane`   (`Pending.StrongOpennessFromRegularOhsawaTakegoshi`)
      ⟹ `IncreasingStrongOpenness n` (`Pending.StrongOpennessFromOhsawaTakegoshi`)

and the regular case is now a theorem, `ohsawaTakegoshiHyperplaneRegular_proved`
(`Pending.OhsawaTakegoshiRegularProof`): Hörmander's `L²` estimate for `∂̄` on convex domains
with three weights (`Pending.HormanderL2Theorem`) and B.-Y. Chen's derivation of the
Ohsawa--Takegoshi extension from it (`Pending.OTRegularFromHormander`).  This module contains no
`sorry`.
-/

namespace TranscendentalNakamaye.Pending

/-- The Ohsawa--Takegoshi theorem, regular case. -/
theorem ohsawaTakegoshiHyperplaneRegular : OhsawaTakegoshiHyperplaneRegular :=
  ohsawaTakegoshiHyperplaneRegular_proved

/-- Strong openness for increasing sequences in every dimension. -/
theorem increasingStrongOpenness_ofRegularRoute (n : ℕ) : IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_ohsawaTakegoshiRegular ohsawaTakegoshiHyperplaneRegular n

end TranscendentalNakamaye.Pending
