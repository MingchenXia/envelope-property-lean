/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.NormedIdealQuotient
import EnvelopeProperty.NormedAdditiveQuotientUltrametric

/-! # The true infimum ideal quotient norm remains ultrametric -/
noncomputable section
namespace EnvelopeProperty.NormedIdealQuotient

/-- Genuine infimum-norm representatives derive the quotient ultrametric inequality. -/
instance quotientIsUltrametricDist {A : Type*} [SeminormedCommRing A]
    [IsUltrametricDist A] (I : Ideal A) : IsUltrametricDist (A ⧸ I) :=
  NormedAdditiveQuotient.quotientIsUltrametricDist I.toAddSubgroup

end EnvelopeProperty.NormedIdealQuotient
