import EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleMultiplier
import EnvelopeProperty.Vanishing.NadelPrincipalizationKernelRestriction
import EnvelopeProperty.Char0.BPGeometricMultiplierKernel

/-! # The same actual affine BP kernel is the full original multiplier ideal -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleKernel
open Char0 Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

/-- Original smoothness internally selects actual original etale coordinates;
the SAME actual affine BP's entire native kernel ideal is the FULL original
multiplier ideal sheaf for the same original coefficient algebra and ideal. -/
theorem local_kernel_eq_multiplier (x : X) (q : ℚ) :
    let U := NadelPrincipalizationEtaleChart.chart f n x
    letI : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
    letI := f.stalkAlgebra (genericPoint X)
    letI := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
    letI := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
    letI := NadelPrincipalizationKernelRestriction.affineLast_smooth f hp n I hI U
    letI : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
      NadelPrincipalization.composite_isProper f hp n I hI
    letI : IsProper (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
      MorphismProperty.of_isPullback
        (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
    roundedCanonicalKernelIdeal (NadelPrincipalizationAffineChart.structureMap f U)
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n
      ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite)
      (NadelPrincipalizationRoundedRestriction.affineTotalTransform_isSnc f hp n I hI U) q =
    multiplierIdealSheaf (NadelPrincipalizationAffineChart.algebra f U)
      (NadelPrincipalizationAffineChart.ideal f I U)
      (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U) q := by
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := NadelPrincipalizationKernelRestriction.affineLast_smooth f hp n I hI U
  let : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
    NadelPrincipalization.composite_isProper f hp n I hI
  let : IsProper (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
    MorphismProperty.of_isPullback
      (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
  obtain ⟨S, hS, hsm, hproper, hJ, hK⟩ :=
    exists_BP_roundedCanonicalKernelIdeal_eq_multiplierIdealSheaf
      (NadelPrincipalizationAffineChart.algebra f U) n
      (NadelPrincipalizationAffineChart.ideal f I U)
      (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)
      (NadelPrincipalizationEtaleChart.fieldCoordinates f n x)
      (NadelPrincipalizationEtaleChart.fieldCoordinates_etale f n x)
  subst S
  simpa only [NadelPrincipalizationRestriction.affineSequence,
    NadelPrincipalizationRestriction.affineTriple,
    NadelPrincipalizationAffineChart.structureMap] using hK q

end EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleKernel
