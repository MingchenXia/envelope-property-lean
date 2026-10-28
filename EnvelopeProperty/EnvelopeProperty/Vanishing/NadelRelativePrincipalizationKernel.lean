import EnvelopeProperty.Vanishing.NadelRelativePrincipalizationRestriction
import EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleKernel
import EnvelopeProperty.Vanishing.NadelPrincipalizationMultiplierRestriction
import EnvelopeProperty.Vanishing.NadelPrincipalizationWholeKernel

/-! # The original all-DVR multiplier ideal on the relative global BP

The actual affine BP formulas and generic open base-change theorems are reused.
The global scheme is separated finite type over k; properness is required only
of its actual blowup composite, which is produced internally. No global
properness over k or multiplier/kernel comparison is supplied.
-/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelRelativePrincipalizationKernel
open Char0.RoundedCanonicalModule
open NadelPrincipalizationRestriction (affineSequence)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  for (source, short, full) in [
      (`EnvelopeProperty.Vanishing.NadelPrincipalizationKernelRestriction,
        `smooth_transport,
        `EnvelopeProperty.Vanishing.NadelPrincipalizationKernelRestriction.smooth_transport),
      (`EnvelopeProperty.Vanishing.NadelPrincipalizationKernelRestriction,
        `kernel_transport,
        `EnvelopeProperty.Vanishing.NadelPrincipalizationKernelRestriction.kernel_transport),
      (`EnvelopeProperty.Vanishing.NadelPrincipalizationWholeKernel,
        `stalk_eq_of_comap_eq,
        `EnvelopeProperty.Vanishing.NadelPrincipalizationWholeKernel.stalk_eq_of_comap_eq)] do
    let original := Lean.mkPrivateNameCore source full
    unless (← Lean.getEnv).contains original do throwError "missing original generic kernel transport law"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short original :: scope.openDecls}

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

/-- The SAME original affine BP is smooth of the original absolute dimension. -/
theorem affineLast_smooth (U : X.affineOpens) [Nonempty U.1] :
    SmoothOfRelativeDimension n ((affineSequence f n I hI U).composite ≫
      NadelPrincipalizationAffineChart.structureMap f U) := by
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  exact Char0.affinePrincipalization_smoothOfRelativeDimension
    (NadelPrincipalizationAffineChart.structureMap f U) n
    (NadelPrincipalizationAffineChart.ideal f I U)
    (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)

/-- The SAME original affine ideal has its actual full SNC total transform. -/
theorem affineTotalTransform_isSnc (U : X.affineOpens) [Nonempty U.1] :
    ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
      (affineSequence f n I hI U).composite).IsIdealOfSncDivisor := by
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  exact Char0.affinePrincipalization_isIdealOfSncDivisor
    (NadelPrincipalizationAffineChart.structureMap f U) n
    (NadelPrincipalizationAffineChart.ideal f I U)
    (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)

/-- Properness of the actual affine blowup composite is internal, over its own base. -/
theorem affineComposite_isProper (U : X.affineOpens) [Nonempty U.1] :
    IsProper (affineSequence f n I hI U).composite := by
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let : Smooth (NadelPrincipalizationAffineChart.structureMap f U) :=
    SmoothOfRelativeDimension.smooth n _
  let : IsLocallyNoetherian (Spec (.of (NadelPrincipalizationAffineChart.algebra f U))) :=
    (NadelPrincipalizationAffineChart.structureMap f U).isLocallyNoetherian_of_field
  exact (affineSequence f n I hI U).isProper_composite

/-- The native all-DVR affine theorem identifies the entire actual affine kernel. -/
theorem local_kernel_eq_multiplier (x : X) (q : ℚ) :
    let U := NadelPrincipalizationEtaleChart.chart f n x
    letI : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
    letI := f.stalkAlgebra (genericPoint X)
    letI := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
    letI := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
    letI := affineLast_smooth f n I hI U
    letI := affineComposite_isProper f n I hI U
    roundedCanonicalKernelIdeal (NadelPrincipalizationAffineChart.structureMap f U)
      (affineSequence f n I hI U).composite n
      ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (affineSequence f n I hI U).composite)
      (affineTotalTransform_isSnc f n I hI U) q =
    Char0.multiplierIdealSheaf (NadelPrincipalizationAffineChart.algebra f U)
      (NadelPrincipalizationAffineChart.ideal f I U)
      (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U) q := by
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := affineLast_smooth f n I hI U
  let := affineComposite_isProper f n I hI U
  obtain ⟨S, hS, hsm, hproper, hJ, hK⟩ :=
    Char0.exists_BP_roundedCanonicalKernelIdeal_eq_multiplierIdealSheaf
      (NadelPrincipalizationAffineChart.algebra f U) n
      (NadelPrincipalizationAffineChart.ideal f I U)
      (NadelPrincipalizationAffineChart.ideal_ne_bot f I hI U)
      (NadelPrincipalizationEtaleChart.fieldCoordinates f n x)
      (NadelPrincipalizationEtaleChart.fieldCoordinates_etale f n x)
  subst S
  simpa only [NadelPrincipalizationRestriction.affineSequence,
    NadelPrincipalizationRestriction.affineTriple,
    NadelPrincipalizationAffineChart.structureMap] using hK q

variable [FiniteType f] [IsSeparated f]

private theorem global_smooth :
    SmoothOfRelativeDimension n ((NadelRelativePrincipalization.sequence f n I hI).composite ≫ f) :=
  NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)

/-- The full original global BP kernel genuinely restricts to its SAME actual affine BP. -/
theorem kernel_comap (U : X.affineOpens) [Nonempty U.1] (q : ℚ) :
    letI := global_smooth f n I hI
    letI := NadelRelativePrincipalization.composite_isProper f n I hI
    letI := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
    letI := affineLast_smooth f n I hI U
    letI := affineComposite_isProper f n I hI U
    (roundedCanonicalKernelIdeal f (NadelRelativePrincipalization.sequence f n I hI).composite n
      (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
      (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q).comap
        (NadelPrincipalizationAffineChart.map f U) =
    roundedCanonicalKernelIdeal (NadelPrincipalizationAffineChart.structureMap f U)
      (affineSequence f n I hI U).composite n
      ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (affineSequence f n I hI U).composite)
      (affineTotalTransform_isSnc f n I hI U) q := by
  let := global_smooth f n I hI
  let := NadelRelativePrincipalization.composite_isProper f n I hI
  let : Smooth ((NadelRelativePrincipalization.sequence f n I hI).composite ≫ f) :=
    SmoothOfRelativeDimension.smooth n _
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := affineLast_smooth f n I hI U
  let := affineComposite_isProper f n I hI U
  let := NadelRelativePrincipalizationRestriction.lastMap_isOpenImmersion f n I hI U
  let : SmoothOfRelativeDimension n (NadelPrincipalizationAffineChart.map f U ≫ f) :=
    smooth_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U) n
  let : SmoothOfRelativeDimension n
      ((affineSequence f n I hI U).composite ≫ (NadelPrincipalizationAffineChart.map f U ≫ f)) :=
    smooth_transport _ _ (congrArg (fun a => (affineSequence f n I hI U).composite ≫ a)
      (NadelPrincipalizationAffineChart.map_structure f U)) n
  have hk := NadelPrincipalizationRelativeKernel.kernel_comap f
    (NadelPrincipalizationAffineChart.map f U)
    (NadelRelativePrincipalization.sequence f n I hI).composite
    (affineSequence f n I hI U).composite
    (NadelRelativePrincipalizationRestriction.lastMap f n I hI U)
    (NadelRelativePrincipalizationRestriction.last_isPullback f n I hI U).flip n
    (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
    (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q
  exact hk.trans (kernel_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U)
    (affineSequence f n I hI U).composite n _ _
    (NadelRelativePrincipalizationRestriction.totalTransform_comap f n I hI U) _
    (affineTotalTransform_isSnc f n I hI U) q)

/-- The ENTIRE original all-DVR scheme multiplier ideal equals the actual relative BP kernel. -/
theorem kernel_eq_multiplier (q : ℚ) :
    letI := global_smooth f n I hI
    letI := NadelRelativePrincipalization.composite_isProper f n I hI
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    roundedCanonicalKernelIdeal f (NadelRelativePrincipalization.sequence f n I hI).composite n
      (I.comap (NadelRelativePrincipalization.sequence f n I hI).composite)
      (NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI) q =
    Char0.schemeMultiplierIdealSheaf f I hI q := by
  let := global_smooth f n I hI
  let := NadelRelativePrincipalization.composite_isProper f n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro x
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := affineLast_smooth f n I hI U
  let := affineComposite_isProper f n I hI U
  have he := (kernel_comap f n I hI U q).trans
    ((local_kernel_eq_multiplier f n I hI x q).trans
      (NadelPrincipalizationMultiplierRestriction.comap_eq f I hI q U).symm)
  obtain ⟨y, hy⟩ := NadelPrincipalizationEtaleChart.map_covers f n x
  change NadelPrincipalizationAffineChart.map f U y = x at hy
  have hs := stalk_eq_of_comap_eq (NadelPrincipalizationAffineChart.map f U) _ _ he y
  rw [hy] at hs
  exact hs

end EnvelopeProperty.Vanishing.NadelRelativePrincipalizationKernel
