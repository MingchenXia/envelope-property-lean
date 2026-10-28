import EnvelopeProperty.Vanishing.NadelPrincipalizationEtaleKernel
import EnvelopeProperty.Vanishing.NadelPrincipalizationMultiplierRestriction
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! # The entire original global BP kernel is the original scheme multiplier ideal -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationWholeKernel
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem stalk_eq_of_comap_eq {X Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (I J : X.IdealSheafData) (h : I.comap g = J.comap g) (y : Y) :
    I.stalkIdeal (g y) = J.stalkIdeal (g y) := by
  have hs := congrArg (fun K : Y.IdealSheafData => K.stalkIdeal y) h
  rw [Scheme.IdealSheafData.stalkIdeal_comap,
    Scheme.IdealSheafData.stalkIdeal_comap] at hs
  have hb : Function.Bijective (g.stalkMap y).hom :=
    ConcreteCategory.bijective_of_isIso (g.stalkMap y)
  have hc := congrArg (fun K => Ideal.comap (g.stalkMap y).hom K) hs
  simpa only [Ideal.comap_map_of_bijective _ hb] using hc

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

private theorem global_smooth :
    SmoothOfRelativeDimension n ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) :=
  NadelPrincipalization.stage_smoothOfRelativeDimension f hp n I hI (Fin.last _)

/-- The ENTIRE native rounded canonical kernel ideal of the original global
BP equals the ENTIRE original scheme multiplier ideal, retaining the original
scheme, field map, ideal, relative dimension and rational exponent. -/
theorem kernel_eq_multiplier (q : ℚ) :
    letI := global_smooth f hp n I hI
    letI : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
      NadelPrincipalization.composite_isProper f hp n I hI
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    roundedCanonicalKernelIdeal f (NadelPrincipalization.sequence f hp n I hI).composite n
      (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
      (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q =
    Char0.schemeMultiplierIdealSheaf f I hI q := by
  let := global_smooth f hp n I hI
  let : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
    NadelPrincipalization.composite_isProper f hp n I hI
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro x
  let U := NadelPrincipalizationEtaleChart.chart f n x
  let : Nonempty U.1 := NadelPrincipalizationEtaleChart.chart_nonempty f n x
  let := f.stalkAlgebra (genericPoint X)
  let := NadelPrincipalizationAffineChart.algebra_isFractionRing f U
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := NadelPrincipalizationKernelRestriction.affineLast_smooth f hp n I hI U
  let : IsProper (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
    MorphismProperty.of_isPullback
      (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
  have he := (NadelPrincipalizationKernelRestriction.kernel_comap f hp n I hI U q).trans
    ((NadelPrincipalizationEtaleKernel.local_kernel_eq_multiplier f hp n I hI x q).trans
      (NadelPrincipalizationMultiplierRestriction.comap_eq f I hI q U).symm)
  obtain ⟨y, hy⟩ := NadelPrincipalizationEtaleChart.map_covers f n x
  change NadelPrincipalizationAffineChart.map f U y = x at hy
  have hs := stalk_eq_of_comap_eq (NadelPrincipalizationAffineChart.map f U) _ _ he y
  rw [hy] at hs
  exact hs

end EnvelopeProperty.Vanishing.NadelPrincipalizationWholeKernel
