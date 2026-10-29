import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeKernel
import EnvelopeProperty.Vanishing.NadelPrincipalizationRoundedRestriction
import EnvelopeProperty.Vanishing.NadelPrincipalizationGeometry
import EnvelopeProperty.Char0.RoundedCanonicalKernelIdeal

/-! # The whole original BP kernel ideal on the same original affine BP

All local smoothness, properness and kernel criteria are produced internally
from the original geometry. No local kernel comparison is an input.
-/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationKernelRestriction
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem smooth_open_transport {A B S : Scheme.{u}}
    (s : A ⟶ S) (j : B ⟶ A) [IsOpenImmersion j] (t : B ⟶ S)
    (e : j ≫ s = t) (n : ℕ) [SmoothOfRelativeDimension n s] :
    SmoothOfRelativeDimension n t :=
  e ▸ ((Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := j) (n := 0) (m := n) s))

private theorem smooth_transport {A S : Scheme.{u}} (a b : A ⟶ S)
    (e : a = b) (n : ℕ) [SmoothOfRelativeDimension n b] : SmoothOfRelativeDimension n a :=
  e.symm ▸ inferInstance

private theorem kernel_transport {k : Type u} [Field k] {A B : Scheme.{u}}
    (f₁ f₂ : A ⟶ Spec (.of k)) (ef : f₁ = f₂) (p : B ⟶ A) (n : ℕ)
    [SmoothOfRelativeDimension n f₁] [SmoothOfRelativeDimension n f₂]
    [SmoothOfRelativeDimension n (p ≫ f₁)] [SmoothOfRelativeDimension n (p ≫ f₂)] [QuasiCompact p]
    (J J' : B.IdealSheafData) (eJ : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ) :
    roundedCanonicalKernelIdeal f₁ p n J hJ q = roundedCanonicalKernelIdeal f₂ p n J' hJ' q := by
  subst f₂
  subst J'
  rfl

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (U : X.affineOpens) [Nonempty U.1]

private theorem global_smooth :
    SmoothOfRelativeDimension n ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) :=
  NadelPrincipalization.stage_smoothOfRelativeDimension f hp n I hI (Fin.last _)

include hp in
theorem affineLast_smooth :
    SmoothOfRelativeDimension n
      ((NadelPrincipalizationRestriction.affineSequence f n I hI U).composite ≫
        NadelPrincipalizationAffineChart.structureMap f U) := by
  let := global_smooth f hp n I hI
  let := NadelPrincipalizationRestriction.lastMap_isOpenImmersion f hp n I hI U
  exact smooth_open_transport
    ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f)
    (NadelPrincipalizationRestriction.lastMap f hp n I hI U) _
    (NadelPrincipalizationRestriction.lastMap_structure f hp n I hI U) n


/-- The ENTIRE original global BP rounded canonical kernel ideal restricts
to the ENTIRE actual original affine BP kernel ideal. All comparisons and
smoothness on the original source and local BP are produced internally. -/
theorem kernel_comap (q : ℚ) :
    letI := global_smooth f hp n I hI
    letI : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
      NadelPrincipalization.composite_isProper f hp n I hI
    letI := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
    letI := affineLast_smooth f hp n I hI U
    letI : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
      MorphismProperty.of_isPullback
        (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
    (roundedCanonicalKernelIdeal f (NadelPrincipalization.sequence f hp n I hI).composite n
      (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
      (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q).comap
        (NadelPrincipalizationAffineChart.map f U) =
    roundedCanonicalKernelIdeal (NadelPrincipalizationAffineChart.structureMap f U)
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n
      ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
        (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite)
      (NadelPrincipalizationRoundedRestriction.affineTotalTransform_isSnc f hp n I hI U) q := by
  let := global_smooth f hp n I hI
  let : IsProper (NadelPrincipalization.sequence f hp n I hI).composite :=
    NadelPrincipalization.composite_isProper f hp n I hI
  let : Smooth ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) :=
    SmoothOfRelativeDimension.smooth n _
  let := NadelPrincipalizationAffineChart.structureMap_smoothOfRelativeDimension f n U
  let := affineLast_smooth f hp n I hI U
  let := NadelPrincipalizationRestriction.lastMap_isOpenImmersion f hp n I hI U
  let : QuasiCompact (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite :=
    MorphismProperty.of_isPullback (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U) inferInstance
  let : SmoothOfRelativeDimension n (NadelPrincipalizationAffineChart.map f U ≫ f) :=
    smooth_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U) n
  let : SmoothOfRelativeDimension n
      ((NadelPrincipalizationRestriction.affineSequence f n I hI U).composite ≫
        (NadelPrincipalizationAffineChart.map f U ≫ f)) :=
    smooth_transport _ _ (congrArg (fun a =>
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite ≫ a)
        (NadelPrincipalizationAffineChart.map_structure f U)) n
  have hk := NadelPrincipalizationRelativeKernel.kernel_comap f
    (NadelPrincipalizationAffineChart.map f U)
    (NadelPrincipalization.sequence f hp n I hI).composite
    (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite
    (NadelPrincipalizationRestriction.lastMap f hp n I hI U)
    (NadelPrincipalizationRestriction.last_isPullback f hp n I hI U).flip n
    (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
    (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q
  exact hk.trans (kernel_transport _ _ (NadelPrincipalizationAffineChart.map_structure f U)
    (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n _ _
    (NadelPrincipalizationRestriction.totalTransform_comap f hp n I hI U) _
    (NadelPrincipalizationRoundedRestriction.affineTotalTransform_isSnc f hp n I hI U) q)


end EnvelopeProperty.Vanishing.NadelPrincipalizationKernelRestriction
