import EnvelopeProperty.Vanishing.NadelPrincipalizationRestriction
import EnvelopeProperty.Vanishing.NadelPrincipalizationRoundedRestrictionCore

/-! # The original global BP relative-rounded module on its actual affine BP

The original whole canonical objects and original rounded ideal inclusion
are retained; every field and total-transform transport is produced by
the actual principalization restriction, rather than supplied as a premise.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRoundedRestriction

open Char0.RoundedCanonicalModule

set_option backward.isDefEq.respectTransparency false

private def relativeTransport {k : Type u} [Field k] {X Y : Scheme.{u}}
    {f f' : X ⟶ Spec (.of k)} (e : f = f') (p : Y ⟶ X) (n : ℕ) :
    relative f p n ≅ relative f' p n :=
  eqToIso (congrArg (fun t => relative t p n) e)

private def roundedTransport {k : Type u} [Field k] {X Y : Scheme.{u}}
    {f f' : X ⟶ Spec (.of k)} (e : f = f') (p : Y ⟶ X) (n : ℕ)
    {J J' : Y.IdealSheafData} (eJ : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ) :
    relativeRounded f p n J hJ q ≅ relativeRounded f' p n J' hJ' q := by
  subst f'
  subst J'
  exact Iso.refl _

private theorem roundedTransport_inclusion {k : Type u} [Field k] {X Y : Scheme.{u}}
    {f f' : X ⟶ Spec (.of k)} (e : f = f') (p : Y ⟶ X) (n : ℕ)
    {J J' : Y.IdealSheafData} (eJ : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ) :
    (roundedTransport e p n eJ hJ hJ' q).hom ≫ relativeRoundedInclusion f' p n J' hJ' q =
      relativeRoundedInclusion f p n J hJ q ≫ (relativeTransport e p n).hom := by
  subst f'
  subst J'
  simp [roundedTransport, relativeTransport]

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (U : X.affineOpens) [Nonempty U.1]

private theorem originalLast_smooth : Smooth ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) := by
  let : SmoothOfRelativeDimension n ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f) :=
    NadelPrincipalization.stage_smoothOfRelativeDimension f hp n I hI (Fin.last _)
  exact SmoothOfRelativeDimension.smooth n _

include hp in
/-- The same actual affine total transform is SNC, derived through its
actual original global total-transform restriction. -/
theorem affineTotalTransform_isSnc :
    ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite).IsIdealOfSncDivisor := by
  let := originalLast_smooth f hp n I hI
  let := NadelPrincipalizationRestriction.lastMap_isOpenImmersion f hp n I hI U
  have h := (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI).comap_of_smooth
    ((NadelPrincipalization.sequence f hp n I hI).composite ≫ f)
    (NadelPrincipalizationRestriction.lastMap f hp n I hI U)
  rw [NadelPrincipalizationRestriction.totalTransform_comap f hp n I hI U] at h
  exact h

/-- The whole original relative canonical module restricts to the same
actual affine BP and original affine structural field map. -/
def relativeIso :
    (Scheme.Modules.pullback (NadelPrincipalizationRestriction.lastMap f hp n I hI U)).obj
        (relative f (NadelPrincipalization.sequence f hp n I hI).composite n) ≅
      relative (NadelPrincipalizationAffineChart.structureMap f U)
        (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n := by
  let := NadelPrincipalizationRestriction.lastMap_isOpenImmersion f hp n I hI U
  exact NadelPrincipalizationRoundedRestrictionCore.relativeIso f
      (NadelPrincipalization.sequence f hp n I hI).composite
      (NadelPrincipalizationAffineChart.map f U)
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite
      (NadelPrincipalizationRestriction.lastMap f hp n I hI U)
      (NadelPrincipalizationRestriction.lastMap_composite f hp n I hI U) n ≪≫
    relativeTransport (NadelPrincipalizationAffineChart.map_structure f U) _ n

/-- The SAME original whole relative-rounded canonical module restricts
to the SAME actual affine BP, ideal, field and rational exponent. -/
def roundedIso (q : ℚ) :
    (Scheme.Modules.pullback (NadelPrincipalizationRestriction.lastMap f hp n I hI U)).obj
        (relativeRounded f (NadelPrincipalization.sequence f hp n I hI).composite n
          (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
          (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q) ≅
      relativeRounded (NadelPrincipalizationAffineChart.structureMap f U)
        (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n
        ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
          (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite)
        (affineTotalTransform_isSnc f hp n I hI U) q := by
  let := originalLast_smooth f hp n I hI
  let := NadelPrincipalizationRestriction.lastMap_isOpenImmersion f hp n I hI U
  exact NadelPrincipalizationRoundedRestrictionCore.roundedIso f
      (NadelPrincipalization.sequence f hp n I hI).composite
      (NadelPrincipalizationAffineChart.map f U)
      (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite
      (NadelPrincipalizationRestriction.lastMap f hp n I hI U)
      (NadelPrincipalizationRestriction.lastMap_composite f hp n I hI U) n
      (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
      (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q ≪≫
    roundedTransport (NadelPrincipalizationAffineChart.map_structure f U) _ n
      (NadelPrincipalizationRestriction.totalTransform_comap f hp n I hI U) _
      (affineTotalTransform_isSnc f hp n I hI U) q

/-- The entire SAME original rounded inclusion commutes on the actual
affine BP with the original whole relative canonical comparison. -/
theorem roundedIso_inclusion (q : ℚ) :
    (roundedIso f hp n I hI U q).hom ≫
        relativeRoundedInclusion (NadelPrincipalizationAffineChart.structureMap f U)
          (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite n
          ((specIdealSheaf (NadelPrincipalizationAffineChart.ideal f I U)).comap
            (NadelPrincipalizationRestriction.affineSequence f n I hI U).composite)
          (affineTotalTransform_isSnc f hp n I hI U) q =
      (Scheme.Modules.pullback (NadelPrincipalizationRestriction.lastMap f hp n I hI U)).map
          (relativeRoundedInclusion f (NadelPrincipalization.sequence f hp n I hI).composite n
            (I.comap (NadelPrincipalization.sequence f hp n I hI).composite)
            (NadelPrincipalization.totalTransform_isIdealOfSncDivisor f hp n I hI) q) ≫
        (relativeIso f hp n I hI U).hom := by
  let := originalLast_smooth f hp n I hI
  let := NadelPrincipalizationRestriction.lastMap_isOpenImmersion f hp n I hI U
  simp only [roundedIso, relativeIso, Iso.trans_hom, Category.assoc]
  rw [roundedTransport_inclusion]
  rw [← Category.assoc,
    NadelPrincipalizationRoundedRestrictionCore.roundedIso_inclusion, Category.assoc]

end EnvelopeProperty.Vanishing.NadelPrincipalizationRoundedRestriction
