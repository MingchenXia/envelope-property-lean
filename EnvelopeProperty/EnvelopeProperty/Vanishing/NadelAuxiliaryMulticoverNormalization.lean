import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverRoots
import EnvelopeProperty.Berkovich.SchemeIntegralNormalization
import Mathlib.AlgebraicGeometry.Normalization

/-! # Native normalization in the WHOLE original base-generic fibre

Only the original base is integral. The entire literal finite multicover
is base changed to its original function field; no component is chosen.
The native relative normalization is taken for that whole generic-fibre
projection into the original raw multicover, rather than for the already
integral raw projection to X. No finite-normalization or smoothness input
is introduced, and neither conclusion is asserted here.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover

open Scheme.Modules CanonicalGeometry
open SchemeLineSectionEvaluation SchemeGlobalSectionTensorPowerNorms BundleTensorPowerPullback

variable {X : Scheme.{u}} [IsIntegral X]

/-- The ENTIRE actual base-generic fibre of the SAME whole raw multicover. -/
abbrev genericFiber (D : List (AuxiliarySection X)) : Scheme.{u} :=
  Limits.pullback (projection D) (IntegralSchemeNormalization.genericMap X)

/-- The actual whole generic-fibre projection whose native normalization
retains the original raw multicover as its target. -/
def genericProjection (D : List (AuxiliarySection X)) : genericFiber D ⟶ rawScheme D :=
  Limits.pullback.fst _ _

/-- The other actual projection retains the original function-field spectrum. -/
def genericToBase (D : List (AuxiliarySection X)) : genericFiber D ⟶ Spec X.functionField :=
  Limits.pullback.snd _ _

/-- This is the literal native pullback of the SAME original generic-stalk map. -/
theorem generic_isPullback (D : List (AuxiliarySection X)) :
    IsPullback (genericProjection D) (genericToBase D)
      (projection D) (IntegralSchemeNormalization.genericMap X) :=
  IsPullback.of_hasPullback _ _

/-- The original whole base-generic projection triangle, before normalization. -/
theorem genericProjection_over (D : List (AuxiliarySection X)) :
    genericProjection D ≫ projection D = genericToBase D ≫ IntegralSchemeNormalization.genericMap X :=
  Limits.pullback.condition

/-- Quasi-compactness follows from the ACTUAL original base-generic map. -/
theorem genericProjection_quasiCompact (D : List (AuxiliarySection X)) :
    QuasiCompact (genericProjection D) := by
  let := IntegralSchemeNormalization.genericMap_quasiCompact X
  exact inferInstanceAs (QuasiCompact
    (Limits.pullback.fst (projection D) (IntegralSchemeNormalization.genericMap X)))

/-- Quasi-separatedness follows from the ACTUAL original base-generic map. -/
theorem genericProjection_quasiSeparated (D : List (AuxiliarySection X)) :
    QuasiSeparated (genericProjection D) := by
  let := IntegralSchemeNormalization.genericMap_quasiSeparated X
  exact inferInstanceAs (QuasiSeparated
    (Limits.pullback.fst (projection D) (IntegralSchemeNormalization.genericMap X)))

attribute [local instance] genericProjection_quasiCompact genericProjection_quasiSeparated

/-- Native relative normalization in the ENTIRE base-generic fibre.
This definition does not claim normality, finiteness or smoothness. -/
abbrev normalizedScheme (D : List (AuxiliarySection X)) : Scheme.{u} :=
  (genericProjection D).normalization

/-- The actual native integral normalization projection to the SAME raw multicover. -/
abbrev normalizationProjection (D : List (AuxiliarySection X)) : normalizedScheme D ⟶ rawScheme D :=
  (genericProjection D).fromNormalization

/-- The entire original base-generic fibre has its actual native generic lift. -/
abbrev normalizationGenericLift (D : List (AuxiliarySection X)) : genericFiber D ⟶ normalizedScheme D :=
  (genericProjection D).toNormalization

/-- The native whole generic lift and projection compose to exactly
the SAME original whole generic-fibre morphism. -/
theorem normalizationGenericLift_projection (D : List (AuxiliarySection X)) :
    normalizationGenericLift D ≫ normalizationProjection D = genericProjection D :=
  (genericProjection D).toNormalization_fromNormalization

/-- The SAME actual normalization projection is integral by the native theorem. -/
theorem normalizationProjection_integral (D : List (AuxiliarySection X)) :
    IsIntegralHom (normalizationProjection D) := inferInstance

/-- The actual original-X structure of the entire native normalization. -/
def normalizedToOriginal (D : List (AuxiliarySection X)) : normalizedScheme D ⟶ X :=
  normalizationProjection D ≫ projection D

/-- The whole original-X projection is integral, from the actual finite
raw projection and the ACTUAL native integral normalization projection. -/
theorem normalizedToOriginal_integral (D : List (AuxiliarySection X))
    (hL : ∀ E ∈ D, IsInvertible E.line) (hN : ∀ E ∈ D, 0 < E.degree) :
    IsIntegralHom (normalizedToOriginal D) := by
  let := projection_finite D hL hN
  let := normalizationProjection_integral D
  change IsIntegralHom (normalizationProjection D ≫ projection D)
  infer_instance

/-- EVERY original raw cyclic factor is retained after native whole normalization. -/
def normalizedFactorMap (D : List (AuxiliarySection X)) (i : Fin D.length) :
    normalizedScheme D ⟶ factorCover (D.get i) :=
  normalizationProjection D ≫ factorMap D i

/-- Every whole normalized factor still lies over the SAME original X. -/
theorem normalizedFactorMap_over (D : List (AuxiliarySection X)) (i : Fin D.length) :
    normalizedFactorMap D i ≫ factorProjection (D.get i) = normalizedToOriginal D := by
  rw [normalizedFactorMap, Category.assoc, factorMap_over]
  rfl

/-- The SAME original line at EVERY original list position on the
entire native generic-normalization object. -/
def normalizedLine (D : List (AuxiliarySection X)) (i : Fin D.length) : (normalizedScheme D).Modules :=
  (Scheme.Modules.pullback (normalizedToOriginal D)).obj (D.get i).line

/-- The original section on that SAME whole normalized pulled line-power. -/
def normalizedSectionPower (D : List (AuxiliarySection X)) (i : Fin D.length) :
    unitObj (normalizedScheme D) ⟶ bundleTensorPower (normalizedLine D i) (D.get i).degree :=
  pullbackSectionHom (normalizedToOriginal D) (D.get i).sectionHom ≫
    (pullbackIso (normalizedToOriginal D) (D.get i).line (D.get i).degree).hom

/-- The actual original root, genuinely retained on the whole native
normalization via the actual original factor triangle. -/
def normalizedRoot (D : List (AuxiliarySection X)) (i : Fin D.length) :
    unitObj (normalizedScheme D) ⟶ normalizedLine D i :=
  transportedRoot (D.get i) (normalizedFactorMap D i) (normalizedToOriginal D)
    (normalizedFactorMap_over D i)

/-- Its genuine original native power is exactly the SAME original
section pulled to the ENTIRE native generic-normalization object. -/
theorem normalizedRoot_power (D : List (AuxiliarySection X)) (i : Fin D.length) :
    powerSectionHom (normalizedRoot D i) (D.get i).degree = normalizedSectionPower D i :=
  transportedRoot_power (D.get i) (normalizedFactorMap D i) (normalizedToOriginal D)
    (normalizedFactorMap_over D i)

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover
