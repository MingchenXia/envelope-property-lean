import BingWangEntropy.PolynomialProjectiveProper
import BingWangEntropy.SchemeAnalyticCountability
import BingWangEntropy.SchemeAnalyticSeparation
import BingWangEntropy.SchemeTangentEndomorphism
import BingWangEntropy.PolynomialProjectiveAnalyticCompactness
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Native smooth projective Fano geometric inputs

Projectivity is an actual closed immersion into the actual polynomial Proj
whose structural composite is the literal given structural morphism.
Anticanonical positivity is an actual positive tensor power of the genuine
dual exterior cotangent sheaf identified with the genuine pullback of O(1).
The data include no section dimension, entropy, measure or curvature result.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle
open scoped Topology ContDiff Bundle

namespace BingWangEntropy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A literal closed projective embedding over the actual structural map. -/
structure ClosedProjectiveEmbedding {X : Scheme} (f : X ⟶ Spec (.of ℂ)) where
  ambientDimension : ℕ
  map : X ⟶ polynomialProj ℂ ambientDimension
  closedImmersion : IsClosedImmersion map
  over_base : map ≫ polynomialProjStructureMap ℂ ambientDimension = f

attribute [instance] ClosedProjectiveEmbedding.closedImmersion

/-- Genuine projectivity produces native properness of the literal structural map. -/
theorem ClosedProjectiveEmbedding.isProper {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (e : ClosedProjectiveEmbedding f) : IsProper f := by
  rw [← e.over_base]
  infer_instance

/-- The literal projective structural map is separated. -/
theorem ClosedProjectiveEmbedding.isSeparated {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (e : ClosedProjectiveEmbedding f) : IsSeparated f := by
  let := e.isProper
  infer_instance

/-- The literal projective structural map is universally closed. -/
theorem ClosedProjectiveEmbedding.universallyClosed {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (e : ClosedProjectiveEmbedding f) : UniversallyClosed f := by
  let := e.isProper
  infer_instance

/-- The literal projective structural map is quasi-compact. -/
theorem ClosedProjectiveEmbedding.quasiCompact {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (e : ClosedProjectiveEmbedding f) : QuasiCompact f := by
  let := e.isProper
  infer_instance

/-- The literal projective structural map is locally of finite type. -/
theorem ClosedProjectiveEmbedding.locallyOfFiniteType {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (e : ClosedProjectiveEmbedding f) : LocallyOfFiniteType f := by
  let := e.isProper
  infer_instance

/-- Actual closed projectivity gives actual analytic Hausdorffness. -/
theorem ClosedProjectiveEmbedding.analyticT2 {X : Scheme} {f : X ⟶ Spec (.of ℂ)}
    (e : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticPointTopology f
    T2Space (SchemeComplexPoint f) := by
  let := e.isProper
  exact schemeAnalyticPoint_t2Space f

/-- Actual closed projectivity gives actual analytic second countability. -/
theorem ClosedProjectiveEmbedding.analyticSecondCountable {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticPointTopology f
    SecondCountableTopology (SchemeComplexPoint f) := by
  let := e.isProper
  exact schemeAnalyticPoint_secondCountable f

/-- Actual analytic compactness follows from the genuine projective unit-sphere producer. -/
theorem ClosedProjectiveEmbedding.analyticCompact {X : Scheme}
    {f : X ⟶ Spec (.of ℂ)} (e : ClosedProjectiveEmbedding f) :
    letI := schemeAnalyticPointTopology f
    CompactSpace (SchemeComplexPoint f) := by
  rw [← e.over_base]
  exact closedPolynomialProjComplexPoint_compactSpace e.ambientDimension e.map

/-- Native smooth integral projective geometry with concrete anticanonical ampleness. -/
structure SmoothProjectiveFano (n : ℕ) where
  scheme : Scheme
  structureMap : scheme ⟶ Spec (.of ℂ)
  integral : IsIntegral scheme
  smooth : SmoothOfRelativeDimension n structureMap
  projective : ClosedProjectiveEmbedding structureMap
  anticanonicalPower : ℕ
  anticanonicalPower_positive : 0 < anticanonicalPower
  positivityIso :
    bundleTensorPower (anticanonicalLineSheaf structureMap n) anticanonicalPower ≅
      (Scheme.Modules.pullback projective.map).obj
        (projectiveTwistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (projective.ambientDimension + 1)) ℂ) 1)

attribute [instance] SmoothProjectiveFano.integral SmoothProjectiveFano.smooth

/-- Properness is derived from the actual projective embedding of a Fano input. -/
theorem SmoothProjectiveFano.isProper {n : ℕ} (F : SmoothProjectiveFano n) :
    IsProper F.structureMap := F.projective.isProper

/-- The genuine smooth scheme charts give every native complex differentiability order. -/
theorem SmoothProjectiveFano.complexIsManifold {n : ℕ} (F : SmoothProjectiveFano n)
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology F.structureMap
    letI := smoothSchemeComplexChartedSpace F.structureMap n
    IsManifold 𝓘(ℂ, Fin n → ℂ) k (SchemeComplexPoint F.structureMap) :=
  smoothSchemeComplex_isManifold F.structureMap n k

/-- The genuine smooth scheme charts give every native real differentiability order. -/
theorem SmoothProjectiveFano.realIsManifold {n : ℕ} (F : SmoothProjectiveFano n)
    (k : WithTop ℕ∞) :
    letI := schemeAnalyticPointTopology F.structureMap
    letI := smoothSchemeComplexChartedSpace F.structureMap n
    IsManifold 𝓘(ℝ, Fin n → ℂ) k (SchemeComplexPoint F.structureMap) :=
  smoothSchemeReal_isManifold F.structureMap n k

/-- The genuine tangent imaginary operator is a smooth actual native Hom section. -/
theorem SmoothProjectiveFano.tangentJ_smooth {n : ℕ} (F : SmoothProjectiveFano n) :
    letI := schemeAnalyticPointTopology F.structureMap
    letI := smoothSchemeComplexChartedSpace F.structureMap n
    letI := smoothSchemeReal_isManifold F.structureMap n ∞
    ContMDiff 𝓘(ℝ, Fin n → ℂ)
      (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, (Fin n → ℂ) →L[ℝ] (Fin n → ℂ))) ∞
      (fun x => TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) x
        (smoothSchemeTangentJ F.structureMap n x)) :=
  smoothSchemeTangentJ_hom_contMDiff F.structureMap n

/-- Actual proper integral Fano inputs produce the actual global structural constants. -/
def SmoothProjectiveFano.globalConstantsRingEquiv {n : ℕ} (F : SmoothProjectiveFano n) :
    ℂ ≃+* Γ(F.scheme, ⊤) := by
  let := F.isProper
  exact schemeConstantsRingEquiv F.structureMap

/-- The actual degree-zero global space has dimension one in its actual structural algebra. -/
theorem SmoothProjectiveFano.globalSections_finrank {n : ℕ} (F : SmoothProjectiveFano n) :
    letI := schemeGlobalSectionsAlgebra F.structureMap
    Module.finrank ℂ Γ(F.scheme, ⊤) = 1 := by
  let := F.isProper
  exact schemeGlobalSections_finrank F.structureMap

end

end BingWangEntropy
