import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeCoordinateBaseLinearBridge
import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationNativeTensorGlobalSections
import EnvelopeProperty.Projective.TestConfigurationSectionTransport

/-! # Original base-linear whole sections in every native tensor degree

Every higher comparison is constructed from the genuine original scheme
and degree-one module isomorphisms, using the original tensorators.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open EnvelopeProperty.CanonicalGeometry
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (M : MultiModel k K 1) (j : Fin (M.M 0 + 1)) {X : Scheme.{u}}
  (e : X ≅ M.nativeRankOneScheme) (p : X ⟶ Spec (CommRingCat.of k))
  (h : e.hom ≫ M.nativeRankOneStructure = p) (P : X.Modules)
  (a : (Scheme.Modules.pullback e.hom).obj (M.nativeRankOneCoordinateLine j) ≅ P)

/-- The same original degree-one module isomorphism supplies every actual tensor-power comparison. -/
def nativeCoordinatePowerPullbackIso (m : ℕ) :
    (Scheme.Modules.pullback e.hom).obj
        (bundleTensorPower (M.nativeRankOneCoordinateLine j) m) ≅ bundleTensorPower P m :=
  TestConfigurationSectionTransport.tensorPowerPullbackIso e.hom
      (M.nativeRankOneCoordinateLine j) m ≪≫
    TestConfigurationSectionTransport.tensorPowerIso a m

/-- The genuine whole H0 comparison preserves the actual structural k-actions in every degree. -/
def nativeCoordinatePowerH0LinearEquiv (m : ℕ) :
    letI := M.nativeRankOneTensorH0BaseModule j m
    letI := structureH0BaseModule p (bundleTensorPower P m)
    Γ(bundleTensorPower (M.nativeRankOneCoordinateLine j) m, ⊤) ≃ₗ[k]
      Γ(bundleTensorPower P m, ⊤) :=
  isoLineBaseSectionsLinearEquiv e p M.nativeRankOneStructure h
    (bundleTensorPower (M.nativeRankOneCoordinateLine j) m) (bundleTensorPower P m)
    (nativeCoordinatePowerPullbackIso M j e P a m)

/-- Every original forward value is the literal whole-section comparison through the actual power iso. -/
theorem nativeCoordinatePowerH0LinearEquiv_apply (m : ℕ)
    (s : Γ(bundleTensorPower (M.nativeRankOneCoordinateLine j) m, ⊤)) :
    nativeCoordinatePowerH0LinearEquiv M j e p h P a m s =
      ((isoPullbackTopSections e (bundleTensorPower (M.nativeRankOneCoordinateLine j) m)).symm ≪≫
        asIso ((nativeCoordinatePowerPullbackIso M j e P a m).hom.app ⊤)).hom s := rfl

/-- Every original inverse value is the literal inverse whole-section comparison. -/
theorem nativeCoordinatePowerH0LinearEquiv_symm_apply (m : ℕ)
    (s : Γ(bundleTensorPower P m, ⊤)) :
    (nativeCoordinatePowerH0LinearEquiv M j e p h P a m).symm s =
      ((isoPullbackTopSections e (bundleTensorPower (M.nativeRankOneCoordinateLine j) m)).symm ≪≫
        asIso ((nativeCoordinatePowerPullbackIso M j e P a m).hom.app ⊤)).inv s := rfl

/-- Whole original power sections are the full all-chart original saturated power space over actual k. -/
def nativeCoordinatePowerSaturatedH0LinearEquiv (c : M.ChartIndex)
    (hc : ∀ l, M.coord l (c l) ≠ 0) (hj : M.coord 0 j ≠ 0) (m : ℕ) :
    letI := structureH0BaseModule p (bundleTensorPower P m)
    Γ(bundleTensorPower P m, ⊤) ≃ₗ[k] M.sections (m • (1 : Fin 1 → ℤ)) := by
  letI := M.nativeRankOneTensorH0BaseModule j m
  exact (nativeCoordinatePowerH0LinearEquiv M j e p h P a m).symm.trans
    (M.nativeRankOneTensorH0OriginalSectionsLinearEquiv c hc j hj m)

/-- Its value is precisely the original native tensor coefficient of the SAME inverse H0 section. -/
theorem nativeCoordinatePowerSaturatedH0LinearEquiv_coefficient (c : M.ChartIndex)
    (hc : ∀ l, M.coord l (c l) ≠ 0) (hj : M.coord 0 j ≠ 0) (m : ℕ)
    (s : Γ(bundleTensorPower P m, ⊤)) :
    (nativeCoordinatePowerSaturatedH0LinearEquiv M j e p h P a c hc hj m s : K) =
      M.nativeRankOneTensorGlobalSectionCoefficient c hc j hj m
        ((nativeCoordinatePowerH0LinearEquiv M j e p h P a m).symm s) := rfl

end EnvelopeProperty.ClosedProjectiveGlobalSections
