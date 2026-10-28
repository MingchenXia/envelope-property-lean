import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionCompatibility
import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSectionPowerCoherence
import EnvelopeProperty.AlgGeom.SchemeOpenCoverModuleMorphismCompatibility

/-! # The actual tautological root of the original line section -/
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.CyclicSectionGlobalCoverRootSection
open CanonicalGeometry CyclicSectionGlobalCover CyclicSectionGlobalCoverGluing
open CyclicSectionGlobalCoverRootSectionLocal CyclicSectionGlobalCoverRootSectionPowers
open CyclicSectionGlobalCoverRootSectionPowerCoherence SchemeLineSectionEvaluation
open SchemeGlobalSectionTensorPowerNorms BundleTensorPowerPullback
open SchemeOpenCoverModuleMorphismCompatibility

/-- Pullback of the SAME original whole section through an actual factor triangle. -/
theorem factorSection_pullback {X Y W : Scheme.{u}} (L : X.Modules)
    (i : W ⟶ Y) (b : Y ⟶ X) (g : W ⟶ X) (hi : i ≫ b = g)
    (α : unitObj X ⟶ L) :
    factorSection L i b g hi (pullbackSectionHom b α) = pullbackSectionHom g α := by
  subst g
  simpa only [factorSection, frameFactorIso, Iso.trans_hom, Iso.app_hom,
    show (pullbackCongr (rfl : i ≫ b = i ≫ b)).hom.app L = 𝟙 _ from rfl, Category.comp_id]
    using pullbackSectionHom_comp i b α

variable {X : Scheme.{u}} (L : X.Modules) (n : ℕ) (s : unitObj X ⟶ bundleTensorPower L n)

/-- The actual chart root retains the original quotient coordinate in the original pulled frame. -/
theorem chartRoot_coefficient (c : FramedOpen L) :
    chartRoot L n s c ≫ (chartComparison L n s c).hom ≫ (localFrame L n s c).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (CyclicSectionGlobalCoverRootSectionCoordinates.rootCoordinate c.1.toScheme n
        (CyclicSectionGlobalCoverGluing.coefficient L n s c)) := by
  simp only [chartRoot, Category.assoc, Iso.inv_hom_id_assoc]
  exact localRoot_coefficient L n s c

private theorem chartRootHom_factor {c d : FramedOpen L} (h : c ⟶ d) :
    (frameFactorIso (chartMap L n s h) (chartι L n s d) (chartι L n s c)
      (chartMap_chartι L n s h) (unitObj (rawCover L n s))).inv ≫
        (pullback (chartMap L n s h)).map (chartRootHom L n s d) ≫
      (frameFactorIso (chartMap L n s h) (chartι L n s d) (chartι L n s c)
        (chartMap_chartι L n s h) (pulledLine L n s)).hom = chartRootHom L n s c := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun q => (frameFactorIso (chartMap L n s h) (chartι L n s d)
      (chartι L n s c) (chartMap_chartι L n s h) (unitObj (rawCover L n s))).inv ≫ q)
      (chartRootHom_naturality L n s h)

/-- The SAME original section, pulled to the actual raw cover and its actual pulled line-power. -/
def pulledSection : unitObj (rawCover L n s) ⟶ bundleTensorPower (pulledLine L n s) n :=
  pullbackSectionHom (rawProjection L n s) s ≫ (pullbackIso (rawProjection L n s) L n).hom

/-- The chart root power equals the restriction of the SAME actual globally pulled original section. -/
theorem chartRoot_power (c : FramedOpen L) :
    powerSectionHom (chartRoot L n s c) n =
      pullbackSectionHom (chartι L n s c) (pulledSection L n s) ≫
        (pullbackIso (chartι L n s c) (pulledLine L n s) n).hom := by
  apply (cancel_mono (powerIso (chartComparison L n s c) n).hom).mp
  rw [powerSectionHom_iso]
  have hr : chartRoot L n s c ≫ (chartComparison L n s c).hom = localRoot L n s c := by
    simp only [chartRoot, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  have hc := congrArg Iso.hom (pullbackIso_factor L (chartι L n s c) (rawProjection L n s)
    (localBase L n s c) (chartι_projection L n s c) n)
  change (pullback (chartι L n s c)).map (pullbackIso (rawProjection L n s) L n).hom ≫
      (pullbackIso (chartι L n s c) (pulledLine L n s) n).hom ≫
      (powerIso (chartComparison L n s c) n).hom =
    (frameFactorIso (chartι L n s c) (rawProjection L n s) (localBase L n s c)
      (chartι_projection L n s c) (bundleTensorPower L n)).hom ≫
      (pullbackIso (localBase L n s c) L n).hom at hc
  simp only [pulledSection, pullbackSectionHom, Functor.map_comp, Category.assoc]
  rw [hc]
  have hs := factorSection_pullback (bundleTensorPower L n) (chartι L n s c)
    (rawProjection L n s) (localBase L n s c) (chartι_projection L n s c) s
  have h := congrArg (fun τ => τ ≫ (pullbackIso (localBase L n s c) L n).hom) hs
  rw [← localRoot_power] at h
  simpa only [factorSection, pullbackSectionHom, Functor.map_comp, Category.assoc] using h.symm

private theorem power_eq_pulledSection_of_chartRestriction
    (τ : unitObj (rawCover L n s) ⟶ pulledLine L n s)
    (hτ : ∀ c : FramedOpen L, pullbackSectionHom (chartι L n s c) τ = chartRoot L n s c) :
    powerSectionHom τ n = pulledSection L n s := by
  apply SchemeModuleOpenCoverDetection.hom_ext (chart L n s) (chartι L n s)
    (chartι_jointly_surjective L n s)
  intro c
  apply (cancel_epi (pullbackUnitIso (chartι L n s c)).inv).mp
  apply (cancel_mono (pullbackIso (chartι L n s c) (pulledLine L n s) n).hom).mp
  change pullbackSectionHom (chartι L n s c) (powerSectionHom τ n) ≫
    (pullbackIso (chartι L n s c) (pulledLine L n s) n).hom =
      pullbackSectionHom (chartι L n s c) (pulledSection L n s) ≫
        (pullbackIso (chartι L n s c) (pulledLine L n s) n).hom
  rw [pullback_powerSectionHom, hτ]
  exact chartRoot_power L n s c

private theorem chartRootHom_matching :
    NativeMatching (chart L n s) (chartι L n s) (unitObj (rawCover L n s))
      (pulledLine L n s) (chartRootHom L n s) := by
  refine nativeMatching_of_cartesian (chart L n s) (chartι L n s)
    (unitObj (rawCover L n s)) (pulledLine L n s) (chartRootHom L n s)
    (fun c d => chart L n s (intersection L c d))
    (fun c d => chartMap L n s (intersectionLeft L c d))
    (fun c d => chartMap L n s (intersectionRight L c d))
    (fun c d => chartι L n s (intersection L c d))
    (fun c d => chartMap_chartι L n s (intersectionLeft L c d))
    (fun c d => chartMap_chartι L n s (intersectionRight L c d))
    (chartIntersection_isPullback L n s) ?_
  intro c d
  exact (chartRootHom_factor L n s (intersectionLeft L c d)).trans
    (chartRootHom_factor L n s (intersectionRight L c d)).symm

/-- The actual tautological section of the SAME original line pulled to its actual raw cover. -/
def tautologicalRoot : unitObj (rawCover L n s) ⟶ pulledLine L n s :=
  glueHomOfMatching (chart L n s) (chartι L n s) (chartι_jointly_surjective L n s)
    (unitObj (rawCover L n s)) (pulledLine L n s) (chartRootHom L n s)
    (chartRootHom_matching L n s)

/-- Every actual chart restriction is exactly its original line-valued quotient root. -/
theorem tautologicalRoot_on_chart (c : FramedOpen L) :
    pullbackSectionHom (chartι L n s c) (tautologicalRoot L n s) = chartRoot L n s c := by
  simp only [pullbackSectionHom, tautologicalRoot, pullback_glueHomOfMatching,
    chartRootHom, Iso.inv_hom_id_assoc]

/-- The global root has the actual original quotient-root coefficient in every original chart. -/
theorem tautologicalRoot_coefficient (c : FramedOpen L) :
    pullbackSectionHom (chartι L n s c) (tautologicalRoot L n s) ≫
      (chartComparison L n s c).hom ≫ (localFrame L n s c).hom =
        ModularCurves.unitEndomorphismOfTopSection
          (CyclicSectionGlobalCoverRootSectionCoordinates.rootCoordinate c.1.toScheme n
            (CyclicSectionGlobalCoverGluing.coefficient L n s c)) := by
  rw [tautologicalRoot_on_chart]
  exact chartRoot_coefficient L n s c

/-- Its actual native tensor power is the pullback of the SAME original section. -/
theorem tautologicalRoot_power :
    powerSectionHom (tautologicalRoot L n s) n = pulledSection L n s :=
  power_eq_pulledSection_of_chartRestriction L n s (tautologicalRoot L n s)
    (tautologicalRoot_on_chart L n s)

end EnvelopeProperty.CyclicSectionGlobalCoverRootSection
