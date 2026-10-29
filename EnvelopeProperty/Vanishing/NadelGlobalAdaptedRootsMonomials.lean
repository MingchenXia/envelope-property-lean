import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsModel
import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverChartsFactors

/-! # Actual normalized root sections in their original ratio-chart frames

The native tautological section, actual cyclic chart, whole quotient factor
map, and canonical normalization triangle determine every section coefficient.
No expected section value or root-matching certificate is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching
open SchemeLineSectionEvaluation CyclicSectionGlobalCoverRootSection
open CyclicSectionGlobalCoverRootSectionLocal

private def transportedRootPullbackIso {X T V : Scheme.{u}}
    (E : AuxiliarySection X) (t : T ⟶ factorCover E) (π : T ⟶ X)
    (ht : t ≫ factorProjection E = π) (i : V ⟶ T) :
    (pullback i).obj ((pullback π).obj E.line) ≅
      (pullback (i ≫ t)).obj ((pullback (factorProjection E)).obj E.line) :=
  (pullback i).mapIso (frameFactorIso t (factorProjection E) π ht E.line).symm ≪≫
    (pullbackComp i t).app ((pullback (factorProjection E)).obj E.line)

private theorem transportedRoot_pullback {X T V : Scheme.{u}}
    (E : AuxiliarySection X) (t : T ⟶ factorCover E) (π : T ⟶ X)
    (ht : t ≫ factorProjection E = π) (i : V ⟶ T) :
    pullbackSectionHom i (transportedRoot E t π ht) ≫
        (transportedRootPullbackIso E t π ht i).hom =
      pullbackSectionHom (i ≫ t)
        (tautologicalRoot E.line E.degree E.sectionHom) := by
  let τ : unitObj (factorCover E) ⟶
      (pullback (factorProjection E)).obj E.line :=
    tautologicalRoot E.line E.degree E.sectionHom
  change pullbackSectionHom i
      (pullbackSectionHom t τ ≫
        (frameFactorIso t (factorProjection E) π ht E.line).hom) ≫
      ((pullback i).map (frameFactorIso t (factorProjection E) π ht E.line).inv ≫
        (pullbackComp i t).hom.app ((pullback (factorProjection E)).obj E.line)) =
    pullbackSectionHom (i ≫ t) τ
  simp only [pullbackSectionHom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← (pullback i).map_comp_assoc
      (frameFactorIso t (factorProjection E) π ht E.line).hom
      (frameFactorIso t (factorProjection E) π ht E.line).inv,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hc := pullbackSectionHom_comp i t
    (M := (pullback (factorProjection E)).obj E.line) τ
  simpa only [pullbackSectionHom, CategoryTheory.Functor.map_comp, Category.assoc] using hc

section RawChart
variable {X : Scheme.{u}} (U : X.affineOpens) (D : List (AuxiliarySection X))
  (e : NadelAuxiliaryMulticoverCharts.Frames U.1 D)
local instance rawBaseAffine : IsAffine U.1.toScheme := U.2

/-- The SAME actual whole raw chart retains every original cyclic factor. -/
theorem rawChart_factor (i : Fin (D).length) :
    NadelGlobalNormalization.RawChart.map U D e ≫ factorMap D i =
      Spec.map (NadelAuxiliaryMulticoverCharts.factorRingMap U.1 D e i ≫
        CommRingCat.ofHom (WholeChart.ringEquiv U D e).toRingHom) ≫
          NadelAuxiliaryMulticoverCharts.singleMap U.1 ((D).get i) (e i) := by
  let : IsAffine U.1.toScheme := U.2
  change (Spec.map (CommRingCat.ofHom (WholeChart.ringEquiv U D e).toRingHom) ≫
    NadelAuxiliaryMulticoverCharts.chartMap U.1 D e) ≫ factorMap D i = _
  rw [Category.assoc, NadelAuxiliaryMulticoverCharts.chartMap_factor,
    ← Category.assoc, ← Spec.map_comp]

private theorem singleRoot_coordinate {B : CommRingCat.{u}}
    (E : AuxiliarySection X) (eE : NadelAuxiliaryMulticoverCharts.Frame U.1 E)
    (a : CommRingCat.of (CyclicSectionAlgebra.RootRing E.degree
      (NadelAuxiliaryMulticoverCharts.coefficient U.1 E eE)) ⟶ B) :
    (Spec.map a ≫ (NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).inv).appTop
        (CyclicSectionGlobalCoverRootSectionCoordinates.rootCoordinate U.1.toScheme E.degree
          (NadelAuxiliaryMulticoverCharts.coefficient U.1 E eE)) =
      (Scheme.ΓSpecIso B).inv
        (a (CyclicSectionAlgebra.root E.degree
          (NadelAuxiliaryMulticoverCharts.coefficient U.1 E eE))) := by
  let : IsAffine U.1.toScheme := U.2
  rw [Scheme.Hom.comp_appTop]
  change (Spec.map a).appTop
    (((NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).hom.appTop ≫
      (NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).inv.appTop)
      ((Scheme.ΓSpecIso _).inv _)) = _
  have he :
      (NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).hom.appTop ≫
        (NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).inv.appTop = 𝟙 _ := by
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] using
      congrArg (fun q => q.appTop)
        (NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).inv_hom_id
  let R₀ : CommRingCat.{u} := .of (CyclicSectionAlgebra.RootRing E.degree
    (NadelAuxiliaryMulticoverCharts.coefficient U.1 E eE))
  let r₀ : R₀ := CyclicSectionAlgebra.root E.degree
    (NadelAuxiliaryMulticoverCharts.coefficient U.1 E eE)
  have hval :
      ((NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).hom.appTop ≫
        (NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 E eE).inv.appTop)
          ((Scheme.ΓSpecIso R₀).inv r₀) = (Scheme.ΓSpecIso R₀).inv r₀ :=
    congrArg (fun q : Γ(Spec R₀, ⊤) ⟶ Γ(Spec R₀, ⊤) =>
      q ((Scheme.ΓSpecIso R₀).inv r₀)) he
  have hn := congrArg (fun q : R₀ ⟶ Γ(Spec B, ⊤) => q r₀)
    (Scheme.ΓSpecIso_inv_naturality a)
  exact (congrArg (fun z : Γ(Spec R₀, ⊤) => (Spec.map a).appTop z) hval).trans hn.symm

end RawChart

section CanonicalChart
open NadelGlobalNormalization NadelGlobalAdaptedModel NadelMixedKummer
open CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  (y : X) (U : X.affineOpens) [Nonempty U.1] (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).component i).support} → Fin n)
  (j₀ : F.ι → Fin (n + 1))
  (w : Fin (OriginalData.data F n L m σ).length → (Γ(X, U.1))ˣ)
  {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
  (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
  (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).IsSnc)
  (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U = Ideal.span {v (c i)})
  (hyU : y ∈ U.1)
  (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
  (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
  (hw : ∀ i, WholeChart.coefficients U (OriginalData.data F n L m σ) e i =
    (w i : Γ(X, U.1)) * uniformBranches y U v c (OriginalData.branchIndex F n L m σ hL hD i) *
      uniformBranches y U v c (OriginalData.auxiliaryIndex F n L m σ hL hD i))

local instance canonicalBaseAffine : IsAffine U.1.toScheme := U.2
local notation "D" => OriginalData.data F n L m σ
local notation "B" => RatioRing F n L m σ hL hD y U v c j₀ w
local notation "π" => normalizedToOriginal D
local notation "α" => originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
local notation "C" => Model.canonicalChart F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw
private abbrev canonicalChartMap : Spec (.of B) ⟶ normalizedScheme D :=
  (C).hom ≫ (π ⁻¹ᵁ U.1).ι
local notation "φ" => canonicalChartMap F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw

private def factorScalarMap (a : Fin (D).length) :
    CommRingCat.of (CyclicSectionAlgebra.RootRing ((D).get a).degree
      (NadelAuxiliaryMulticoverCharts.coefficient U.1 ((D).get a) (e a))) ⟶ .of B :=
  NadelAuxiliaryMulticoverCharts.factorRingMap U.1 D e a ≫
    CommRingCat.ofHom (WholeChart.ringEquiv U D e).toRingHom ≫
      CommRingCat.ofHom (α).toRingHom

private theorem canonicalChart_factor (a : Fin (D).length) :
    (φ) ≫ normalizedFactorMap D a =
      Spec.map (factorScalarMap F n L m σ hL hD y U v c j₀ w habsent e hw a) ≫
        NadelAuxiliaryMulticoverCharts.singleMap U.1 ((D).get a) (e a) := by
  calc
    _ = ((C).hom ≫ (π ⁻¹ᵁ U.1).ι ≫ normalizationProjection D) ≫ factorMap D a := by
      simp only [normalizedFactorMap, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom (α).toRingHom) ≫ RawChart.map U D e) ≫
        factorMap D a := congrArg (fun z => z ≫ factorMap D a)
      (Model.canonicalChart_over_raw F n L m σ hL hD y U v c j₀ w
        f het hcinj hm htame hG hcomp hyU habsent e hw)
    _ = _ := by
      rw [Category.assoc, rawChart_factor, ← Category.assoc, ← Spec.map_comp]
      simp only [factorScalarMap, Category.assoc]

private def factorChartMap (a : Fin (D).length) : Spec (.of B) ⟶
    CyclicSectionGlobalCoverGluing.chart ((D).get a).line ((D).get a).degree
      ((D).get a).sectionHom ⟨U.1, e a⟩ :=
  Spec.map (factorScalarMap F n L m σ hL hD y U v c j₀ w habsent e hw a) ≫
    (NadelAuxiliaryMulticoverCharts.scalarRootIso U.1 ((D).get a) (e a)).inv

private theorem factorChartMap_triangle (a : Fin (D).length) :
    factorChartMap F n L m σ hL hD y U v c j₀ w habsent e hw a ≫
        CyclicSectionGlobalCoverGluing.chartι ((D).get a).line ((D).get a).degree
          ((D).get a).sectionHom ⟨U.1, e a⟩ =
      (φ) ≫ normalizedFactorMap D a := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc]
  exact (canonicalChart_factor F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU habsent e hw a).symm

/-- The actual pulled original line frame on the SAME canonical normalized
chart. It uses only native structural comparisons and the original frame;
it is independent of any proposed root value. -/
def canonicalRootFrame (a : Fin (D).length) :
    (pullback (φ)).obj (normalizedLine D a) ≅ unitObj (Spec (.of B)) :=
  transportedRootPullbackIso ((D).get a) (normalizedFactorMap D a) π
    (normalizedFactorMap_over D a) (φ) ≪≫
  frameViaFactor
    (factorChartMap F n L m σ hL hD y U v c j₀ w habsent e hw a)
    (CyclicSectionGlobalCoverGluing.chartι ((D).get a).line ((D).get a).degree
      ((D).get a).sectionHom ⟨U.1, e a⟩)
    ((φ) ≫ normalizedFactorMap D a)
    (factorChartMap_triangle F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU habsent e hw a)
    (chartComparison ((D).get a).line ((D).get a).degree ((D).get a).sectionHom ⟨U.1, e a⟩ ≪≫
      localFrame ((D).get a).line ((D).get a).degree ((D).get a).sectionHom ⟨U.1, e a⟩)

/-- Every SAME actual normalized root section has its proved original
quotient image in the actual pulled line frame, as an ENTIRE morphism. -/
theorem canonicalRoot_coefficient (a : Fin (D).length) :
    pullbackSectionHom (φ) (normalizedRoot D a) ≫
        (canonicalRootFrame F n L m σ hL hD y U v c j₀ w
          f het hcinj hm htame hG hcomp hyU habsent e hw a).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (.of B)).inv
          ((α) (NadelMixedKummer.root (OriginalChart.degree D) (WholeChart.coefficients U D e) a))) := by
  rw [canonicalRootFrame, Iso.trans_hom, ← Category.assoc, normalizedRoot,
    transportedRoot_pullback]
  have hs := frameViaFactor_sectionHom_scalar
    (factorChartMap F n L m σ hL hD y U v c j₀ w habsent e hw a)
    (CyclicSectionGlobalCoverGluing.chartι ((D).get a).line ((D).get a).degree
      ((D).get a).sectionHom ⟨U.1, e a⟩)
    ((φ) ≫ normalizedFactorMap D a)
    (factorChartMap_triangle F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU habsent e hw a)
    (chartComparison ((D).get a).line ((D).get a).degree ((D).get a).sectionHom ⟨U.1, e a⟩ ≪≫
      localFrame ((D).get a).line ((D).get a).degree ((D).get a).sectionHom ⟨U.1, e a⟩)
    (tautologicalRoot ((D).get a).line ((D).get a).degree ((D).get a).sectionHom)
    (CyclicSectionGlobalCoverRootSectionCoordinates.rootCoordinate U.1.toScheme ((D).get a).degree
      (NadelAuxiliaryMulticoverCharts.coefficient U.1 ((D).get a) (e a)))
    (by simpa only [NadelAuxiliaryMulticoverCharts.coefficient,
      Iso.trans_hom, Category.assoc] using
      tautologicalRoot_coefficient ((D).get a).line ((D).get a).degree ((D).get a).sectionHom ⟨U.1, e a⟩)
  rw [hs]
  have hc := singleRoot_coordinate U ((D).get a) (e a)
    (factorScalarMap F n L m σ hL hD y U v c j₀ w habsent e hw a)
  have hc' :
      (factorChartMap F n L m σ hL hD y U v c j₀ w habsent e hw a).appTop
          (CyclicSectionGlobalCoverRootSectionCoordinates.rootCoordinate U.1.toScheme
            ((D).get a).degree
            (NadelAuxiliaryMulticoverCharts.coefficient U.1 ((D).get a) (e a))) =
        (Scheme.ΓSpecIso (.of B)).inv
          ((factorScalarMap F n L m σ hL hD y U v c j₀ w habsent e hw a)
            (CyclicSectionAlgebra.root ((D).get a).degree
              (NadelAuxiliaryMulticoverCharts.coefficient U.1 ((D).get a) (e a)))) := by
    simpa only [factorChartMap, CyclicSectionGlobalCoverGluing.chart,
      NadelAuxiliaryMulticoverCharts.coefficient] using hc
  apply (congrArg
    (fun z : Γ(Spec (.of B), ⊤) => ModularCurves.unitEndomorphismOfTopSection z) hc').trans
  apply congrArg (fun z => ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso (.of B)).inv z))
  change (α) (WholeChart.ringEquiv U D e
    (NadelAuxiliaryMulticoverCharts.factorRingMap U.1 D e a
      (CyclicSectionAlgebra.root ((D).get a).degree
        (NadelAuxiliaryMulticoverCharts.coefficient U.1 ((D).get a) (e a))))) = _
  apply congrArg (α)
  exact (congrArg (WholeChart.ringEquiv U D e)
    (NadelAuxiliaryMulticoverCharts.factorRingMap_root U.1 D e a)).trans
      (WholeChart.ringEquiv_root U D e a)

/-- The distinguished SAME normalized original row root is the actual
branch root in its native pulled original line frame. -/
theorem canonicalRoot_head (i : F.ι) :
    pullbackSectionHom (φ) (normalizedRoot D (rowPosition F n L m σ i (j₀ i))) ≫
        (canonicalRootFrame F n L m σ hL hD y U v c j₀ w
          f het hcinj hm htame hG hcomp hyU habsent e hw
          (rowPosition F n L m σ i (j₀ i))).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (.of B)).inv
          (NadelMixedKummer.root (Joined.degree F n m)
            (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
            (Joined.ordering F n (i, j₀ i)))) := by
  rw [canonicalRoot_coefficient, originalToRatio_head_root]

/-- EVERY other SAME normalized original row root retains the entire
original ratio root, with no unit-root or component selection. -/
theorem canonicalRoot_other (i : F.ι) (j : Fin (n + 1)) (hj : j ≠ j₀ i) :
    pullbackSectionHom (φ) (normalizedRoot D (rowPosition F n L m σ i j)) ≫
        (canonicalRootFrame F n L m σ hL hD y U v c j₀ w
          f het hcinj hm htame hG hcomp hyU habsent e hw
          (rowPosition F n L m σ i j)).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (.of B)).inv
          (NadelMixedKummer.root (Joined.degree F n m)
              (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
              (Joined.ordering F n (i, j₀ i)) *
            NadelMixedKummer.root (Joined.degree F n m)
              (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
              (Joined.ordering F n (i, j)))) := by
  rw [canonicalRoot_coefficient, originalToRatio_other_root]
  exact hj

end CanonicalChart
end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
