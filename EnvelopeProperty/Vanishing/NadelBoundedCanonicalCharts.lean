import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRoundedCharts
import EnvelopeProperty.Vanishing.NadelGlobalNormalizationOriginalRaw

/-! # The SAME canonical whole ratio chart retains the original projection

The existing public raw-chart triangle is composed with the actual original
raw projection. Original algebra commutativity supplies the exact Spec base
map. No over-original matching equality is an incoming premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalCharts
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelAdaptedChartMatching NadelGlobalAdaptedModel
open CyclicSectionSNCUniformFramedCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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


local instance canonicalBoundBaseAffine : IsAffine U.1.toScheme := U.2
local notation "D" => OriginalData.data F n L m σ
local notation "B" => RatioRing F n L m σ hL hD y U v c j₀ w
local notation "π" => normalizedToOriginal D
local notation "α" => originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
local notation "C" => Model.canonicalChart F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw

/-- The actual SAME whole normalized ratio chart lies over the SAME original
scheme through the original algebraMap. Its exact triangle is produced from
original raw projection coherence and actual algebra commutativity. -/
theorem canonicalChart_over_original :
    (C).hom ≫ (π ⁻¹ᵁ U.1).ι ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B)) ≫ U.2.fromSpec := by
  have hh := congrArg (fun z => z ≫ projection D)
    (Model.canonicalChart_over_raw F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU habsent e hw)
  calc
    _ = Spec.map (CommRingCat.ofHom (α).toRingHom) ≫
        (RawChart.baseMap U D e ≫ U.2.fromSpec) := by
      simpa only [normalizedToOriginal, Category.assoc, RawChart.map_over] using hh
    _ = _ := by
      rw [← Category.assoc]
      apply congrArg (fun z => z ≫ U.2.fromSpec)
      rw [RawChart.baseMap, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      ext a
      exact (α).commutes a

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalCharts
