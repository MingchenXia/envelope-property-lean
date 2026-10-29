import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRowIdeals
import EnvelopeProperty.AlgGeom.CartierAdmissibleModulePullback
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Regular.Basic

/-! # Actual regular head roots and the same whole row ideal's Cartier chart

Regularity is produced from the original Cartier divisor generators and the
proved flatness of the entire original ratio algebra. No regularity, Cartier,
or ideal-power conclusion for the normalized row ideal is supplied as input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped nonZeroDivisors
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching
open SchemeLineSectionEvaluation NadelAuxiliaryBranchSectionsSnc

private theorem flat_algebraMap_regular {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (r : R) (hr : r ∈ nonZeroDivisors R) :
    IsRegular (algebraMap R S r) := by
  have hc : ∀ s : S, algebraMap R S r * s = 0 → s = 0 := by
    intro s hs
    apply (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) hr).right_eq_zero_of_smul
    simpa only [Algebra.smul_def] using hs
  have hm : algebraMap R S r ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_iff.mpr ⟨hc, fun s hs => hc s (by rwa [mul_comm])⟩
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl (nonZeroDivisors S))
    ⟨algebraMap R S r, hm⟩

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

local instance cartierBaseAffine : IsAffine U.1.toScheme := U.2
local notation "D" => OriginalData.data F n L m σ
local notation "B" => RatioRing F n L m σ hL hD y U v c j₀ w
local notation "π" => normalizedToOriginal D
local notation "α" => originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
local notation "C" => Model.canonicalChart F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw
private abbrev cartierChartMap : Spec (.of B) ⟶ normalizedScheme D :=
  (C).hom ≫ (π ⁻¹ᵁ U.1).ι
local notation "φ" => cartierChartMap F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw

omit [IsIntegral X] [Nonempty U.1] in
include hcomp in
/-- Every SAME original branch generator is regular in the original affine
ring, including branches absent at the original point. -/
theorem originalBranchGenerator_regular
    (a : Fin (Fintype.card (Joined.Index F n))) :
    Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c a ∈
      nonZeroDivisors Γ(X, U.1) := by
  classical
  let A := OriginalData.ideals F n L m σ hL hD
  let b := originalIndex F n A (Joined.row F n a)
  by_cases hb : y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A).component b).support
  · have hi : (F.component (Joined.row F n a)).ideal U =
        Ideal.span {v (c ⟨b, hb⟩)} := by
      simpa only [b, A, component_originalIndex] using hcomp ⟨b, hb⟩
    have hreg := (hD (Joined.row F n a)).generator_mem_nonZeroDivisors U
      (v (c ⟨b, hb⟩)) hi
    simpa only [Joined.branchGenerator, uniformBranches, b, A, dif_pos hb] using hreg
  · simpa only [Joined.branchGenerator, uniformBranches, b, A, dif_neg hb] using
      (Submonoid.one_mem (nonZeroDivisors Γ(X, U.1)))

omit [IsIntegral X] in
include hcomp hm in
/-- The SAME distinguished original root is a nonzerodivisor in the WHOLE
ratio algebra. No domain or connected-component assumption on that algebra
is used. -/
theorem canonicalHeadRoot_regular (i : F.ι) :
    NadelMixedKummer.root (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
        (Joined.ordering F n (i, j₀ i)) ∈ nonZeroDivisors B := by
  let a : Fin (Fintype.card (Joined.Index F n)) := Joined.ordering F n (i, j₀ i)
  have hfix : a = Joined.head F n j₀ a := by
    simp only [a, Joined.head, Joined.row, Equiv.symm_apply_apply]
  have hcoefficient : ratioCoefficients F n L m σ hL hD y U v c j₀ w a ∈
      nonZeroDivisors Γ(X, U.1) := by
    change (BranchRatios.ratioUnit (Joined.head F n j₀)
        (OriginalData.orderedUnits F n L m σ U w) a : Γ(X, U.1)) *
      BranchRatios.ratioGenerator (Joined.head F n j₀)
        (Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
        (Joined.auxiliaryGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c) a ∈ _
    rw [BranchRatios.ratioGenerator, if_pos hfix]
    exact mul_mem
      (BranchRatios.ratioUnit (Joined.head F n j₀)
        (OriginalData.orderedUnits F n L m σ U w) a).isUnit.mem_nonZeroDivisors
      (originalBranchGenerator_regular F n L m σ hL hD y U v c hcomp a)
  let : Module.Flat Γ(X, U.1) B :=
    VaryingFinite.flat (Joined.degree F n m)
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
      (fun a => hm (Joined.row F n a))
  have hmap := flat_algebraMap_regular (S := B)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w a) hcoefficient
  have hpower : IsRegular
      (NadelMixedKummer.root (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w) a ^ Joined.degree F n m a) := by
    rw [NadelMixedKummer.root_pow]
    exact hmap
  exact ((IsRegular.pow_iff (show 0 < Joined.degree F n m a from
    hm (Joined.row F n a))).mp hpower).mem_nonZeroDivisors

/-- The literal whole original row ideal is ACTUALLY Cartier on its SAME
whole normalized chart, with every unit-root factor retained. -/
theorem canonicalRowIdeal_comap_isInvertible (i : F.ι) :
    ((wholeRowIdeal F n L m σ hL i).comap (φ)).IsInvertible := by
  let s : B := NadelMixedKummer.root (Joined.degree F n m)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
    (Joined.ordering F n (i, j₀ i))
  let eΓ : B ≃+* Γ(Spec (.of B), ⊤) :=
    (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.symm
  have hs : s ∈ nonZeroDivisors B :=
    canonicalHeadRoot_regular F n L m σ hL hD y U v c j₀ w hm hcomp i
  have hΓ : (Scheme.ΓSpecIso (.of B)).inv s ∈
      nonZeroDivisors Γ(Spec (.of B), ⊤) := by
    change eΓ s ∈ nonZeroDivisors Γ(Spec (.of B), ⊤)
    rw [← MulEquivClass.map_nonZeroDivisors eΓ]
    exact ⟨s, hs, rfl⟩
  intro z
  refine ⟨⟨⊤, isAffineOpen_top (Spec (.of B))⟩, trivial,
    (Scheme.ΓSpecIso (.of B)).inv s, hΓ, ?_⟩
  exact canonicalRowIdeal_top F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU habsent e hw i

end CanonicalChart
end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
