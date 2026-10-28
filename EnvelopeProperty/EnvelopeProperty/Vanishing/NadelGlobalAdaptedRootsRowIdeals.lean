import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsMonomials
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsIdeals

/-! # The actual whole row-root ideal on the same normalized ratio chart

The proved original section coefficients compute the literal global sum of
ALL original normalized root zero ideals after actual pullback. Every original
copy and every whole ratio-algebra factor is retained.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching
open SchemeLineSectionEvaluation NadelBertiniFibreIdeals

private theorem zeroIdeal_on_frame {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (e : (pullback f).obj L ≅ unitObj Y) :
    (LineSectionZeroIdeal.zeroIdeal L hL s).comap f =
      LineSectionZeroIdeal.zeroIdeal (unitObj Y) (isInvertible_unit (X := Y))
        (pullbackSectionHom f s ≫ e.hom) :=
  (zeroIdeal_comap f L hL s).trans
    (zeroIdeal_iso ((pullback f).obj L) (unitObj Y) (hL.pullback f)
      (isInvertible_unit (X := Y)) e (pullbackSectionHom f s))

private theorem zeroIdeal_unitEnd_top {Y : Scheme.{u}} [IsAffine Y] (r : Γ(Y, ⊤)) :
    (LineSectionZeroIdeal.zeroIdeal (unitObj Y) (isInvertible_unit (X := Y))
      (ModularCurves.unitEndomorphismOfTopSection r)).ideal
        ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {r} := by
  rw [LineSectionZeroIdeal.zeroIdeal_ideal_of_frame (unitObj Y)
    (isInvertible_unit (X := Y)) (ModularCurves.unitEndomorphismOfTopSection r)
    ⟨⊤, isAffineOpen_top Y⟩ (Iso.refl _)]
  change Ideal.span {1 * Y.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op r} = _
  simp

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

local instance rowIdealBaseAffine : IsAffine U.1.toScheme := U.2
local notation "D" => OriginalData.data F n L m σ
local notation "B" => RatioRing F n L m σ hL hD y U v c j₀ w
local notation "π" => normalizedToOriginal D
local notation "α" => originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
local notation "C" => Model.canonicalChart F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw
private abbrev rowIdealChartMap : Spec (.of B) ⟶ normalizedScheme D :=
  (C).hom ≫ (π ⁻¹ᵁ U.1).ι
local notation "φ" => rowIdealChartMap F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw

/-- The actual zero ideal of every SAME original normalized root has its
proved original quotient coefficient on the whole canonical chart. -/
theorem canonicalRootIdeal_top (a : Fin (D).length) :
    ((normalizedRootIdeal D a (OriginalData.get_isInvertible F n L m σ hL a)).comap
        (φ)).ideal ⟨⊤, isAffineOpen_top (Spec (.of B))⟩ =
      Ideal.span {((Scheme.ΓSpecIso (.of B)).inv
        ((α) (NadelMixedKummer.root (OriginalChart.degree D)
          (WholeChart.coefficients U D e) a)))} := by
  unfold normalizedRootIdeal
  rw [zeroIdeal_on_frame (φ) (normalizedLine D a)
    ((OriginalData.get_isInvertible F n L m σ hL a).pullback π)
    (normalizedRoot D a)
    (canonicalRootFrame F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU habsent e hw a)]
  rw [canonicalRoot_coefficient, zeroIdeal_unitEnd_top]

/-- The literal sum of ALL original normalized row-root zero ideals becomes
precisely the head-root principal ideal on the SAME whole canonical chart. -/
theorem canonicalRowIdeal_top (i : F.ι) :
    ((wholeRowIdeal F n L m σ hL i).comap (φ)).ideal
        ⟨⊤, isAffineOpen_top (Spec (.of B))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (.of B)).inv
        (NadelMixedKummer.root (Joined.degree F n m)
          (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
          (Joined.ordering F n (i, j₀ i)))} := by
  have hhead :
      ((normalizedRootIdeal D (rowPosition F n L m σ i (j₀ i))
        (OriginalData.get_isInvertible F n L m σ hL
          (rowPosition F n L m σ i (j₀ i)))).comap (φ)).ideal
          ⟨⊤, isAffineOpen_top (Spec (.of B))⟩ =
        Ideal.span {(Scheme.ΓSpecIso (.of B)).inv
          (NadelMixedKummer.root (Joined.degree F n m)
            (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
            (Joined.ordering F n (i, j₀ i)))} := by
    rw [canonicalRootIdeal_top, originalToRatio_head_root]
  rw [wholeRowIdeal, (Scheme.IdealSheafData.map_gc (φ)).l_iSup,
    Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hj : j = j₀ i
    · subst j
      exact hhead.le
    · rw [canonicalRootIdeal_top,
        originalToRatio_other_root F n L m σ hL hD y U v c j₀ e w hw habsent i j hj,
        map_mul]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
  · exact le_iSup_of_le (j₀ i) hhead.ge

/-- This is an equality for the entire actual pulled global row ideal,
including every whole disconnected unit-root factor. -/
theorem canonicalRowIdeal_comap_eq_principal (i : F.ι) :
    (wholeRowIdeal F n L m σ hL i).comap (φ) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso (.of B)).inv
          (NadelMixedKummer.root (Joined.degree F n m)
            (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
            (Joined.ordering F n (i, j₀ i)))}) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [canonicalRowIdeal_top, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp

/-- The SAME entire global row sum is locally its SAME original distinguished
root zero ideal; no new replacement global ideal is introduced. -/
theorem canonicalRowIdeal_comap_eq_head (i : F.ι) :
    (wholeRowIdeal F n L m σ hL i).comap (φ) =
      (normalizedRootIdeal D (rowPosition F n L m σ i (j₀ i))
        (OriginalData.get_isInvertible F n L m σ hL
          (rowPosition F n L m σ i (j₀ i)))).comap (φ) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [canonicalRowIdeal_top, canonicalRootIdeal_top, originalToRatio_head_root]

end CanonicalChart
end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
