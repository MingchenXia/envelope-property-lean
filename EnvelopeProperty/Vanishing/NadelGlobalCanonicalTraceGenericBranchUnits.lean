import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureCharts
import EnvelopeProperty.Vanishing.NadelCanonicalMixedUnitCover
import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingTensor
import Mathlib.RingTheory.Localization.Away.Basic

/-! # The SAME original ratio equations are units on their actual dense open

Original SNC geometry produces nonzero coefficients for EVERY original
ratio equation. Localizing at their actual full product produces the
whole tame unit-root algebra, retaining all original root factors.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericBranch
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelAdaptedChartMatching NadelGlobalAdaptedModel NadelGlobalAdaptedRoots
open CyclicSectionSNCUniformFramedCharts
open scoped TensorProduct BigOperators
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensor_root_etale_of_unit_coefficients
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {q : ℕ} (N : Fin q → ℕ) (c : Fin q → R) (hN : ∀ i, 0 < N i)
    (htame : ∀ i, IsUnit (N i : S))
    (hc : ∀ i, IsUnit (algebraMap R S (c i))) :
    Algebra.Etale S (S ⊗[R] NadelMixedKummer.Ring N c) := by
  let v (i : Fin q) : Sˣ := (hc i).unit
  have hv : (fun i => (v i : S)) = (fun i => algebraMap R S (c i)) :=
    funext (fun i => (hc i).unit_spec)
  have h : Algebra.Etale S
      (NadelMixedKummer.Ring N (fun i => algebraMap R S (c i))) := by
    rw [← hv]
    exact NadelCanonicalMixed.unitCover_etale N v hN htame
  let : Algebra.Etale S
      (NadelMixedKummer.Ring N (fun i => algebraMap R S (c i))) := h
  exact Algebra.Etale.of_equiv (BaseChange.tensorAlgEquiv (S := S) N c).symm

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    (y : X) (U : X.affineOpens) (v : Fin n → Γ(X, U.1))
    (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
        (OriginalData.ideals F n L m σ hL hD)).ι //
      y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
        (OriginalData.ideals F n L m σ hL hD)).component i).support} → Fin n)
    (j₀ : F.ι → Fin (n + 1))
    (w : Fin (OriginalData.data F n L m σ).length → (Γ(X, U.1))ˣ)

local notation "cc" => ratioCoefficients F n L m σ hL hD y U v c j₀ w
local notation "N" => Joined.degree F n m

/-- The actual product of EVERY original ratio coefficient. -/
def coefficientProduct : Γ(X, U.1) := ∏ i, cc i

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U = Ideal.span {v (c i)})
    (hy : y ∈ U.1)

include f hG hcomp hy in
/-- EVERY SAME original ratio coefficient is nonzero, internally from
the genuine original SNC generators, including all absent unit factors. -/
theorem ratioCoefficients_ne_zero (i : Fin (Fintype.card (Joined.Index F n))) : cc i ≠ 0 := by
  let : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hcoord := CyclicSectionSNCAffineOriginalCoefficient.branch_sections_ne_zero
    f hG y U v c hcomp y hy
  have hg := uniformBranches_ne_zero y U v c hcoord y hy
    (Joined.orderedLabel F n (OriginalData.ideals F n L m σ hL hD) j₀ i)
  change BranchRatios.coefficient (Joined.head F n j₀)
    (Joined.branchGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
    (Joined.auxiliaryGenerator F n (OriginalData.ideals F n L m σ hL hD) y U v c)
    (OriginalData.orderedUnits F n L m σ U w) i ≠ 0
  rw [Joined.ratioCoefficient_eq]
  exact mul_ne_zero (Units.ne_zero _) hg

include f hG hcomp hy in
/-- The actual full product is nonzero; no coefficient nonvanishing
or generic-branch avoidance certificate is an input. -/
theorem coefficientProduct_ne_zero :
    coefficientProduct F n L m σ hL hD y U v c j₀ w ≠ 0 := by
  let : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  exact Finset.prod_ne_zero_iff.mpr
    (fun i _ => ratioCoefficients_ne_zero F n L m σ hL hD y U v c j₀ w f hG hcomp hy i)

include f hG hcomp hy in
/-- The actual original generic field inverts EVERY original ratio
coefficient by injectivity of its SAME actual regular-function germ. -/
theorem ratioCoefficients_generic_isUnit (i : Fin (Fintype.card (Joined.Index F n))) :
    letI : Nonempty U.1 := ⟨⟨y, hy⟩⟩
    IsUnit ((X.germToFunctionField U.1) (cc i)) := by
  let : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using (X.germToFunctionField_injective U.1).ne
    (ratioCoefficients_ne_zero F n L m σ hL hD y U v c j₀ w f hG hcomp hy i)

variable (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

include f hm hfield in
omit [IsIntegral X] [SmoothOfRelativeDimension n f] in
/-- On the actual localization at the SAME full coefficient product,
the WHOLE original ratio model is tame etale. The units and the entire
tensor/algebra comparison are internally produced; no etaleness input. -/
theorem localizedRatio_etale :
    let S := Localization.Away (coefficientProduct F n L m σ hL hD y U v c j₀ w)
    Algebra.Etale S (S ⊗[Γ(X, U.1)] RatioRing F n L m σ hL hD y U v c j₀ w) := by
  let S := Localization.Away (coefficientProduct F n L m σ hL hD y U v c j₀ w)
  let _ := f.sectionsAlgebra U.1
  apply tensor_root_etale_of_unit_coefficients (R := Γ(X, U.1)) (S := S) N cc
    (fun i => hm (Joined.row F n i))
  · intro i
    have hA : IsUnit (N i : Γ(X, U.1)) := by
      simpa only [map_natCast, Joined.degree] using
        (hfield (Joined.row F n i)).map (algebraMap k Γ(X, U.1))
    simpa only [map_natCast] using hA.map (algebraMap Γ(X, U.1) S)
  · intro i
    apply IsLocalization.Away.isUnit_of_dvd
      (coefficientProduct F n L m σ hL hD y U v c j₀ w)
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericBranch
