import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRoundedLine
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRowIdeals
import Mathlib.RingTheory.Ideal.Operations

/-! # Literal whole rounded ideal coefficients on the actual canonical charts

The genuine inverse image of the product of ALL original whole row ideals
is the ideal of the actual product of distinguished root powers. This keeps
whole ideals and all unit-root factors, without a support/radical replacement.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry NadelAuxiliaryMulticover NadelAdaptedChartMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def chartIdealHom {Y Z : Scheme.{u}} (g : Y ⟶ Z) (V : Y.affineOpens) :
    Z.IdealSheafData →* Ideal Γ(Y, V) where
  toFun I := (I.comap g).ideal V
  map_one' := by simp
  map_mul' I J := by rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.ideal_mul]; rfl

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

local instance roundedIdealBaseAffine : IsAffine U.1.toScheme := U.2
local notation "D" => OriginalData.data F n L m σ
local notation "B" => RatioRing F n L m σ hL hD y U v c j₀ w
local notation "π" => normalizedToOriginal D
local notation "α" => originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
local notation "C" => Model.canonicalChart F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw
private abbrev roundedIdealChartMap : Spec (.of B) ⟶ normalizedScheme D :=
  (C).hom ≫ (π ⁻¹ᵁ U.1).ι
local notation "φ" => roundedIdealChartMap F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw

/-- The literal monomial in the SAME original whole canonical ratio ring. -/
def canonicalRoundedMonomial (a : F.ι → ℕ) : B :=
  ∏ i, NadelMixedKummer.root (Joined.degree F n m)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
    (Joined.ordering F n (i, j₀ i)) ^ a i

/-- The entire pulled original rounded ideal has the actual product of
original head roots as its principal generator on the SAME chart. -/
theorem canonicalRoundedIdeal_top (a : F.ι → ℕ) :
    ((wholeRoundedIdeal F n L m σ hL a).comap (φ)).ideal
        ⟨⊤, isAffineOpen_top (Spec (.of B))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (.of B)).inv
        (canonicalRoundedMonomial F n L m σ hL hD y U v c j₀ w a)} := by
  classical
  let V : (Spec (.of B)).affineOpens := ⟨⊤, isAffineOpen_top (Spec (.of B))⟩
  let ρ := chartIdealHom (φ) V
  let g (i : F.ι) : Γ(Spec (.of B), ⊤) :=
    (Scheme.ΓSpecIso (.of B)).inv
      (NadelMixedKummer.root (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w)
        (Joined.ordering F n (i, j₀ i)))
  have hrow (i : F.ι) : ρ (wholeRowIdeal F n L m σ hL i) = Ideal.span {g i} :=
    canonicalRowIdeal_top F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU habsent e hw i
  have hprod (s : Finset F.ι) :
      ρ (∏ i ∈ s, wholeRowIdeal F n L m σ hL i ^ a i) =
        Ideal.span {∏ i ∈ s, g i ^ a i} := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, map_one, Ideal.one_eq_top, Ideal.span_singleton_one]
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, map_mul, map_pow,
          hrow, ih, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  change ρ (∏ i, wholeRowIdeal F n L m σ hL i ^ a i) = _
  rw [hprod]
  congr 1
  unfold canonicalRoundedMonomial
  simp only [map_prod, map_pow, g]

/-- Equality of the WHOLE original pulled rounded ideal with the actual
principal ideal sheaf, including all disconnected unit-root factors. -/
theorem canonicalRoundedIdeal_comap_eq_principal (a : F.ι → ℕ) :
    (wholeRoundedIdeal F n L m σ hL a).comap (φ) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(Scheme.ΓSpecIso (.of B)).inv
          (canonicalRoundedMonomial F n L m σ hL hD y U v c j₀ w a)}) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [canonicalRoundedIdeal_top, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp

end CanonicalChart
end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
