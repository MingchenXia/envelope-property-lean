import EnvelopeProperty.Vanishing.NadelBoundedCanonicalSelectedPowers
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRoundedCharts

/-! # The literal whole original ratio monomial bounds its native top form

Original joined-family coefficients and original SNC coordinates internally
identify the SAME actual ratio algebra with its exact mixed formula. Every
selected original row root, including inactive unit roots, is retained.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalRatioPowers
open CanonicalGeometry NadelMixedKummer NadelCanonicalBaseChange
open NadelGlobalAdaptedRoots NadelGlobalAdaptedModel NadelAdaptedChartMatching
open NadelAuxiliaryMulticover NadelGlobalNormalization CyclicSectionSNCUniformFramedCharts
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

private theorem coefficient_selected_factor {k R : Type u}
    [Field k] [CommRing R] [Algebra k R] {n q : ℕ}
    (x : Fin n → R) (N : Fin q → ℕ) (I : Set (Fin q))
    (τ : I ↪ Fin n) (v : Fin q → Rˣ) (c : Fin q → R)
    (hc : c = mixedCoefficient x I τ v) (hN : ∀ i, 0 < N i)
    {E : Type u} [Fintype E] (h : E ↪ Fin q)
    (a : E → ℕ) (ha : ∀ i, a i < N (h i)) :
    ∃ ω : affineCanonicalModule k (NadelMixedKummer.Ring N c) n,
      topPullback (R := k) (A := R) (B := NadelMixedKummer.Ring N c) n
        (exteriorPower.ιMulti R n (fun j => KaehlerDifferential.D k R (x j))) =
      (∏ i, root N c (h i) ^ a i) • ω := by
  subst c
  exact NadelBoundedCanonicalSelectedPowers.mixedCoordinateTopDifferential_selected_factor
    x N I τ v hN h a ha

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
  {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

local notation "Bᵣ" => RatioRing F n L m σ hL hD y U v c j₀ w

omit [IsIntegral X] in
/-- The SAME literal whole original rounded-ideal chart monomial divides
the SAME original pulled coordinate top form. The active set, mixed
coordinates, coefficient equality and head injection are all constructed
internally from the original data; no desired local factor is a premise. -/
theorem canonicalRoundedMonomial_topDifferential_factor
    (hcinj : Function.Injective c) (hm : ∀ i, 0 < m i)
    (a : F.ι → ℕ) (ha : ∀ i, a i < m i) :
    let _ := f.sectionsAlgebra U.1
    ∃ ω : affineCanonicalModule k Bᵣ n,
      topPullback (R := k) (A := Γ(X, U.1)) (B := Bᵣ) n
        (exteriorPower.ιMulti Γ(X, U.1) n
          (fun j => KaehlerDifferential.D k Γ(X, U.1) (v j))) =
      canonicalRoundedMonomial F n L m σ hL hD y U v c j₀ w a • ω := by
  classical
  let _ := f.sectionsAlgebra U.1
  let A₀ := OriginalData.ideals F n L m σ hL hD
  let G := NadelBertiniAuxiliaryFamily.auxiliaryFamily F n A₀
  let ell := Joined.orderedLabel F n A₀ j₀
  let I := OriginalMixed.active G y ell
  let τ := OriginalMixed.coordinates G y c hcinj ell
  let ū := BranchRatios.ratioUnit (Joined.head F n j₀)
    (OriginalData.orderedUnits F n L m σ U w)
  have hc : ratioCoefficients F n L m σ hL hD y U v c j₀ w =
      mixedCoefficient v I τ ū := by
    funext i
    exact (Joined.ratioCoefficient_eq F n A₀ j₀ y U v c
      (OriginalData.orderedUnits F n L m σ U w) i).trans
      (OriginalMixed.coefficient_eq_mixed G y U v c hcinj ell ū i)
  let h : F.ι ↪ Fin (Fintype.card (Joined.Index F n)) :=
    ⟨fun i => Joined.ordering F n (i, j₀ i), by
      intro i j hij
      exact congrArg Prod.fst ((Joined.ordering F n).injective hij)⟩
  have hN (i) : 0 < Joined.degree F n m i := hm (Joined.row F n i)
  have ha' (i) : a i < Joined.degree F n m (h i) := by
    simpa only [h, Function.Embedding.coeFn_mk, Joined.degree, Joined.row,
      Equiv.symm_apply_apply] using ha i
  change ∃ ω : affineCanonicalModule k
      (NadelMixedKummer.Ring (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w)) n,
    topPullback (R := k) (A := Γ(X, U.1))
      (B := NadelMixedKummer.Ring (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w)) n
      (exteriorPower.ιMulti Γ(X, U.1) n
        (fun j => KaehlerDifferential.D k Γ(X, U.1) (v j))) =
      (∏ i, root (Joined.degree F n m)
        (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (h i) ^ a i) • ω
  exact coefficient_selected_factor v (Joined.degree F n m) I τ ū
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w) hc hN h a ha'

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalRatioPowers
