import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedSheafCandidate
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalRatioPowers

/-! # The actual original whole ratio chart has its regular sheaf candidate

The original joined-family coefficients internally give the actual mixed
coefficient identity. Equality elimination transports the SAME mixed
sheaf candidate to the SAME whole ratio algebra. The actual original
field triangles then give a regular candidate for the native chart
canonical objects. No incoming map, model matching, normalization or
rational-factor certificate occurs.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
open NadelMixedKummer NadelCanonicalMixed
open NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelGlobalAdaptedModel NadelAdaptedChartMatching
open CyclicSectionSNCUniformFramedCharts
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
local infixr:80 " ≫ₛ " => CategoryStruct.comp (obj := Scheme)

private def coefficientSheafCandidate
    {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (τ : I ↪ Fin n) (u : Fin q → Aˣ) (d : Fin q → A)
    (hd : d = mixedCoefficient x I τ u)
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (pushforward (Spec.map (CommRingCat.ofHom
      (algebraMap A (NadelMixedKummer.Ring N d))))).obj
        (exteriorCotangentSheaf
          (affineStructuralMap k (.of (NadelMixedKummer.Ring N d))) n) ⟶
      exteriorCotangentSheaf (affineStructuralMap k (.of A)) n := by
  subst d
  exact mixedCanonicalSheafCandidate x N I τ u hx hN htame

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    (y : X) (U : X.affineOpens) [Nonempty U.1] (v : Fin n → Γ(X, U.1))
    (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
        (OriginalData.ideals F n L m σ hL hD)).ι //
      y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
        (OriginalData.ideals F n L m σ hL hD)).component i).support} → Fin n)
    (j₀ : F.ι → Fin (n + 1))
    (w : Fin (OriginalData.data F n L m σ).length → (Γ(X, U.1))ˣ)
    {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))

local notation "Bᵣ" => RatioRing F n L m σ hL hD y U v c j₀ w

/-- The SAME literal WHOLE original ratio chart has an internally
constructed regular sheaf candidate on its actual native canonical
objects. All mixed data, the coefficient identity and original field
triangles are internally derived from the original geometry.
This is not yet a normalization or rational-factor theorem. -/
def ratioCanonicalSheafCandidate :
    let _ := f.sectionsAlgebra U.1
    let p : Scheme.Hom (Spec (.of Bᵣ)) (Spec Γ(X, U.1)) :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))
    (pushforward p).obj
        (exteriorCotangentSheaf (p ≫ₛ (U.2.fromSpec ≫ₛ f)) n) ⟶
      exteriorCotangentSheaf (U.2.fromSpec ≫ₛ f) n := by
  let _ := f.sectionsAlgebra U.1
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
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
  have hN (i) : 0 < Joined.degree F n m i := hm (Joined.row F n i)
  have htameN (i) : IsUnit (Joined.degree F n m i : Γ(X, U.1)) :=
    htame (Joined.row F n i)
  have hx : (MvPolynomial.aeval (R := k) v).toRingHom.Etale :=
    (etale_toAffineSpace_iff f U.2 v).mp het
  let Taff := coefficientSheafCandidate (k := k) (A := Γ(X, U.1))
    v (Joined.degree F n m) I τ ū
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w) hc hx hN htameN
  let p : Scheme.Hom (Spec (.of Bᵣ)) (Spec Γ(X, U.1)) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))
  have hbase : U.2.fromSpec ≫ₛ f = affineStructuralMap k (.of Γ(X, U.1)) := by
    have hh := IsAffineOpen.SpecMap_appLE_fromSpec f
      (isAffineOpen_top (Spec (.of k))) U.2 le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hh
    exact hh.symm
  have hfield : p ≫ₛ affineStructuralMap k (.of Γ(X, U.1)) =
      affineStructuralMap k (.of Bᵣ) :=
    affineAlgebraMap_structuralSquare k (.of Γ(X, U.1)) (.of Bᵣ)
      (IsScalarTower.toAlgHom k Γ(X, U.1) Bᵣ)
  let eA := eqToIso (congrArg (fun z => exteriorCotangentSheaf z n) hbase)
  let eB := eqToIso (congrArg (fun z => exteriorCotangentSheaf z n)
    ((congrArg (fun z => p ≫ₛ z) hbase).trans hfield))
  exact (pushforward p).map eB.hom ≫ Taff ≫ eA.inv

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
