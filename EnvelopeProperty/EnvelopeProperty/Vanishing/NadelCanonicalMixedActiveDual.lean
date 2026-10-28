import EnvelopeProperty.Vanishing.NadelCanonicalMixedActiveDifferentials
import EnvelopeProperty.Vanishing.NadelCanonicalDualTransport
import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniqueness

/-! # The whole actual active quotient has its genuine native finite dual frame -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange
open NadelKummerTraceBaseChangeUniqueness
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R)
local notation "d" => coordinateExponent N I σ
local notation "x" => originalCoordinates a
local notation "A₀" => ActiveRing N I (pureCoefficient x I σ)
local notation "C₀" => powerBaseChangeRing k d R a.toRingHom

/-- The actual whole active coefficient functional, transferred from the already proved genuine power-map counit. -/
def activeCoefficient :
    (restrictScalars (algebraMap R A₀)).obj (ModuleCat.of A₀ A₀) →ₗ[R] R := by
  let : Algebra R C₀ := (powerBaseChangeLeft k d R a.toRingHom).toAlgebra
  exact NadelCanonicalDualTransport.coefficient (activePowerAlgEquiv N I σ hN a)
    (coefficientFunctional k d R a.toRingHom)

/-- Every original coefficient has its literal original power-counit value under the proved whole algebra map. -/
theorem activeCoefficient_apply (z : A₀) :
    activeCoefficient N I σ hN a z =
      powerBaseChangeCoefficient k d R a.toRingHom (activeToPower N I σ hN a z) := by
  change coefficientFunctional k d R a.toRingHom (activeToPower N I σ hN a z) = _
  exact coefficientFunctional_apply k d R a.toRingHom _

/-- The native adjunction turns this genuine coefficient into an actual active-algebra-linear dual frame. -/
def activeDualizingMap : A₀ →ₗ[A₀]
    (coextendScalars (algebraMap R A₀)).obj (ModuleCat.of R R) :=
  coextensionFrame (algebraMap R A₀) (activeCoefficient N I σ hN a)

/-- The whole original active dual frame retains its multiplication and actual whole coordinate map. -/
theorem activeDualizingMap_apply (z w : A₀) :
    activeDualizingMap N I σ hN a z w =
      powerBaseChangeCoefficient k d R a.toRingHom (activeToPower N I σ hN a (w * z)) := by
  rw [activeDualizingMap, coextensionFrame_apply]
  exact activeCoefficient_apply N I σ hN a _

/-- The already proved native power-frame is the actual transferred native frame on the ENTIRE power tensor algebra. -/
theorem powerFrame_bijective :
    letI : Algebra R C₀ := (powerBaseChangeLeft k d R a.toRingHom).toAlgebra
    Function.Bijective (coextensionFrame (algebraMap R C₀) (coefficientFunctional k d R a.toRingHom)) := by
  let : Algebra R C₀ := (powerBaseChangeLeft k d R a.toRingHom).toAlgebra
  have he (z : C₀) : coextensionFrame (algebraMap R C₀) (coefficientFunctional k d R a.toRingHom) z =
      (powerBaseChangeIso k d R a.toRingHom).hom z := by
    apply CoextendScalars.ext
    ext (w : C₀)
    rw [coextensionFrame_apply, coefficientFunctional_apply]
    exact (powerBaseChangeIso_apply k d R a.toRingHom z w).symm
  have hf : (coextensionFrame (algebraMap R C₀) (coefficientFunctional k d R a.toRingHom) :
      C₀ → (coextendScalars (algebraMap R C₀)).obj (ModuleCat.of R R)) =
        (powerBaseChangeIso k d R a.toRingHom).hom := funext he
  rw [hf]
  exact (powerBaseChangeIso k d R a.toRingHom).toLinearEquiv.bijective

include hN in
/-- Actual whole-frame bijectivity is derived internally from the original power duality and proved whole algebra iso. -/
theorem activeDualizingMap_bijective : Function.Bijective (activeDualizingMap N I σ hN a) := by
  let : Algebra R C₀ := (powerBaseChangeLeft k d R a.toRingHom).toAlgebra
  exact NadelCanonicalDualTransport.frame_bijective (activePowerAlgEquiv N I σ hN a)
    (coefficientFunctional k d R a.toRingHom) (powerFrame_bijective N I σ a)

/-- The SAME entire active quotient is its actual native coextension dual, without a supplied pairing or comparison input. -/
def activeDualizingIso : ModuleCat.of A₀ A₀ ≅
    (coextendScalars (algebraMap R A₀)).obj (ModuleCat.of R R) :=
  (LinearEquiv.ofBijective (activeDualizingMap N I σ hN a)
    (activeDualizingMap_bijective N I σ hN a)).toModuleIso

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
