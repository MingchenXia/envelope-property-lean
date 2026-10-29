import EnvelopeProperty.Vanishing.NadelCanonicalMixedActivePower
import EnvelopeProperty.Vanishing.NadelCanonicalUnitRootChart
import EnvelopeProperty.Vanishing.NadelKummerTraceJacobian

/-! # Actual etale coordinates and genuine differential frames on the whole original active quotient -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CanonicalGeometry NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
local notation "d" => coordinateExponent N I σ
local notation "x" => originalCoordinates a
local notation "A₀" => ActiveRing N I (pureCoefficient x I σ)

private theorem formallyEtale_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) : f.FormallyEtale := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.Etale A B := RingHom.Etale.of_bijective hf
  change Algebra.FormallyEtale A B
  infer_instance

include hN ha in
/-- The SAME actual coordinate evaluation is formally etale, from the original chart and the proved whole ring iso. -/
theorem coordinateEvaluation_formallyEtale : (coordinateEvaluation N I σ a).toRingHom.FormallyEtale := by
  have hright := powerBaseChangeRight_formallyEtale k d R a.toRingHom ha
  have hinv : (powerToActive N I σ hN a).FormallyEtale :=
    formallyEtale_of_bijective _ (activePowerRingEquiv N I σ hN a).symm.bijective
  rw [← powerToActive_right N I σ hN a]
  exact hright.comp hinv

/-- Actual original geometry internally produces a true differential frame on the whole active quotient. -/
def activeDifferentialBasis : Module.Basis (Fin n) A₀ (KaehlerDifferential k A₀) :=
  NadelCanonicalUnitRoot.chartDifferentialBasis k A₀ (coordinateEvaluation N I σ a)
    (coordinateEvaluation_formallyEtale N I σ hN a ha)

/-- The produced whole-source differential frame consists of the SAME original coordinate-root differentials. -/
theorem activeDifferentialBasis_apply (j : Fin n) :
    activeDifferentialBasis N I σ hN a ha j = KaehlerDifferential.D k A₀ (coordinateRoot N I σ x j) := by
  rw [activeDifferentialBasis, NadelCanonicalUnitRoot.chartDifferentialBasis_apply]
  congr 1
  simp only [coordinateEvaluation, MvPolynomial.aeval_X]

/-- The genuine original base top frame, produced from its actual original etale coordinates. -/
def baseDifferentialBasis : Module.Basis (Fin n) R (KaehlerDifferential k R) :=
  NadelCanonicalUnitRoot.chartDifferentialBasis k R a ha

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
