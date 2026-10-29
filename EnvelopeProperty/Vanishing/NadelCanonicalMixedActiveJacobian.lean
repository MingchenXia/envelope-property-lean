import EnvelopeProperty.Vanishing.NadelCanonicalMixedActiveCanonical
import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniquenessCoordinate

/-! # Actual whole differential Jacobian and intrinsic trace normalization of the active canonical counit -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange
open NadelKummerTraceJacobian NadelKummerTraceBaseChangeUniqueness NadelCanonicalBaseChange
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
local notation "d" => coordinateExponent N I σ
local notation "x" => originalCoordinates a
local notation "A₀" => ActiveRing N I (pureCoefficient x I σ)
local notation "C₀" => powerBaseChangeRing k d R a.toRingHom

/-- The original coordinate Jacobian evaluated at the SAME actual active roots. -/
def activeJacobian : A₀ := coordinateEvaluation N I σ a (jacobian k d)

omit [Nontrivial k] in
/-- The whole original active coordinate map retains every original polynomial under the actual inverse comparison. -/
theorem activeToPower_coordinateEvaluation :
    (activeToPower N I σ hN a).comp (coordinateEvaluation N I σ a).toRingHom =
      powerBaseChangeRight k d R a.toRingHom := by
  have h := congrArg (fun f : C₀ →+* C₀ => f.comp (powerBaseChangeRight k d R a.toRingHom))
    (activeToPower_comp_powerToActive N I σ hN a)
  rw [RingHom.comp_assoc, powerToActive_right] at h
  exact h

omit [Nontrivial k] in
/-- The actual whole finite dual comparison preserves the original Jacobian polynomial. -/
theorem activeToPower_jacobian :
    activeToPower N I σ hN a (activeJacobian N I σ a) =
      powerBaseChangeRight k d R a.toRingHom (jacobian k d) :=
  congrArg (fun f : MvPolynomial (Fin n) k →+* C₀ => f (jacobian k d))
    (activeToPower_coordinateEvaluation N I σ hN a)

omit [Nontrivial k] in
/-- The genuine original base frame is literally the original ordered coordinate differential wedge. -/
theorem baseGenerator_eq_wedge : affineCanonicalGenerator (baseDifferentialBasis a ha) =
    exteriorPower.ιMulti R n (fun j => KaehlerDifferential.D k R (x j)) := by
  rw [affineCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  exact NadelCanonicalUnitRoot.chartDifferentialBasis_apply k R a ha j

omit [Nontrivial k] in
/-- The genuine target generator is the actual exterior differential image of the original polynomial generator. -/
theorem activeGenerator_eq_exteriorImage :
    affineCanonicalGenerator (activeDifferentialBasis N I σ hN a ha) =
      algebraExteriorMap (coordinateEvaluation N I σ a) n (canonicalGenerator k n) := by
  rw [canonicalGenerator_eq_wedge, algebraExteriorMap_differential_wedge,
    affineCanonicalGenerator_eq_wedge]
  congr 1
  funext j
  rw [activeDifferentialBasis_apply]
  congr 1
  simp only [coordinateEvaluation, MvPolynomial.aeval_X]

omit [Nontrivial k] in
/-- The actual original canonical differential is the true Jacobian multiple on the whole active quotient. -/
theorem activeTopPullback_generator :
    topPullback (R := k) (A := R) (B := A₀) n (affineCanonicalGenerator (baseDifferentialBasis a ha)) =
      activeJacobian N I σ a • affineCanonicalGenerator (activeDifferentialBasis N I σ hN a ha) := by
  have he : topPullback (R := k) (A := R) (B := A₀) n
      (affineCanonicalGenerator (baseDifferentialBasis a ha)) =
      algebraExteriorMap (coordinateEvaluation N I σ a) n
        (exteriorPower.ιMulti (MvPolynomial (Fin n) k) n
          (fun j => KaehlerDifferential.D k (MvPolynomial (Fin n) k) (powerMap k d (MvPolynomial.X j)))) := by
    rw [baseGenerator_eq_wedge, topPullback_wedge, algebraExteriorMap_differential_wedge]
    congr 1
    funext j
    rw [KaehlerDifferential.map_D]
    exact congrArg (KaehlerDifferential.D k A₀)
      (congrArg (fun f : MvPolynomial (Fin n) k →+* A₀ => f (MvPolynomial.X j))
        (coordinateEvaluation_square N I σ hN a)).symm
  rw [he]
  change algebraExteriorMap (coordinateEvaluation N I σ a) n
    (exteriorPower.ιMulti (MvPolynomial (Fin n) k) n
      (fun j => KaehlerDifferential.D k (MvPolynomial (Fin n) k)
        (NadelKummerCover.coordinatePowerHom k (fun i => d i + 1) (MvPolynomial.X j)))) = _
  rw [differential_power_wedge, map_smulₛₗ, ← activeGenerator_eq_exteriorImage N I σ hN a ha]
  rfl

/-- Native whole-algebra trace is the actual active coefficient functional against the original genuine Jacobian. -/
theorem activeCoefficient_jacobian (c : A₀) :
    powerBaseChangeCoefficient k d R a.toRingHom
      (activeToPower N I σ hN a (activeJacobian N I σ a * c)) = Algebra.trace R A₀ c := by
  let : Algebra R C₀ := (powerBaseChangeLeft k d R a.toRingHom).toAlgebra
  rw [map_mul, activeToPower_jacobian]
  have h := baseChangeTrace_eq_coefficient_jacobian k d R a.toRingHom (activeToPower N I σ hN a c)
  rw [coefficientFunctional_apply] at h
  exact h.symm.trans (Algebra.trace_eq_of_algEquiv (activePowerAlgEquiv N I σ hN a) c)

/-- Intrinsic trace normalization holds on the SAME actual pulled base top generator. -/
theorem activeCanonicalCounit_pulled_generator (c : A₀) :
    activeCanonicalCounit N I σ hN a ha
      (c • topPullback (R := k) (A := R) (B := A₀) n
        (affineCanonicalGenerator (baseDifferentialBasis a ha))) =
      Algebra.trace R A₀ c • affineCanonicalGenerator (baseDifferentialBasis a ha) := by
  have he : c • topPullback (R := k) (A := R) (B := A₀) n
      (affineCanonicalGenerator (baseDifferentialBasis a ha)) =
      (c * activeJacobian N I σ a) • affineCanonicalGenerator (activeDifferentialBasis N I σ hN a ha) := by
    rw [activeTopPullback_generator N I σ hN a ha]
    exact smul_smul c _ _
  calc
    _ = activeCanonicalCounit N I σ hN a ha
        ((c * activeJacobian N I σ a) • affineCanonicalGenerator (activeDifferentialBasis N I σ hN a ha)) :=
      congrArg (fun w : affineCanonicalModule k A₀ n => activeCanonicalCounit N I σ hN a ha w) he
    _ = powerBaseChangeCoefficient k d R a.toRingHom
        (activeToPower N I σ hN a (c * activeJacobian N I σ a)) •
          affineCanonicalGenerator (baseDifferentialBasis a ha) :=
      activeCanonicalCounit_generator N I σ hN a ha _
    _ = _ := by rw [mul_comm c, activeCoefficient_jacobian]

/-- Every genuine original base top form has its true whole active-algebra intrinsic trace normalization. -/
theorem activeCanonicalCounit_pulled_topform (c : A₀) (w : affineCanonicalModule k R n) :
    activeCanonicalCounit N I σ hN a ha (c • topPullback (R := k) (A := R) (B := A₀) n w) =
      Algebra.trace R A₀ c • w := by
  have he : c • topPullback (R := k) (A := R) (B := A₀) n w =
      (c * algebraMap R A₀ (affineCanonicalTrivialization (baseDifferentialBasis a ha) w)) •
        topPullback (R := k) (A := R) (B := A₀) n
          (affineCanonicalGenerator (baseDifferentialBasis a ha)) := by
    conv_lhs => rw [affineCanonical_eq_smul_generator (baseDifferentialBasis a ha) w]
    rw [map_smulₛₗ]
    exact smul_smul c _ _
  calc
    _ = activeCanonicalCounit N I σ hN a ha
        ((c * algebraMap R A₀ (affineCanonicalTrivialization (baseDifferentialBasis a ha) w)) •
          topPullback (R := k) (A := R) (B := A₀) n
            (affineCanonicalGenerator (baseDifferentialBasis a ha))) :=
      congrArg (fun z : affineCanonicalModule k A₀ n => activeCanonicalCounit N I σ hN a ha z) he
    _ = Algebra.trace R A₀
        (c * algebraMap R A₀ (affineCanonicalTrivialization (baseDifferentialBasis a ha) w)) •
          affineCanonicalGenerator (baseDifferentialBasis a ha) :=
      activeCanonicalCounit_pulled_generator N I σ hN a ha _
    _ = _ := by
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm,
        ← smul_smul, ← affineCanonical_eq_smul_generator (baseDifferentialBasis a ha) w]

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
