import EnvelopeProperty.Vanishing.NadelCanonicalMixedCoordinates
import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChange

/-! # Actual original active quotient and coordinate-power tensor maps -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open NadelMixedKummer NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange NadelKummerCover
attribute [local instance] Classical.propDecidable
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R)

/-- The SAME original coordinate tuple of the actual original etale chart map. -/
def originalCoordinates (j : Fin n) : R := a (MvPolynomial.X j)

local notation "d" => coordinateExponent N I σ
local notation "x" => originalCoordinates a
local notation "A₀" => ActiveRing N I (pureCoefficient x I σ)
local notation "C₀" => powerBaseChangeRing k d R a.toRingHom

/-- The actual new polynomial coordinates evaluate to the genuine original active roots. -/
def coordinateEvaluation : MvPolynomial (Fin n) k →ₐ[k] A₀ :=
  MvPolynomial.aeval (coordinateRoot N I σ x)

include hN in
/-- Every original coordinate power has its SAME true base coefficient. -/
theorem coordinateEvaluation_power_X (j : Fin n) :
    coordinateEvaluation N I σ a (MvPolynomial.X j ^ (d j + 1)) = algebraMap R A₀ (x j) := by
  rw [map_pow, coordinateExponent_succ N I σ hN]
  simpa only [coordinateEvaluation, MvPolynomial.aeval_X] using coordinateRoot_pow N I σ x j

include hN in
/-- The entire original coefficient square commutes, on all original polynomial elements. -/
theorem coordinateEvaluation_square :
    (coordinateEvaluation N I σ a).toRingHom.comp (powerMap k d) =
      (algebraMap R A₀).comp a.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change coordinateEvaluation N I σ a (powerMap k d (MvPolynomial.C c)) = algebraMap R A₀ (a (MvPolynomial.C c))
    have hC : powerMap k d (MvPolynomial.C c) = MvPolynomial.C c :=
      coordinatePowerHom_C k (fun j => d j + 1) c
    rw [hC]
    change coordinateEvaluation N I σ a (algebraMap k (MvPolynomial (Fin n) k) c) = _
    rw [(coordinateEvaluation N I σ a).commutes]
    have ha : a (MvPolynomial.C c) = algebraMap k R c := a.commutes c
    rw [ha]
    exact IsScalarTower.algebraMap_apply k R A₀ c
  · intro j
    change coordinateEvaluation N I σ a (powerMap k d (MvPolynomial.X j)) = algebraMap R A₀ (x j)
    have hX : powerMap k d (MvPolynomial.X j) = MvPolynomial.X j ^ (d j + 1) :=
      coordinatePowerHom_X k (fun j => d j + 1) j
    rw [hX]
    exact coordinateEvaluation_power_X N I σ hN a j

/-- The original coordinate-power tensor algebra maps to the SAME entire active quotient. -/
def powerToActive : C₀ →+* A₀ := by
  let P := MvPolynomial (Fin n) k
  let : Algebra P R := a.toRingHom.toAlgebra
  let : Algebra P P := (powerMap k d).toAlgebra
  let : Module P P := (powerMap k d).toAlgebra.toModule
  let f : R →ₐ[R] A₀ := Algebra.ofId R A₀
  let g : P →ₐ[P] A₀ := {
    toRingHom := (coordinateEvaluation N I σ a).toRingHom
    commutes' p := congrArg (fun z : P →+* A₀ => z p) (coordinateEvaluation_square N I σ hN a) }
  exact (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all ..)).toRingHom

include hN in
/-- The true original power map sends each active coordinate root to the original base coordinate. -/
theorem powerRight_X_pow (i : I) :
    powerBaseChangeRight k d R a.toRingHom (MvPolynomial.X (σ i)) ^ N i.1 =
      powerBaseChangeLeft k d R a.toRingHom (x (σ i)) := by
  have h := congrArg (fun z : MvPolynomial (Fin n) k →+* C₀ => z (MvPolynomial.X (σ i)))
    (powerBaseChange_square k d R a.toRingHom)
  change powerBaseChangeLeft k d R a.toRingHom (x (σ i)) =
    powerBaseChangeRight k d R a.toRingHom (powerMap k d (MvPolynomial.X (σ i))) at h
  have hX : powerMap k d (MvPolynomial.X (σ i)) = MvPolynomial.X (σ i) ^ (d (σ i) + 1) :=
    coordinatePowerHom_X k (fun j => d j + 1) (σ i)
  rw [hX, map_pow, coordinateExponent_active N I σ hN i] at h
  exact h.symm

/-- Every original active quotient root maps to its SAME native power coordinate; inactive degree-one roots map to one. -/
def activeToPower : A₀ →+* C₀ := by
  classical
  exact evaluate (activeDegree N I) (pureCoefficient x I σ) (powerBaseChangeLeft k d R a.toRingHom)
    (fun i => if hh : i ∈ I then powerBaseChangeRight k d R a.toRingHom (MvPolynomial.X (σ ⟨i, hh⟩)) else 1)
    (by
      intro i
      by_cases hh : i ∈ I
      · simp only [activeDegree, if_pos hh, dif_pos hh, pureCoefficient]
        exact powerRight_X_pow N I σ hN a ⟨i, hh⟩
      · simp only [activeDegree, if_neg hh, dif_neg hh, pureCoefficient, one_pow, map_one])

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
