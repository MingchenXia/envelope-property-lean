import EnvelopeProperty.Vanishing.NadelCanonicalMixedActivePowerMaps

/-! # Whole original coefficient and root formulas for actual active/power comparison maps -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open NadelMixedKummer NadelKummerCanonicalTrace NadelKummerCanonicalBaseChange NadelKummerCover
attribute [local instance] Classical.propDecidable
open scoped TensorProduct
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n q : ℕ}
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R)
local notation "d" => coordinateExponent N I σ
local notation "x" => originalCoordinates a
local notation "A₀" => ActiveRing N I (pureCoefficient x I σ)
local notation "C₀" => powerBaseChangeRing k d R a.toRingHom

/-- Every original pure tensor has its genuine original coefficient/root-evaluation product. -/
theorem powerToActive_tensor (r : R) (p : MvPolynomial (Fin n) k) :
    powerToActive N I σ hN a (powerBaseChangeTensor k d R a.toRingHom r p) =
      algebraMap R A₀ r * coordinateEvaluation N I σ a p := by
  let P := MvPolynomial (Fin n) k
  let : Algebra P R := a.toRingHom.toAlgebra
  let : Algebra P P := (powerMap k d).toAlgebra
  let : Module P P := (powerMap k d).toAlgebra.toModule
  let f : R →ₐ[R] A₀ := Algebra.ofId R A₀
  let g : P →ₐ[P] A₀ := {
    toRingHom := (coordinateEvaluation N I σ a).toRingHom
    commutes' p := congrArg (fun z : P →+* A₀ => z p) (coordinateEvaluation_square N I σ hN a) }
  change Algebra.TensorProduct.lift f g (fun _ _ => Commute.all ..) (r ⊗ₜ[P] p) = _
  exact Algebra.TensorProduct.lift_tmul f g _ r p

/-- The actual left coefficient map is retained on every original coefficient. -/
theorem powerToActive_left : (powerToActive N I σ hN a).comp (powerBaseChangeLeft k d R a.toRingHom) =
    algebraMap R A₀ := by
  apply RingHom.ext
  intro r
  change powerToActive N I σ hN a (powerBaseChangeTensor k d R a.toRingHom r 1) = _
  rw [powerToActive_tensor, map_one, mul_one]

/-- The actual original polynomial inclusion has its true coordinate-root evaluation on the entire polynomial ring. -/
theorem powerToActive_right : (powerToActive N I σ hN a).comp (powerBaseChangeRight k d R a.toRingHom) =
    (coordinateEvaluation N I σ a).toRingHom := by
  apply RingHom.ext
  intro p
  change powerToActive N I σ hN a (powerBaseChangeTensor k d R a.toRingHom 1 p) = _
  rw [powerToActive_tensor, map_one, one_mul]
  rfl

/-- The whole original active quotient map retains the SAME original coefficient inclusion. -/
theorem activeToPower_structure : (activeToPower N I σ hN a).comp (algebraMap R A₀) =
    powerBaseChangeLeft k d R a.toRingHom := by
  exact evaluate_structure _ _ _ _ _

/-- Every same original active root has its actual original coordinate in the power algebra. -/
theorem activeToPower_root (i : Fin q) :
    activeToPower N I σ hN a (root (activeDegree N I) (pureCoefficient x I σ) i) =
      if hh : i ∈ I then powerBaseChangeRight k d R a.toRingHom (MvPolynomial.X (σ ⟨i, hh⟩)) else 1 :=
  evaluate_root _ _ _ _ _ i

include hN in
/-- All coordinate exponents, including every degree-one unused coordinate, have their original base power relation. -/
theorem powerRight_coordinate_pow (j : Fin n) :
    powerBaseChangeRight k d R a.toRingHom (MvPolynomial.X j) ^ coordinateDegree N I σ j =
      powerBaseChangeLeft k d R a.toRingHom (x j) := by
  have h := congrArg (fun z : MvPolynomial (Fin n) k →+* C₀ => z (MvPolynomial.X j))
    (powerBaseChange_square k d R a.toRingHom)
  have hX : powerMap k d (MvPolynomial.X j) = MvPolynomial.X j ^ (d j + 1) :=
    coordinatePowerHom_X k (fun j => d j + 1) j
  change powerBaseChangeLeft k d R a.toRingHom (x j) =
    powerBaseChangeRight k d R a.toRingHom (powerMap k d (MvPolynomial.X j)) at h
  rw [hX, map_pow, coordinateExponent_succ N I σ hN] at h
  exact h.symm

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
