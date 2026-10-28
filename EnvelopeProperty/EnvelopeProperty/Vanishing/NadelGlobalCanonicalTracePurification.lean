import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceBaseChange
import EnvelopeProperty.Vanishing.NadelCanonicalMixedPureCoordinates

/-! # The actual same whole purification in the original field coordinates

This instantiates the published whole mixed purification on the original
unit cover.  Its target is exactly the pure quotient used by the genuine
pure canonical counit, with no comparison isomorphism supplied by a caller.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- The original coordinate homomorphism after the SAME entire unit cover. -/
def unitCoordinateMap : MvPolynomial (Fin n) k →ₐ[k] UnitCover N u :=
  (IsScalarTower.toAlgHom k A (UnitCover N u)).comp (MvPolynomial.aeval x)

/-- Original etale coordinates and positive tame degrees produce actual
etale coordinates over the whole unit cover, including every component. -/
theorem unitCoordinateMap_etale
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (unitCoordinateMap (k := k) x N u).toRingHom.Etale := by
  change ((algebraMap A (UnitCover N u)).comp
    (MvPolynomial.aeval (R := k) x).toRingHom).Etale
  exact RingHom.Etale.stableUnderComposition _ _ hx
    (RingHom.etale_algebraMap.mpr (unitCover_etale N u hN htame))

/-- The actual map used by the pure producer has its required formal
etaleness internally, rather than as an additional coordinate certificate. -/
theorem unitCoordinateMap_formallyEtale
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (unitCoordinateMap (k := k) x N u).toRingHom.FormallyEtale := by
  let : Algebra (MvPolynomial (Fin n) k) (UnitCover N u) :=
    (unitCoordinateMap (k := k) x N u).toRingHom.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) k) (UnitCover N u) :=
    unitCoordinateMap_etale x N u hx hN htame
  change Algebra.FormallyEtale (MvPolynomial (Fin n) k) (UnitCover N u)
  infer_instance

/-- Each active original coordinate and each inactive unit-one coefficient
is exactly the coefficient of the SAME original pure-counit presentation. -/
theorem unitPureCoefficient (i : Fin q) :
    algebraMap A (UnitCover N u) (pureCoefficient x I σ i) =
      pureCoefficient (originalCoordinates (unitCoordinateMap (k := k) x N u)) I σ i := by
  classical
  by_cases hi : i ∈ I
  · simp [pureCoefficient, hi, originalCoordinates, unitCoordinateMap]
  · simp only [pureCoefficient, dif_neg hi, map_one]

/-- The entire pure target of the actual original mixed purification. -/
abbrev mixedPureRing := NadelMixedKummer.Ring N
  (pureCoefficient (originalCoordinates (unitCoordinateMap (k := k) x N u)) I σ)

/-- The SAME actual whole purification, internally identified with the
pure producer's original coordinate quotient.  All original factors remain. -/
def mixedPurificationIso (hN : ∀ i, 0 < N i) :
    extendedMixedRing x N I σ u ≃ₐ[UnitCover N u]
      mixedPureRing (k := k) x N I σ u := by
  change UnitCover N u ⊗[A] NadelMixedKummer.Ring N (mixedCoefficient x I σ u) ≃ₐ[UnitCover N u]
    NadelMixedKummer.Ring N
      (pureCoefficient (originalCoordinates (unitCoordinateMap (k := k) x N u)) I σ)
  rw [← funext (unitPureCoefficient (k := k) x N I σ u)]
  exact mixedPurificationAlgEquiv N u hN x I σ

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
