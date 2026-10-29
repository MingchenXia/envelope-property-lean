import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquareRestrictedInputEquality
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquarePurificationTypedInput

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

/-- The accepted source equality in the literal original purification
function's S-source, before applying any P-reader. -/
theorem mixedNativeCanonicalSquare_restricted_input_original_coordinate
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    originalMixedCoordinateSquarePiece%(40,
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame,
      unitBaseSectionsIso (k := k) x N u hx hN htame,
      pureNativeCanonicalPullback N I σ (unitCoordinateMap (k := k) x N u)
        (unitCoordinateMap_etale x N u hx hN htame),
      mixedNativeCanonicalSquare_purificationInputCoordinates (k := k) x N I σ u hx hN htame,
      mixedPurification_ring_square (k := k) x N I σ u hN) :=
  originalMixedCoordinateSquarePiece%(41,
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame,
      unitBaseSectionsIso (k := k) x N u hx hN htame,
      pureNativeCanonicalPullback N I σ (unitCoordinateMap (k := k) x N u)
        (unitCoordinateMap_etale x N u hx hN htame),
      mixedNativeCanonicalSquare_purificationInputCoordinates (k := k) x N I σ u hx hN htame,
      mixedPurification_ring_square (k := k) x N I σ u hN)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
