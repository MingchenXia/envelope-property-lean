import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquareInputTuple
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquareRestrictedSourceValues

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

/-- The exact original purification theorem specialized to the SAME mixed input tuple, with no reconstructed endpoint. -/
theorem mixedNativeCanonicalSquare_purification_input_coordinate_typed
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    originalActionType%(originalMixedCoordinateSquarePiece%(30,
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame,
      unitBaseSectionsIso (k := k) x N u hx hN htame,
      pureNativeCanonicalPullback N I σ (unitCoordinateMap (k := k) x N u)
        (unitCoordinateMap_etale x N u hx hN htame),
      (mixedNativeCanonicalSquare_purificationInputCoordinates (k := k) x N I σ u hx hN htame),
      mixedPurification_ring_square (k := k) x N I σ u hN)) :=
  originalMixedCoordinateSquarePiece%(30,
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame,
      unitBaseSectionsIso (k := k) x N u hx hN htame,
      pureNativeCanonicalPullback N I σ (unitCoordinateMap (k := k) x N u)
        (unitCoordinateMap_etale x N u hx hN htame),
      (mixedNativeCanonicalSquare_purificationInputCoordinates (k := k) x N I σ u hx hN htame),
      mixedPurification_ring_square (k := k) x N I σ u hN)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
