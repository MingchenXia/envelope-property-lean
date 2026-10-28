import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquareLeft
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedCoordinateSquareRight

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

/-- The original pure coordinate value in the original target-ring alias. All coefficient and field dictionaries are retained. -/
theorem mixedNativeCanonicalSquare_original_right_coordinate
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    originalMixedCoordinateSquarePiece%(47,
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame,
      unitBaseSectionsIso (k := k) x N u hx hN htame,
      pureNativeCanonicalPullback N I σ (unitCoordinateMap (k := k) x N u)
        (unitCoordinateMap_etale x N u hx hN htame),
      mixedNativeCanonicalSquare_purificationInputCoordinates (k := k) x N I σ u hx hN htame,
      mixedPurification_ring_square (k := k) x N I σ u hN) :=
  originalMixedCoordinateSquarePiece%(48,
      mixedExtendedSectionsIso (k := k) x N I σ u hx hN htame,
      mixedPurificationSectionsIso (k := k) x N I σ u hx hN htame,
      unitBaseSectionsIso (k := k) x N u hx hN htame,
      pureNativeCanonicalPullback N I σ (unitCoordinateMap (k := k) x N u)
        (unitCoordinateMap_etale x N u hx hN htame),
      mixedNativeCanonicalSquare_purificationInputCoordinates (k := k) x N I σ u hx hN htame,
      mixedPurification_ring_square (k := k) x N I σ u hN)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
