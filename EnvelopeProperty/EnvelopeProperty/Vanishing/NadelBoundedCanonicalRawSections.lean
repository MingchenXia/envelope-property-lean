import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRawUnits

/-! # Ordinary coordinate wedges in their actual raw canonical sheaf sections

The original affine exterior map takes the ordered ordinary differentials
to the same ordered presheaf differentials of the original coordinate
functions. Apply the actual sheafification unit, retaining RAW sheaf-section
carriers on both sides. No native Gamma functor or differential frame enters.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalRawSections
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open NadelGlobalCanonicalTrace
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original raw coordinate sheaf wedge is the SAME sheafification of
the SAME ordinary coordinate top form, through the actual affine map.
Both sides have the RAW exterior-sheaf section carrier. -/
theorem ordinaryCoordinateSheafSection_eq (K : Type u) [Field K]
    (A : CommRingCat.{u}) [Algebra K A] (n : ℕ) (z : Fin n → A) :
    exteriorSheafSection (cotangentPresheaf (affineStructuralMap K A)) n ⊤
        (fun j => (cotangentPresheafDerivation (affineStructuralMap K A)).d
          (affineCoordinateMap A (op ⊤) (z j))) =
      ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K A)) n).app
        (op ⊤)).hom.toFun
        ((affineExteriorCotangentToOpen K A n (op ⊤)).hom.toFun
          (exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D K A (z j)))) := by
  have h := affineExteriorCotangentToOpen_wedge K A n (op ⊤)
    (fun j => KaehlerDifferential.D K A (z j))
  have hv : (fun j => (affineOrdinaryCotangentSemilinear K A (op ⊤)).toFun
      (KaehlerDifferential.D K A (z j))) =
      (fun j => (cotangentPresheafDerivation (affineStructuralMap K A)).d
        (affineCoordinateMap A (op ⊤) (z j))) :=
    funext (fun j => affineOrdinaryCotangentToOpen_D K A (op ⊤) (z j))
  have hw := h.trans (congrArg (exteriorPower.ιMulti Γ(Spec A, ⊤) n) hv)
  exact (congrArg
    ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K A)) n).app
      (op ⊤)).hom.toFun hw).symm

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalRawSections
