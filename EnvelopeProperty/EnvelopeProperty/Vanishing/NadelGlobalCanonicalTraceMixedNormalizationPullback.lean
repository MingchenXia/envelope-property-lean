import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitBase
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceNative

/-! # The original native canonical input of the whole mixed counit

This is the actual original affine algebra-map differential on the same
whole mixed source, with its original field structure and original A action.
No normalization, comparison or target canonical frame is supplied.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
local notation "Bₘ" => mixedRing x N I σ u

/-- The actual original canonical differential into the SAME entire
original mixed canonical module, with its ORIGINAL coefficient action. -/
def mixedNativeCanonicalPullback
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n) ⟶
      mixedCanonicalModuleOverBase (k := k) x N I σ u := by
  let := coordinateStructure_smooth x hx
  exact affineAlgebraCanonicalPullbackMap (.of A) (.of Bₘ)
    (IsScalarTower.toAlgHom k A Bₘ) n

/-- The original base coordinate generator has its actual original
image under the SAME entire mixed canonical differential. -/
theorem mixedNativeCanonicalPullback_coordinate
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale) :
    mixedNativeCanonicalPullback x N I σ u hx
      (affineCanonicalCoordinateSection k (.of A) n x) =
      affineCanonicalCoordinateSection k (.of Bₘ) n
        (fun j => algebraMap A Bₘ (x j)) := by
  let := coordinateStructure_smooth x hx
  exact affineAlgebraCanonicalPullbackMap_coordinate_wedge (.of A) (.of Bₘ)
    (IsScalarTower.toAlgHom k A Bₘ) n x

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
