import EnvelopeProperty.Vanishing.RelativeFiniteAmpleClosedBase
import EnvelopeProperty.Vanishing.NadelFiniteAmplePullback

/-! # Actual finite pullback ampleness over the original arbitrary ring

The coefficient-image domain is constructed internally from the integral
target. Closed coefficient-base comparison returns the actual original
line and composite map to the original base, retaining the whole finite source.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.RelativeFiniteAmplePullback
open GeneratedLineProjectiveAffineMap

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual image of the original coefficient homomorphism in global sections. -/
def coefficientImage (p : X ⟶ Spec (.of R)) : Subring Γ(X, ⊤) :=
  (baseCoefficients p).range

/-- The literal surjection from the original coefficient ring to its image. -/
def coefficientImageMap (p : X ⟶ Spec (.of R)) : R →+* coefficientImage p :=
  (baseCoefficients p).rangeRestrict

/-- The original scheme's canonical map to the spectrum of its coefficient image. -/
def coefficientImageStructure (p : X ⟶ Spec (.of R)) :
    X ⟶ Spec (.of (coefficientImage p)) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (coefficientImage p).subtype)

/-- The literal original coefficient map is retained on the whole original scheme. -/
theorem coefficientImageStructure_comp (p : X ⟶ Spec (.of R)) :
    coefficientImageStructure p ≫ Spec.map (CommRingCat.ofHom (coefficientImageMap p)) = p := by
  rw [coefficientImageStructure, Category.assoc, ← Spec.map_comp]
  change X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (baseCoefficients p)) = p
  have h : CommRingCat.ofHom (baseCoefficients p) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop := rfl
  rw [h, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality p,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- Surjectivity is derived from the actual original coefficient image. -/
theorem coefficientImageMap_surjective (p : X ⟶ Spec (.of R)) :
    Function.Surjective (coefficientImageMap p) :=
  (baseCoefficients p).rangeRestrict_surjective

/-- The original ample line is ample over the internally constructed coefficient
image, with no change to the original scheme or line. -/
theorem isAmple_over_coefficientImage (p : X ⟶ Spec (.of R)) (L : X.Modules)
    (hL : SchemeLineAmpleness.IsAmple p L) :
    SchemeLineAmpleness.IsAmple (coefficientImageStructure p) L :=
  (RelativeFiniteAmpleClosedBase.isAmple_closedBase_iff (coefficientImageMap p)
    (coefficientImageMap_surjective p) p (coefficientImageStructure p)
    (coefficientImageStructure_comp p) L).mpr hL

/-- Actual finite pullback of the original ample line over an arbitrary original
coefficient ring. Only the target is integral; the entire finite source is retained. -/
theorem isAmple_pullback [IsIntegral X] {Y : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (L : X.Modules)
    (hL : SchemeLineAmpleness.IsAmple p L) (π : Y ⟶ X) [IsFinite π] :
    SchemeLineAmpleness.IsAmple (π ≫ p) ((pullback π).obj L) := by
  let : IsDomain (coefficientImage p) := inferInstance
  have hA := NadelFiniteAmplePullback.isAmple_pullback (coefficientImageStructure p) L
    (isAmple_over_coefficientImage p L hL) π
  have hR := RelativeFiniteAmpleClosedBase.isAmple_comp_of_surjective
    (coefficientImageMap p) (coefficientImageMap_surjective p)
    (π ≫ coefficientImageStructure p) ((pullback π).obj L) hA
  rwa [Category.assoc, coefficientImageStructure_comp] at hR

end EnvelopeProperty.Vanishing.RelativeFiniteAmplePullback
