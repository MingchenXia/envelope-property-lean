import EnvelopeProperty.Vanishing.NadelBertiniUniversal
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Actual original coordinate sections produce their own whole source frames -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniProjectiveFrames
open NadelBertiniUniversal SchemeLineSectionEvaluation SchemeLineSectionFactorization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}
  (j : X ⟶ Alterations.projectiveSpace R m)

/-- The genuine original preimage of the original native coordinate open. -/
def sourceOpen (a : Fin (m + 1)) : X.Opens := j ⁻¹ᵁ coordinateOpen (R := R) a

/-- The original whole coordinate section after original source pullback. -/
def sectionHom (a : Fin (m + 1)) : unitObj X ⟶ projectiveLine j :=
  pullbackSectionHom j
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) (0 : Fin (m + 1)) a 1)

private theorem ambient_isIso (a : Fin (m + 1)) :
    IsIso (pullbackSectionHom (coordinateOpen (R := R) a).ι
      (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) (0 : Fin (m + 1)) a 1)) := by
  let hmap := (NatIso.isIso_map_iff
    (restrictFunctorIsoPullback (coordinateOpen (R := R) a).ι)
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) (0 : Fin (m + 1)) a 1)).mp
    (ProjectiveTwistGlobalGeneration.coordinateSectionHom_isIso_on_own_chart
      (R := R) (0 : Fin (m + 1)) a 1)
  change IsIso ((pullbackUnitIso (coordinateOpen (R := R) a).ι).inv ≫ _)
  exact IsIso.comp_isIso' (pullbackUnitIso (coordinateOpen (R := R) a).ι).isIso_inv hmap

/-- The actual same coordinate section is invertible on its actual original source open. -/
theorem section_isIso (a : Fin (m + 1)) :
    IsIso (pullbackSectionHom (sourceOpen j a).ι (sectionHom j a)) := by
  let U := sourceOpen j a
  let V := coordinateOpen (R := R) a
  let c := ProjectiveTwistGlobalGeneration.coordinateSectionHom (R := R) (0 : Fin (m + 1)) a 1
  have hc : IsIso (pullbackSectionHom (U.ι ≫ j) c) :=
    isIso_pullbackSectionHom_factor (j.resLE V U le_rfl) V.ι (U.ι ≫ j)
      (j.resLE_comp_ι le_rfl) c (ambient_isIso a)
  have hw : pullbackSectionHom U.ι (pullbackSectionHom j c) ≫
      (frameFactorIso U.ι j (U.ι ≫ j) rfl
        (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)).hom =
      pullbackSectionHom (U.ι ≫ j) c :=
    pullbackSectionHom_factor U.ι j (U.ι ≫ j) rfl c
  let : IsIso (pullbackSectionHom U.ι (pullbackSectionHom j c) ≫
      (frameFactorIso U.ι j (U.ι ≫ j) rfl
        (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)).hom) := hw.symm ▸ hc
  change IsIso (pullbackSectionHom U.ι (pullbackSectionHom j c))
  exact IsIso.of_isIso_comp_right _
    (frameFactorIso U.ι j (U.ι ≫ j) rfl
      (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1)).hom

/-- The original coordinate section itself constructs the actual normalized frame. -/
def coordinateFrame (a : Fin (m + 1)) :
    (Scheme.Modules.pullback (sourceOpen j a).ι).obj (projectiveLine j) ≅
      unitObj (sourceOpen j a).toScheme := by
  let := section_isIso j a
  exact (asIso (pullbackSectionHom (sourceOpen j a).ι (sectionHom j a))).symm

/-- The same original coordinate section is precisely one in its own constructed frame. -/
theorem coordinateFrame_section (a : Fin (m + 1)) :
    pullbackSectionHom (sourceOpen j a).ι (sectionHom j a) ≫ (coordinateFrame j a).hom = 𝟙 _ := by
  let := section_isIso j a
  exact (asIso (pullbackSectionHom (sourceOpen j a).ι (sectionHom j a))).hom_inv_id

/-- A genuine original closed projective embedding has actual affine coordinate preimages. -/
theorem sourceOpen_affine [IsClosedImmersion j] (a : Fin (m + 1)) :
    IsAffineOpen (sourceOpen j a) := by
  let : IsAffineHom j := inferInstance
  exact @IsAffineOpen.preimage _ _ _ (coordinateOpen_isAffineOpen (R := R) a) j
    (inferInstanceAs (IsAffineHom j))

end EnvelopeProperty.Vanishing.NadelBertiniProjectiveFrames
