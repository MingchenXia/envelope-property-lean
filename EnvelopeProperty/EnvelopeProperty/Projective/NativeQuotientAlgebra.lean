/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Projective.NativeQuotientSections
import EnvelopeProperty.SchemeImageFlat

open CategoryTheory AlgebraicGeometry Opposite
open EnvelopeProperty.Berkovich
noncomputable section
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] {n : ℕ}

private theorem coordinateCoefficients_ringHom (j : Fin (n + 1)) :
    CommRingCat.ofHom (algebraMap R (CoordinateRing R j)) ≫
      (nativeCoordinateSectionsIso (R := R) j).hom =
        CommRingCat.ofHom (SchemeValuedPoint.sectionBaseMap (nativeStructureMap (R := R) (n := n))
          (nativeCoordinateOpen (R := R) j)) := by
  apply (cancel_mono ((nativeCoordinateOpen (R := R) j).topIso.inv ≫
    (nativeCoordinateSchemeIso (R := R) j).inv.appTop)).mp
  simp only [Category.assoc]
  rw [nativeCoordinateSectionsIso_cancel]
  have hr : (NativeProjectiveScheme R n).presheaf.map
      (homOfLE (show nativeCoordinateOpen (R := R) j ≤ ⊤ from le_top)).op ≫
        (nativeCoordinateOpen (R := R) j).topIso.inv = (nativeCoordinateOpen (R := R) j).ι.appTop := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop, ← Functor.map_comp]
    rfl
  change CommRingCat.ofHom (algebraMap R (CoordinateRing R j)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R j))).inv =
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (nativeStructureMap (R := R) (n := n)).appTop ≫
      (NativeProjectiveScheme R n).presheaf.map (homOfLE le_top).op) ≫
        (nativeCoordinateOpen (R := R) j).topIso.inv ≫ (nativeCoordinateSchemeIso (R := R) j).inv.appTop
  simp only [Category.assoc]
  rw [← Category.assoc _ (nativeCoordinateOpen (R := R) j).topIso.inv, hr]
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
    Category.assoc, nativeCoordinateChart_over_base, Scheme.ΓSpecIso_inv_naturality]

/-- The existing native coordinate section equivalence preserves the original coefficients. -/
theorem nativeCoordinateSectionsIso_coefficients (j : Fin (n + 1)) (r : R) :
    (nativeCoordinateSectionsIso (R := R) j).hom.hom (algebraMap R (CoordinateRing R j) r) =
      SchemeValuedPoint.sectionBaseMap (nativeStructureMap (R := R) (n := n)) (nativeCoordinateOpen (R := R) j) r :=
  congrArg (fun f => f.hom r) (coordinateCoefficients_ringHom j)

/-- The SAME original quotient-section equivalence is linear for its actual structure-map action. -/
def nativeQuotientCoordinateSectionsAlgEquiv
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (j : Fin (n + 1)) :
    let I := GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J
    letI := SchemeValuedPoint.sectionBaseAlgebra (I.subschemeι ≫ (nativeStructureMap (R := R) (n := n)))
      (I.subschemeι ⁻¹ᵁ nativeCoordinateOpen (R := R) j)
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ nativeCoordinateOpen (R := R) j) ≃ₐ[R]
      CoordinateRing R j ⧸ J.toIdeal.map (coordinateDehom j).toRingHom := by
  let I := GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J
  letI := SchemeValuedPoint.sectionBaseAlgebra (I.subschemeι ≫ (nativeStructureMap (R := R) (n := n)))
    (I.subschemeι ⁻¹ᵁ nativeCoordinateOpen (R := R) j)
  refine { nativeQuotientCoordinateSectionsEquiv J j with commutes' := ?_ }
  intro r
  have hn := RingHom.congr_fun (SchemeImage.sectionBaseMap_comp_app (RingHom.id R)
    (I.subschemeι ≫ (nativeStructureMap (R := R) (n := n))) (nativeStructureMap (R := R) (n := n)) I.subschemeι (by simp)
    (nativeCoordinateOpen (R := R) j)) r
  have he := nativeQuotientCoordinateSectionsEquiv_pullback J j
    (algebraMap R (CoordinateRing R j) r)
  rw [nativeCoordinateSectionsIso_coefficients] at he
  change nativeQuotientCoordinateSectionsEquiv J j
    (SchemeValuedPoint.sectionBaseMap (I.subschemeι ≫ (nativeStructureMap (R := R) (n := n)))
      (I.subschemeι ⁻¹ᵁ nativeCoordinateOpen (R := R) j) r) = _
  simpa only [RingHom.comp_apply, RingHom.id_apply] using hn ▸ he
end EnvelopeProperty.ProjBerk
