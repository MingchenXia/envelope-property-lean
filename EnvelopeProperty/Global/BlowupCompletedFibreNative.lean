/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupFibreNative
import EnvelopeProperty.Berkovich.SchemeCompletedFibre

/-!
# The literal proper completed-residue Rees scheme fibre of the whole old fibre

The actual affine base point supplies its genuine completed stalk residue
field. The literal scheme pullback of the constructed proper original Rees
projection gives a proper scheme over that field. The generic native
completed-fibre comparison and the proved whole original-fibre comparison
supply the homeomorphism, with the entire native projection retained.
-/

open scoped NNReal Topology
open CategoryTheory AlgebraicGeometry EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (MvPolynomial.X i) = 1)

/-- The actual whole native affine base point, constructed from the original
entire affine quotient-chart seminorm. -/
def fcNativeBasePoint : SchemeValuedPoint (Spec (CommRingCat.of
    (ProjBerk.QuotChartAlg V.ideal (MvPolynomial.X i) 1))) :=
  SchemeValuedPoint.basePoint
    (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).val

/-- The literal scheme pullback to the actual completed stalk residue field
of the original native affine base point. -/
abbrev fcNativeCompletedFibre : Scheme.{u} :=
  SchemeCompletedFibre.model (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (fcNativeBasePoint t i hi)

/-- The literal completed-residue structure morphism of that same scheme fibre. -/
abbrev fcNativeCompletedFibreStructure : B.fcNativeCompletedFibre t i hi ⟶
    Spec (CommRingCat.of (SchemeValuedPoint.H (fcNativeBasePoint t i hi))) :=
  SchemeCompletedFibre.structureMap (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (fcNativeBasePoint t i hi)

/-- Properness is derived by actual scheme base change from the genuine
proper finite-index Rees projection; no model or properness is assumed. -/
instance fcNativeCompletedFibreStructure_isProper : IsProper (B.fcNativeCompletedFibreStructure t i hi) := by
  dsimp only [fcNativeCompletedFibreStructure, SchemeCompletedFibre.structureMap]
  infer_instance

/-- The entire old blowup fibre is the fixed-norm native point space of the
literal proper scheme fibre over the actual completed native base residue field. -/
def fcNativeCompletedFibreHomeomorph :
    RelativeSchemeValuedPoint (NormedField.valuation (K := SchemeValuedPoint.H (fcNativeBasePoint t i hi)))
      (B.fcNativeCompletedFibreStructure t i hi) ≃ₜ {y : B.an // B.proj y = t} :=
  (SchemeCompletedFibre.nativeFibreHomeomorph (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (fcNativeBasePoint t i hi)).trans (B.fcNativeFibreHomeomorph i t hi)

/-- The inverse completed-fibre comparison retains the entire original
native Rees point under the literal scheme pullback projection. -/
theorem fcNativeCompletedFibreHomeomorph_symm_projection (y : {y : B.an // B.proj y = t}) :
    SchemeValuedPoint.map (SchemeCompletedFibre.projection
      (ReesPresentation.fcFiniteProjection (B.centerGen i)) (fcNativeBasePoint t i hi))
        ((B.fcNativeCompletedFibreHomeomorph t i hi).symm y).1 =
      ((B.fcNativeFibreHomeomorph i t hi).symm y).1 :=
  SchemeCompletedFibre.projection_map_nativeFibreHomeomorph_symm
    (ReesPresentation.fcFiniteProjection (B.centerGen i)) (fcNativeBasePoint t i hi)
    ((B.fcNativeFibreHomeomorph i t hi).symm y)

/-- The literal Rees scheme fibre over the completion of the entire
original affine seminorm; this is the field convention of the proved
intrinsic chart-psh producers. -/
abbrev fcAffineCompletedFibre : Scheme.{u} :=
  SchemeCompletedFibre.affineBaseModel (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum

/-- The exact completed-affine-seminorm structure map of the same literal
scheme fibre, with the field convention used by the actual local psh charts. -/
abbrev fcAffineCompletedFibreStructure : B.fcAffineCompletedFibre t i hi ⟶
    Spec (CommRingCat.of (Spectrum.H
      (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum)) :=
  SchemeCompletedFibre.affineBaseStructureMap (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum

/-- Actual properness also holds for the affine-seminorm completion convention
by the literal proper Rees scheme base change. -/
instance fcAffineCompletedFibreStructure_isProper : IsProper (B.fcAffineCompletedFibreStructure t i hi) := by
  dsimp only [fcAffineCompletedFibreStructure, SchemeCompletedFibre.affineBaseStructureMap]
  infer_instance

/-- The whole original fibre is the whole fixed-norm native space of the
literal actual Rees fibre over the completed original affine seminorm. -/
def fcAffineCompletedFibreHomeomorph :
    RelativeSchemeValuedPoint (NormedField.valuation (K := Spectrum.H
      (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum))
      (B.fcAffineCompletedFibreStructure t i hi) ≃ₜ {y : B.an // B.proj y = t} :=
  (SchemeCompletedFibre.affineBaseFibreHomeomorph (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum).trans
      (B.fcNativeFibreHomeomorph i t hi)

/-- The affine-completion comparison retains the entire original native Rees
point under the actual same scheme pullback projection. -/
theorem fcAffineCompletedFibreHomeomorph_symm_projection (y : {y : B.an // B.proj y = t}) :
    SchemeValuedPoint.map (SchemeCompletedFibre.affineBaseProjection
      (ReesPresentation.fcFiniteProjection (B.centerGen i))
        (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum)
        ((B.fcAffineCompletedFibreHomeomorph t i hi).symm y).1 =
      ((B.fcNativeFibreHomeomorph i t hi).symm y).1 :=
  SchemeCompletedFibre.affineBaseProjection_map_affineBaseFibreHomeomorph_symm
    (ReesPresentation.fcFiniteProjection (B.centerGen i))
    (V.chartMap (MvPolynomial.X i) 1 t (hi.trans_ne one_ne_zero)).toSpectrum
    ((B.fcNativeFibreHomeomorph i t hi).symm y)

end EnvelopeProperty.ProjSubvariety.BlowupCenter
