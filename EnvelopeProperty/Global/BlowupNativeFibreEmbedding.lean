/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupAffineReesPoints
import EnvelopeProperty.Global.ReesNormalizedNative

/-!
# A genuine native Rees fibre map into the whole original blowup fibre

This composes the actual native Rees quotient-Proj kernel-locus
homeomorphism with the constructed old-model normalized point map.
It is continuous and injective and retains the entire original base
point. Surjectivity and the full fibre homeomorphism are not assumed.
-/

open scoped NNReal Topology
open Topology MvPolynomial EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (t : V.an) (i : Fin (M + 1))
    (hi : (t : ProjBerk k M).1.val (X i) = 1)

/-- The actual native fixed-base Rees point constructs a point of the whole
original blowup fibre, through the actual original polynomial map. -/
def fcNativeFibrePoint
    (x : RelativeSchemeValuedPoint (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val
      (ReesPresentation.fcFiniteProjection (B.centerGen i))) : {y : B.an // B.proj y = t} :=
  let w := ReesPresentation.fcNativeNormalizedHomeomorph (B.centerGen i)
    (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val x
  ⟨fcAffineReesPoint t i hi B w.1 w.2, fcAffineReesPoint_proj t i hi B w.1 w.2⟩

/-- Every original bihomogeneous value is retained by the whole actual
native fixed-base map through the genuine affine-base polynomial substitution. -/
theorem fcNativeFibrePoint_val
    (x : RelativeSchemeValuedPoint (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val
      (ReesPresentation.fcFiniteProjection (B.centerGen i)))
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    ((B.fcNativeFibrePoint t i hi x).1 : BiProjBerk k M M').1.val F =
      (ReesPresentation.fcNativeNormalizedHomeomorph (B.centerGen i)
        (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val x).1.1.1.val
          (fcAffineReesPolynomial (V := V) i F) :=
  fcAffineProjectivePoint_val t i hi _ hF

/-- The constructed whole native fibre map is continuous through the actual
native quotient-Proj topology and the actual original subspace fibre topology. -/
theorem continuous_fcNativeFibrePoint : Continuous (B.fcNativeFibrePoint t i hi) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_fcAffineProjectivePoint t i hi).comp
    (continuous_subtype_val.comp (ReesPresentation.fcNativeNormalizedHomeomorph (B.centerGen i)
      (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val).continuous)

/-- The whole native Rees fixed-base point is recovered from its original
blowup image, using every homogeneous original polynomial preimage. -/
theorem fcNativeFibrePoint_injective : Function.Injective (B.fcNativeFibrePoint t i hi) := by
  intro x y h
  apply (ReesPresentation.fcNativeNormalizedHomeomorph (B.centerGen i)
    (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val).injective
  apply Subtype.ext
  apply fcAffineProjectivePoint_injective t i hi
  exact congrArg (fun z : {y : B.an // B.proj y = t} => (z.1 : BiProjBerk k M M')) h

end EnvelopeProperty.ProjSubvariety.BlowupCenter
