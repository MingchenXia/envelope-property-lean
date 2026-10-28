/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupAffineReesLifts
import EnvelopeProperty.Global.FibreChartCover
import EnvelopeProperty.Projective.NormalizedSpectrum

/-!
# Faithful normalized affine-base projective points in the old blowup model

Prescribe the entire actual affine base seminorm of a point with value-one
selected coordinate. The genuine affine-base polynomial map constructs
normalized bigraded points, continuously and injectively. The actual Rees
kernel equations imply membership in the original blowup fibre. This file
does not yet assert surjectivity or the whole native Rees comparison.
-/

open scoped NNReal Topology
open Topology MvPolynomial EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (t : V.an) (i : Fin (M + 1)) (hi : (t : ProjBerk k M).1.val (X i) = 1)


private local instance affineReesPolynomialCommRing :
    CommRing (MvPolynomial (Fin (M' + 1)) (ProjBerk.QuotChartAlg V.ideal (X i) 1)) :=
  @AddMonoidAlgebra.commRing (ProjBerk.QuotChartAlg V.ideal (X i) 1) (Fin (M' + 1) →₀ ℕ)
    (Ideal.Quotient.commRing _) inferInstance

/-- The prescribed whole affine coefficient valuation forces the actual
trivial original field norm on every normalized affine-base point. -/
def fcAffineProjectiveBerk (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M') :
    Berk k (MvPolynomial (Fin (M' + 1)) (ProjBerk.QuotChartAlg V.ideal (X i) 1)) where
  val := w.1.1.val
  val_algebraMap c hc := by
    rw [IsScalarTower.algebraMap_apply k (ProjBerk.QuotChartAlg V.ideal (X i) 1) (MvPolynomial (Fin (M' + 1)) (ProjBerk.QuotChartAlg V.ideal (X i) 1))]
    exact (w.2 (algebraMap k (ProjBerk.QuotChartAlg V.ideal (X i) 1) c)).trans
      ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val_algebraMap c hc)

/-- The entire fixed affine coefficient seminorm normalizes all original
first coordinates with exact maximum one. -/
theorem fcAffineProjective_scaleX (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M') :
    BiProjBerk.scaleX (fcAffineReesPolynomial (V := V) i) (fcAffineProjectiveBerk t i hi w) = 1 := by
  change Finset.univ.sup (fun j => w.1.1.val (fcAffineReesPolynomial (V := V) i
    (X (Sum.inl j)))) = 1
  simp_rw [fcAffineReesPolynomial_X_inl, w.2]
  exact fc_baseChart_sup_X t i hi

/-- The genuine normalized projective second coordinates retain exact
maximum one under the actual original affine-base substitution. -/
theorem fcAffineProjective_scaleY (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M') :
    BiProjBerk.scaleY (fcAffineReesPolynomial (V := V) i) (fcAffineProjectiveBerk t i hi w) = 1 := by
  change Finset.univ.sup (fun m => w.1.1.val (fcAffineReesPolynomial (V := V) i
    (X (Sum.inr m)))) = 1
  simp_rw [fcAffineReesPolynomial_X_inr]
  exact w.1.sup_val_X

/-- The actual affine-base normalized seminorm constructs an old bigraded
point with no assumed comparison and no change of its coordinate scales. -/
def fcAffineProjectivePoint (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M') :
    BiProjBerk k M M' :=
  BiProjBerk.ofComap (fcAffineReesPolynomial (V := V) i) (fcAffineProjectiveBerk t i hi w)
    ((fcAffineProjective_scaleX t i hi w).trans_ne one_ne_zero)
    ((fcAffineProjective_scaleY t i hi w).trans_ne one_ne_zero)

/-- Every original bihomogeneous value is retained by the actual affine-base
substitution, since both genuine coordinate maxima equal one. -/
theorem fcAffineProjectivePoint_val (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M')
    {a b : ℕ} {F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k}
    (hF : F.IsWeightedHomogeneous (biWeight M M') (a, b)) :
    (fcAffineProjectivePoint t i hi w).1.val F = w.1.1.val (fcAffineReesPolynomial (V := V) i F) := by
  rw [fcAffineProjectivePoint, BiProjBerk.ofComap_val_of_isWeightedHomogeneous _ _ hF,
    fcAffineProjective_scaleX, fcAffineProjective_scaleY]
  simp only [one_pow, one_mul, div_one]
  rfl

/-- The first projection is the whole original base point, not merely its
prime support or its values on individual coordinate generators. -/
theorem fcAffineProjectivePoint_fst (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M') :
    BiProjBerk.fst (fcAffineProjectivePoint t i hi w) = (t : ProjBerk k M) := by
  apply ProjBerk.ext_of_isHomogeneous
  intro d F hF
  change (fcAffineProjectivePoint t i hi w).1.val (rename Sum.inl F) = _
  rw [fcAffineProjectivePoint_val t i hi w (isWeightedHomogeneous_rename_inl hF),
    fcAffineReesPolynomial_rename_inl, w.2, aeval_quotChartMk_X i hF,
    ProjSubvariety.chartMap_val_quotChartMk t (hi.trans_ne one_ne_zero)
      (by simpa only [mul_one] using hF), hi, one_pow, div_one]

/-- The constructed map is continuous on every entire original polynomial,
by the finite maximum formula for the actual bihomogeneous components. -/
theorem continuous_fcAffineProjectivePoint : Continuous (fcAffineProjectivePoint (M' := M') t i hi) := by
  apply BiProjBerk.continuous_iff.2
  intro F
  have he : (fun w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M' =>
      (fcAffineProjectivePoint t i hi w).1.val F) =
      (fun w => (weightSupport (biWeight M M') F).sup fun p =>
        w.1.1.val (fcAffineReesPolynomial (V := V) i
          (weightedHomogeneousComponent (biWeight M M') p F))) := by
    funext w
    rw [BiProjBerk.val_eq_sup]
    exact Finset.sup_congr rfl fun p _ => fcAffineProjectivePoint_val t i hi w
      (weightedHomogeneousComponent_isWeightedHomogeneous p F)
  rw [he]
  exact Continuous.finset_sup_apply fun p _ =>
    (Spectrum.continuous_val_apply _).comp (continuous_subtype_val.comp continuous_subtype_val)

/-- The constructed old point recovers the whole actual normalized source
seminorm by the genuinely constructed homogeneous polynomial preimages. -/
theorem fcAffineProjectivePoint_injective : Function.Injective (fcAffineProjectivePoint (M' := M') t i hi) := by
  intro w w' he
  apply Subtype.ext
  apply Subtype.ext
  apply Spectrum.ext_val
  intro Q
  rw [w.1.isGraded Q, w'.1.isGraded Q]
  apply Finset.sup_congr rfl
  intro b _
  obtain ⟨a, F, hF, eF⟩ := fcAffineReesPolynomial_homogeneous_preimage (V := V) i
    (homogeneousComponent_isHomogeneous b Q)
  have hv := congrArg (fun z : BiProjBerk k M M' => z.1.val F) he
  simpa only [fcAffineProjectivePoint_val t i hi w hF,
    fcAffineProjectivePoint_val t i hi w' hF, eF] using hv

variable (B : V.BlowupCenter M')

/-- The actual original Rees equations make the constructed point lie in
the actual original blowup ideal zero locus. -/
def fcAffineReesPoint (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M')
    (hw : ∀ Q ∈ ReesPresentation.kernel (B.centerGen i), w.1.1.val Q = 0) : B.an :=
  ⟨fcAffineProjectivePoint t i hi w, fun F hF => by
    rw [BiProjBerk.val_eq_sup]
    apply Finset.sup_eq_zero.2
    intro p _
    rw [fcAffineProjectivePoint_val t i hi w
      (weightedHomogeneousComponent_isWeightedHomogeneous p F)]
    exact hw _ (B.fcAffineReesPolynomial_mem_kernel i
      (B.weightedHomogeneousComponent_mem_ideal hF p))⟩

/-- The genuine Rees-equation point lies over the entire original base point. -/
theorem fcAffineReesPoint_proj (w : RelativeNormalizedProjectiveSpectrum ((V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val) M')
    (hw : ∀ Q ∈ ReesPresentation.kernel (B.centerGen i), w.1.1.val Q = 0) :
    B.proj (fcAffineReesPoint t i hi B w hw) = t :=
  Subtype.ext (fcAffineProjectivePoint_fst t i hi w)

end EnvelopeProperty.ProjSubvariety.BlowupCenter
