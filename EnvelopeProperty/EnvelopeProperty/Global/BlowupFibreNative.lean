/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Global.BlowupNativeFibreEmbedding
import EnvelopeProperty.Global.BlowupChartAtlas
import EnvelopeProperty.Global.ReesNormalizedChart

/-!
# The whole original blowup fibre and its actual native affine-base Rees fibre

Every original fibre point has a constructed nonzero-generator chart
representative. The actual normalized projective chart construction sends
that whole affine seminorm to the original Rees kernel locus and preserves
its full base seminorm. Exact polynomial triangles recover the entire old
chart point. Thus the actual native fixed-base map is a bijection; compact
native projective topology supplies the whole fibre homeomorphism.
-/

open scoped NNReal Topology
open Topology MvPolynomial EnvelopeProperty.Berkovich
noncomputable section
namespace EnvelopeProperty.ProjSubvariety.BlowupCenter
universe u
variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
    (B : V.BlowupCenter M') (i : Fin (M + 1))

section DomainChart
variable [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

/-- The entire actual affine Rees polynomial triangle equals the original
chart homomorphism, with no polynomial or point comparison witness. -/
theorem fcPaperPolynomialDehom_affineReesPolynomial (l : Fin (M' + 1)) :
    ((ReesPresentation.fcPaperPolynomialDehom (B.centerSet i) (B.centerGen i)
      (B.centerGen_mem_centerSet i) l).restrictScalars k).comp
        (fcAffineReesPolynomial (V := V) i) = B.chartHom i (B.centerGen i l) := by
  ext (j | m)
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, fcAffineReesPolynomial_X_inl,
      ReesPresentation.fcPaperPolynomialDehom, aeval_C, B.chartHom_X_inl]
    rfl
  · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, fcAffineReesPolynomial_X_inr,
      ReesPresentation.fcPaperPolynomialDehom, aeval_X, B.chartHom_X_inr]

variable (t : V.an) (hi : (t : ProjBerk k M).1.val (X i) = 1)

/-- The actual entire fixed affine base seminorm makes the original chart's
first normalization scale exactly one. -/
theorem fc_scaleX_chartHom_of_fixed_base (l : Fin (M' + 1))
    (w : Berk k (blowupChart (B.centerSet i) (B.centerGen i l)))
    (hw : Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) (B.centerGen i l)) w =
      V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)) :
    BiProjBerk.scaleX (B.chartHom i (B.centerGen i l)) w = 1 := by
  change Finset.univ.sup (fun j => w.val (B.chartHom i (B.centerGen i l) (X (Sum.inl j)))) = 1
  simp_rw [B.chartHom_X_inl]
  change Finset.univ.sup (fun j =>
    (Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) (B.centerGen i l)) w).val
      (ProjBerk.quotChartMk V.ideal (X i) 1 1 (X j))) = 1
  rw [hw]
  exact fc_baseChart_sup_X t i hi

/-- Each actual old fibre-chart representative constructs a normalized
point of the genuine entire original Rees kernel locus over the whole base. -/
def fcChartNormalizedReesPoint (l : Fin (M' + 1)) (hl : B.centerGen i l ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) (B.centerGen i l)))
    (hw : Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) (B.centerGen i l)) w =
      V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)) :
    {z : RelativeNormalizedProjectiveSpectrum (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val M' //
      ∀ Q ∈ ReesPresentation.kernel (B.centerGen i), z.1.1.val Q = 0} :=
  ⟨⟨ReesPresentation.fcPaperNormalizedPoint (B.centerSet i) (B.centerGen i)
      (B.centerGen_mem_centerSet i) l w.toSpectrum, fun a => by
        rw [ReesPresentation.fcPaperNormalizedPoint_val_C]
        exact congrArg (fun z => z.val a) hw⟩,
    fun _ hQ => ReesPresentation.fcPaperNormalizedPoint_kernel (B.centerSet i) (B.centerGen i)
      (B.centerGen_mem_centerSet i) l hl w.toSpectrum hQ⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constructed normalized Rees chart point recovers the entire old
chart point, by every original bihomogeneous polynomial value. -/
theorem fcAffineProjectivePoint_fcChartNormalizedReesPoint
    (l : Fin (M' + 1)) (hl : B.centerGen i l ≠ 0)
    (w : Berk k (blowupChart (B.centerSet i) (B.centerGen i l)))
    (hw : Berk.comap (EnvelopeProperty.chartMap k (B.centerSet i) (B.centerGen i l)) w =
      V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)) :
    fcAffineProjectivePoint t i hi (B.fcChartNormalizedReesPoint i t hi l hl w hw).1 =
      (B.chartPoint i (B.centerGen_mem_centerSet i l) hl w : BiProjBerk k M M') := by
  apply BiProjBerk.ext_of_isWeightedHomogeneous
  rintro ⟨a, b⟩ F hF
  rw [fcAffineProjectivePoint_val t i hi _ hF]
  change (ReesPresentation.fcPaperNormalizedPoint (B.centerSet i) (B.centerGen i)
    (B.centerGen_mem_centerSet i) l w.toSpectrum).1.val (fcAffineReesPolynomial (V := V) i F) = _
  have hδ := fcAffineReesPolynomial_isHomogeneous (V := V) i hF
  have hnorm := ReesPresentation.fcPaperNormalizedPoint_val (B.centerSet i) (B.centerGen i)
    (B.centerGen_mem_centerSet i) l hl w.toSpectrum hδ
  rw [hnorm]
  have he := AlgHom.congr_fun (B.fcPaperPolynomialDehom_affineReesPolynomial i l) F
  change ReesPresentation.fcPaperPolynomialDehom (B.centerSet i) (B.centerGen i)
    (B.centerGen_mem_centerSet i) l (fcAffineReesPolynomial (V := V) i F) =
      B.chartHom i (B.centerGen i l) F at he
  rw [he]
  change w.val (B.chartHom i (B.centerGen i l) F) /
    (Finset.univ.sup (fun m => w.val (chartFrac (B.centerSet i) (B.centerGen i l)
      (B.centerGen_mem_centerSet i m)))) ^ b = _
  have hp := B.chartPoint_val_of_isWeightedHomogeneous (B.centerGen_mem_centerSet i l) hl w hF
  have hx := B.fc_scaleX_chartHom_of_fixed_base i t hi l w hw
  have hsy : BiProjBerk.scaleY (B.chartHom i (B.centerGen i l)) w =
      Finset.univ.sup (fun m => w.val (chartFrac (B.centerSet i) (B.centerGen i l)
        (B.centerGen_mem_centerSet i m))) := by
    unfold BiProjBerk.scaleY
    simp only [B.chartHom_X_inr]
  rw [hx, hsy, one_pow, one_mul] at hp
  exact hp.symm

end DomainChart

/-- Every point of the whole original blowup fibre has a genuine native
point of the actual original affine-base Rees scheme as preimage. -/
theorem fcNativeFibrePoint_surjective (t : V.an)
    (hi : (t : ProjBerk k M).1.val (X i) = 1) :
    Function.Surjective (B.fcNativeFibrePoint t i hi) := by
  let := fc_isDomain_baseChart t i hi
  intro y
  obtain ⟨l, hl, w, hw, he⟩ := B.fc_exists_chartPoint_eq i t hi y.1 y.2
  let z := B.fcChartNormalizedReesPoint i t hi l hl w hw
  let e := ReesPresentation.fcNativeNormalizedHomeomorph (B.centerGen i)
    (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val
  refine ⟨e.symm z, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change fcAffineProjectivePoint t i hi (e (e.symm z)).1 = (y.1 : BiProjBerk k M M')
  rw [e.apply_symm_apply]
  exact (B.fcAffineProjectivePoint_fcChartNormalizedReesPoint i t hi l hl w hw).trans
    (congrArg Subtype.val he)

/-- The whole original fibre is homeomorphic to the entire native valued
point space of the actual original affine-base Rees quotient scheme.
Both injectivity and surjectivity are proved; no comparison premise is added. -/
def fcNativeFibreHomeomorph (t : V.an)
    (hi : (t : ProjBerk k M).1.val (X i) = 1) :
    RelativeSchemeValuedPoint (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val
      (ReesPresentation.fcFiniteProjection (B.centerGen i)) ≃ₜ {y : B.an // B.proj y = t} := by
  let : CompactSpace (RelativeSchemeValuedPoint
      (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val
      (ReesPresentation.fcFiniteProjection (B.centerGen i))) :=
    ProjBerk.compactSpace_nativeClosedProjective _ (ReesPresentation.fcFiniteImmersion (B.centerGen i))
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (B.fcNativeFibrePoint t i hi)
      ⟨B.fcNativeFibrePoint_injective t i hi, B.fcNativeFibrePoint_surjective i t hi⟩)
    (B.continuous_fcNativeFibrePoint t i hi)

/-- The whole native fibre homeomorphism is exactly the constructed original
seminorm map, retaining its actual fixed base projection. -/
@[simp]
theorem fcNativeFibreHomeomorph_apply (t : V.an)
    (hi : (t : ProjBerk k M).1.val (X i) = 1)
    (x : RelativeSchemeValuedPoint (V.chartMap (X i) 1 t (hi.trans_ne one_ne_zero)).val
      (ReesPresentation.fcFiniteProjection (B.centerGen i))) :
    B.fcNativeFibreHomeomorph i t hi x = B.fcNativeFibrePoint t i hi x := rfl

end EnvelopeProperty.ProjSubvariety.BlowupCenter
