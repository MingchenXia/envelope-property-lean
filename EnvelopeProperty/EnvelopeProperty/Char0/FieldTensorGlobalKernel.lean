import EnvelopeProperty.Char0.FieldTensorAffineCharts
import EnvelopeProperty.Char0.AffineFieldQuotientKernel
import EnvelopeProperty.Algebra.FieldTensorIdealCoefficients
import EnvelopeProperty.Char0.SpecPushedKernelOpenCover
import EnvelopeProperty.AlgGeom.FlatModuleGlobalSections
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder

/-!
# The ENTIRE intrinsic pushed kernel on the actual changed original model

Actual tensor-chart geometry and every original coefficient identify the
whole original chart-kernel intersection with the intrinsic new-field
pushed quotient kernel, with no comparison certificate or geometric
integrality input.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EnvelopeProperty.CanonicalGeometry
open scoped TensorProduct

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace FieldTensorGlobalKernel

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  (A : CommRingCat.{u}) [Algebra k A] {Y : Scheme.{u}} (g : Y ⟶ Spec A)

/-- The SAME categorical original model pullback is the actual field-change pullback. -/
theorem model_isPullback :
    IsPullback (FlatGlobalSections.firstProjection (S := L ⊗[k] A) g)
      (FlatGlobalSections.structureMap (S := L ⊗[k] A) g ≫
        affineStructuralMap L (.of (L ⊗[k] A)))
      (g ≫ affineStructuralMap k A)
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  exact (IsPullback.of_hasPullback g _).paste_vert
    (isPullback_fieldTensor (k := k) (L := L) (A := A))

/-- Actual original pure smoothness manufactures pure smoothness on the actual changed model. -/
theorem model_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)] :
    SmoothOfRelativeDimension n
      (FlatGlobalSections.structureMap (S := L ⊗[k] A) g ≫
        affineStructuralMap L (.of (L ⊗[k] A))) :=
  smoothOfRelativeDimension_of_isPullback_specMap (model_isPullback (L := L) A g) n

/-- Actual original geometry supplies SNC on the SAME literal pulled original ideal. -/
theorem model_snc [CharZero k] (n : ℕ)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    (J.comap (FlatGlobalSections.firstProjection (S := L ⊗[k] A) g)).IsIdealOfSncDivisor := by
  let : Smooth (g ≫ affineStructuralMap k A) := SmoothOfRelativeDimension.smooth n _
  exact RoundedSncIdealSheaf.isIdealOfSncDivisor_comap_of_isPullback_specMap
    (model_isPullback (L := L) A g) J hJ

end FieldTensorGlobalKernel

namespace RoundedCanonicalModule

private theorem quotientKernel_congr_ideal
    {k : Type u} [Field k] (A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) {n : ℕ} (z : Fin n → A)
    (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    {J J' : (Spec B).IdealSheafData} (h : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ) :
    specQuotientKernel A B φ z hz J hJ q = specQuotientKernel A B φ z hz J' hJ' q := by
  cases h
  rfl

variable {k L : Type u} [Field k] [Field L] [CharZero k] [Algebra k L]
  (A : CommRingCat.{u}) [Algebra k A] {Y : Scheme.{u}} (g : Y ⟶ Spec A) {n : ℕ}
  [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]

/-- The WHOLE actual original pushed quotient-kernel extension equals the intrinsic new-field
kernel on the SAME actual original model pullback, for ALL q and ALL extended coefficients. -/
theorem specPushedQuotientKernel_fieldTensor
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    {ι : Type v} (B : ι → CommRingCat.{u}) [∀ i, Algebra k (B i)]
    (φ : (i : ι) → A →ₐ[k] B i) (j : (i : ι) → Spec (B i) ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (htriangle : ∀ i, j i ≫ g = Spec.map (CommRingCat.ofHom (φ i).toRingHom))
    (hcover : ∀ y : Y, ∃ (i : ι) (x : Spec (B i)), j i x = y)
    (v : (i : ι) → Fin n → B i)
    (hv : ∀ i, (MvPolynomial.aeval (R := k) (v i)).toRingHom.Etale) :
    (specPushedQuotientKernel A g z hz J hJ q).map
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom =
      specPushedQuotientKernel (.of (L ⊗[k] A))
        (FlatGlobalSections.structureMap (S := L ⊗[k] A) g)
        (fieldTensorCoordinates (k := k) (L := L) z) (etale_fieldTensorCoordinates z hz)
        (J.comap (FlatGlobalSections.firstProjection (S := L ⊗[k] A) g))
        (FieldTensorGlobalKernel.model_snc (L := L) A g n J hJ) q := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  let : Smooth (g ≫ affineStructuralMap k A) := SmoothOfRelativeDimension.smooth n _
  let gL := FlatGlobalSections.structureMap (S := L ⊗[k] A) g
  let p := FlatGlobalSections.firstProjection (S := L ⊗[k] A) g
  let : SmoothOfRelativeDimension n (gL ≫ affineStructuralMap L (.of (L ⊗[k] A))) :=
    FieldTensorGlobalKernel.model_smoothOfRelativeDimension (L := L) A g n
  let : Smooth (gL ≫ affineStructuralMap L (.of (L ⊗[k] A))) :=
    SmoothOfRelativeDimension.smooth n _
  let BL (i : ι) : CommRingCat.{u} := .of (L ⊗[k] B i)
  let φL (i : ι) : (L ⊗[k] A) →ₐ[L] BL i :=
    Algebra.TensorProduct.map (AlgHom.id L L) (φ i)
  let jL (i : ι) : Spec (BL i) ⟶ FlatGlobalSections.baseChange (S := L ⊗[k] A) g :=
    FieldTensorAffineCharts.chartMap (L := L) g (j i) (φ i) (htriangle i)
  let : ∀ i, IsOpenImmersion (jL i) := fun i =>
    FieldTensorAffineCharts.chartMap_isOpenImmersion g (j i) (φ i) (htriangle i)
  have htriangleL : ∀ i, jL i ≫ gL = Spec.map (CommRingCat.ofHom (φL i).toRingHom) :=
    fun i => FieldTensorAffineCharts.chartMap_snd g (j i) (φ i) (htriangle i)
  have hcoverL : ∀ y, ∃ i x, jL i x = y :=
    FieldTensorAffineCharts.chartMap_cover (L := L) g B j φ htriangle hcover
  have hOld := specPushedQuotientKernel_eq_iInf_open_cover A g z hz J hJ q B φ j htriangle hcover
  have hNew := specPushedQuotientKernel_eq_iInf_open_cover (.of (L ⊗[k] A)) gL
    (fieldTensorCoordinates (k := k) (L := L) z) (etale_fieldTensorCoordinates z hz)
    (J.comap p) (FieldTensorGlobalKernel.model_snc (L := L) A g n J hJ) q
    BL φL jL htriangleL hcoverL
  rw [hOld, hNew, FieldTensorIdealCoefficients.map_iInf_comap]
  apply iInf_congr
  intro i
  congr 1
  have hAffine := specQuotientKernel_fieldTensor (L := L) A (B i) (φ i) z hz
    (v i) (hv i) (J.comap (j i)) (hJ.comap_of_smooth (g ≫ affineStructuralMap k A) (j i)) q
  refine hAffine.trans (quotientKernel_congr_ideal _ _ _ _ _ ?_ _ _ q)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  exact congrArg (fun t => J.comap t)
    (FieldTensorAffineCharts.chartMap_fst (L := L) g (j i) (φ i) (htriangle i)).symm

end RoundedCanonicalModule

end EnvelopeProperty.Char0
