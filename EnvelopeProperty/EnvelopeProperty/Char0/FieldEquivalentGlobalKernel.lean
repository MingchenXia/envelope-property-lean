import EnvelopeProperty.Char0.FieldTensorModelEquivalence
import EnvelopeProperty.Char0.FieldTensorGlobalKernel
import EnvelopeProperty.Char0.SourceAlgebraEquivalenceKernel
import EnvelopeProperty.Char0.ModelIsomorphismKernel

/-!
# The entire actual changed-field kernel in an actual equivalent target

Both actual coefficient and categorical-model equivalences are produced
from a real field-tensor algebra equivalence. The target may be an actual
subalgebra of its own fraction field; no identification of valuation
families or desired kernel comparisons is supplied.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EnvelopeProperty.CanonicalGeometry
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace FieldEquivalentGlobalKernel

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  (A D : CommRingCat.{u}) [Algebra k A] [Algebra k D] [Algebra L D]
  [IsScalarTower k L D] (e : (L ⊗[k] A) ≃ₐ[L] D)
  {Y : Scheme.{u}} (g : Y ⟶ Spec A)

/-- The SAME categorical actual target-model pullback is the actual field-change model. -/
theorem model_isPullback :
    IsPullback (pullback.fst g (Spec.map (CommRingCat.ofHom
      (FieldTensorModelEquivalence.coefficientMap e).toRingHom)))
      (pullback.snd g (Spec.map (CommRingCat.ofHom
        (FieldTensorModelEquivalence.coefficientMap e).toRingHom)) ≫ affineStructuralMap L D)
      (g ≫ affineStructuralMap k A)
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
  (IsPullback.of_hasPullback g _).paste_vert
    (FieldTensorModelEquivalence.isPullback_coefficients e)

/-- Original pure smoothness supplies actual target-model pure smoothness. -/
theorem model_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)] :
    SmoothOfRelativeDimension n
      (pullback.snd g (Spec.map (CommRingCat.ofHom
        (FieldTensorModelEquivalence.coefficientMap e).toRingHom)) ≫ affineStructuralMap L D) :=
  smoothOfRelativeDimension_of_isPullback_specMap (model_isPullback A D e g) n

/-- Actual original SNC geometry supplies SNC on the SAME actual pulled ideal over D. -/
theorem model_snc [CharZero k] (n : ℕ)
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    (J.comap (pullback.fst g (Spec.map (CommRingCat.ofHom
      (FieldTensorModelEquivalence.coefficientMap e).toRingHom)))).IsIdealOfSncDivisor := by
  let : Smooth (g ≫ affineStructuralMap k A) := SmoothOfRelativeDimension.smooth n _
  exact RoundedSncIdealSheaf.isIdealOfSncDivisor_comap_of_isPullback_specMap
    (model_isPullback A D e g) J hJ

end FieldEquivalentGlobalKernel

namespace RoundedCanonicalModule

private theorem pushedKernel_congr
    {k : Type u} [Field k] (A : CommRingCat.{u}) [Algebra k A]
    {Y : Scheme.{u}} {g g' : Y ⟶ Spec A} (hg : g = g') {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    {J J' : Y.IdealSheafData} (h : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ) :
    specPushedQuotientKernel A g z hz J hJ q =
      specPushedQuotientKernel A g' z hz J' hJ' q := by
  cases hg
  cases h
  rfl

/-- The WHOLE actual original kernel extends to the actual intrinsic kernel in the actual coefficient-equivalent target. -/
theorem specPushedQuotientKernel_fieldTensorEquiv
    {k L : Type u} [Field k] [Field L] [CharZero k] [Algebra k L]
    (A D : CommRingCat.{u}) [Algebra k A] [Algebra k D] [Algebra L D]
    [IsScalarTower k L D] (e : (L ⊗[k] A) ≃ₐ[L] D)
    {Y : Scheme.{u}} (g : Y ⟶ Spec A) {n : ℕ}
    [SmoothOfRelativeDimension n (g ≫ affineStructuralMap k A)]
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)
    {ι : Type u} (B : ι → CommRingCat.{u}) [∀ i, Algebra k (B i)]
    (φ : (i : ι) → A →ₐ[k] B i) (j : (i : ι) → Spec (B i) ⟶ Y)
    [∀ i, IsOpenImmersion (j i)]
    (htriangle : ∀ i, j i ≫ g = Spec.map (CommRingCat.ofHom (φ i).toRingHom))
    (hcover : ∀ y : Y, ∃ (i : ι) (x : Spec (B i)), j i x = y)
    (v : (i : ι) → Fin n → B i)
    (hv : ∀ i, (MvPolynomial.aeval (R := k) (v i)).toRingHom.Etale) :
    (specPushedQuotientKernel A g z hz J hJ q).map
        (FieldTensorModelEquivalence.coefficientMap e).toRingHom =
      specPushedQuotientKernel D
        (pullback.snd g (Spec.map (CommRingCat.ofHom
          (FieldTensorModelEquivalence.coefficientMap e).toRingHom)))
        (fun i => e (fieldTensorCoordinates (k := k) (L := L) z i))
        (etale_coordinates_sourceAlgEquiv e _ (etale_fieldTensorCoordinates z hz))
        (J.comap (pullback.fst g (Spec.map (CommRingCat.ofHom
          (FieldTensorModelEquivalence.coefficientMap e).toRingHom))))
        (FieldEquivalentGlobalKernel.model_snc A D e g n J hJ) q := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  let gL := FlatGlobalSections.structureMap (S := L ⊗[k] A) g
  let pL := FlatGlobalSections.firstProjection (S := L ⊗[k] A) g
  let pD := Spec.map (CommRingCat.ofHom (FieldTensorModelEquivalence.coefficientMap e).toRingHom)
  let gTarget := pullback.snd g pD
  let pTarget := pullback.fst g pD
  let E := FieldTensorModelEquivalence.modelIso g e
  let gD := gL ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  let JL := J.comap pL
  let hJL := FieldTensorGlobalKernel.model_snc (k := k) (L := L) A g n J hJ
  let : SmoothOfRelativeDimension n (gL ≫ affineStructuralMap L (.of (L ⊗[k] A))) :=
    FieldTensorGlobalKernel.model_smoothOfRelativeDimension (L := L) A g n
  let : SmoothOfRelativeDimension n (gTarget ≫ affineStructuralMap L D) :=
    FieldEquivalentGlobalKernel.model_smoothOfRelativeDimension A D e g n
  have hgd : E.hom ≫ gTarget = gD := FieldTensorModelEquivalence.modelIso_snd g e
  let : SmoothOfRelativeDimension n (gD ≫ affineStructuralMap L D) := by
    rw [← hgd, Category.assoc]
    have hs : SmoothOfRelativeDimension (0 + n)
        (E.hom ≫ (gTarget ≫ affineStructuralMap L D)) := inferInstance
    simpa only [Nat.zero_add] using hs
  let : Smooth (gD ≫ affineStructuralMap L D) := SmoothOfRelativeDimension.smooth n _
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
  let vL (i : ι) := fieldTensorCoordinates (k := k) (L := L) (v i)
  let hvL (i : ι) := etale_fieldTensorCoordinates (L := L) (v i) (hv i)
  have hField := specPushedQuotientKernel_fieldTensor (L := L) A g z hz J hJ q
    B φ j htriangle hcover v hv
  have hSource := specPushedQuotientKernel_sourceAlgEquiv (.of (L ⊗[k] A)) D e gL
    (fieldTensorCoordinates (k := k) (L := L) z) (etale_fieldTensorCoordinates z hz)
    JL hJL q BL φL jL htriangleL hcoverL vL hvL
  have hBoth : (specPushedQuotientKernel A g z hz J hJ q).map
      (FieldTensorModelEquivalence.coefficientMap e).toRingHom =
      specPushedQuotientKernel D gD
        (fun i => e (fieldTensorCoordinates (k := k) (L := L) z i))
        (etale_coordinates_sourceAlgEquiv e _ (etale_fieldTensorCoordinates z hz)) JL hJL q := by
    rw [show (FieldTensorModelEquivalence.coefficientMap e).toRingHom =
      e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := k) (A := L)
        (B := A)).toRingHom from rfl, ← Ideal.map_map, hField]
    exact hSource
  have hModel := specPushedQuotientKernel_modelIso D gD E
    (fun i => e (fieldTensorCoordinates (k := k) (L := L) z i))
    (etale_coordinates_sourceAlgEquiv e _ (etale_fieldTensorCoordinates z hz)) JL hJL q
    BL (fun i => (φL i).comp e.symm.toAlgHom) jL
    (by
      intro i
      dsimp [gD]
      rw [← Category.assoc, htriangleL, ← Spec.map_comp]
      rfl) hcoverL
  have hgInv : E.inv ≫ gD = gTarget := by
    rw [← hgd, Iso.inv_hom_id_assoc]
  have hpInv : E.inv ≫ pL = pTarget := by
    have hp : E.hom ≫ pTarget = pL := FieldTensorModelEquivalence.modelIso_fst g e
    rw [← hp, Iso.inv_hom_id_assoc]
  have hJInv : JL.comap E.inv = J.comap pTarget := by
    change (J.comap pL).comap E.inv = _
    rw [← Scheme.IdealSheafData.comap_comp, hpInv]
  exact hBoth.trans (hModel.trans (pushedKernel_congr D hgInv _ _ hJInv _ _ q))

end RoundedCanonicalModule

end EnvelopeProperty.Char0
