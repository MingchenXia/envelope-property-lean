import EnvelopeProperty.Char0.FieldEquivalentGlobalKernel
import EnvelopeProperty.Char0.SequenceMultiplierKernel
import EnvelopeProperty.Char0.PrincipalizationLeafJacobians
import EnvelopeProperty.Char0.BlowUpOpenIso
import Mathlib.RingTheory.Flat.Basic

/-!
# Whole intrinsic multiplier ideals under actual extension of fields

The actual original resolved sequence is pulled back along the literal
coefficient action. The original and changed all-DVR ideals are computed
independently by actual resolved sequences. No equality or scalar-extension
identification between their full valuation indexing families is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CanonicalGeometry
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual field coefficient map preserves every actual nonzero original ideal. -/
theorem valuativeFieldTargetIdeal_ne_bot
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (A D : CommRingCat.{u}) [Algebra k A] [Algebra k D] [Algebra L D]
    [IsScalarTower k L D] (e : (L ⊗[k] A) ≃ₐ[L] D) (I : Ideal A) (hI : I ≠ ⊥) :
    I.map (FieldTensorModelEquivalence.coefficientMap e).toRingHom ≠ ⊥ := by
  have hinj : Function.Injective (FieldTensorModelEquivalence.coefficientMap e) :=
    e.injective.comp (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective)
  obtain ⟨a, ha, ha0⟩ := I.ne_bot_iff.mp hI
  intro hzero
  have hmem := Ideal.mem_map_of_mem (FieldTensorModelEquivalence.coefficientMap e).toRingHom ha
  rw [hzero, Ideal.mem_bot] at hmem
  exact ha0 (hinj (hmem.trans (map_zero _).symm))

/-- Actual natural resolved-sequence geometry manufactures actual etale coordinates on an actual covering tree. -/
theorem exists_resolvedSequence_etale_cover
    {k K : Type u} [Field k] [Field K] [Algebra k K] [CharZero k]
    (C : Subalgebra k K) [IsFractionRing C K] (n : ℕ) (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (S : Scheme.BlowUpSequence (Spec (.of C)))
    [SmoothOfRelativeDimension n (S.composite ≫ affineStructuralMap k (.of C))]
    [IsIso (S.composite ∣_ (specIdealSheaf I).support.compl)]
    (hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor) :
    ∃ (T : ReesChartTree k K C)
      (j : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ S.last),
      (∀ i, IsOpenImmersion (j i)) ∧
      (∀ i, j i ≫ S.composite = subalgebraSpecMap
        (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
      (∀ y : S.last, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), j i x = y) ∧
      ∃ (v : (i : T.LeafIndex) → Fin n → T.leafAlgebra i),
        ∀ i, (MvPolynomial.aeval (R := k) (v i)).toRingHom.Etale := by
  let f := affineStructuralMap k (.of C)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth f := SmoothOfRelativeDimension.smooth n _
  have hbase : IsNoetherian (Spec (.of C)) := f.isNoetherian_of_field
  have hfinal : IsNoetherian S.last := @Hironaka.Resolution.isNoetherian_stage
    (Spec (.of C)) hbase S (Fin.last _)
  let : CompactSpace S.last := hfinal.toCompactSpace
  let : Smooth (S.composite ≫ f) := SmoothOfRelativeDimension.smooth n _
  let : SmoothOfRelativeDimension n (S.composite ≫
      Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    (inferInstance : SmoothOfRelativeDimension n (S.composite ≫ affineStructuralMap k (.of C)))
  have hCovers := exists_snc_jacobian_rees_cover C (fg_of_etale_coordinates C z hz) S n
    (specIdealSheaf I) hJ (nonempty_compl_support_specIdealSheaf I hI) z hz
  obtain ⟨F, d, hF, hmon, T, j, hopen, htriangle, hcover, hleaf⟩ :=
    exists_etale_monomial_jacobian_rees_cover C S.composite n (specIdealSheaf I) z hz hCovers
  have hv : ∀ i : T.LeafIndex, ∃ v : Fin n → T.leafAlgebra i,
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
    intro i
    obtain ⟨x, hx, v, hv, hrest⟩ := hleaf i
    exact ⟨v, hv⟩
  choose v hv using hv
  exact ⟨T, j, hopen, htriangle, hcover, v, hv⟩

private theorem pushedKernel_congr
    {k : Type u} [Field k] (A : CommRingCat.{u}) [Algebra k A]
    {Y : Scheme.{u}} {g g' : Y ⟶ Spec A} (hg : g = g') {n : ℕ}
    (z : Fin n → A) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    {J J' : Y.IdealSheafData} (h : J = J')
    (hJ : J.IsIdealOfSncDivisor) (hJ' : J'.IsIdealOfSncDivisor) (q : ℚ) :
    RoundedCanonicalModule.specPushedQuotientKernel A g z hz J hJ q =
      RoundedCanonicalModule.specPushedQuotientKernel A g' z hz J' hJ' q := by
  cases hg
  cases h
  rfl

/-- The ENTIRE original intrinsic all-DVR ideal extends to the ENTIRE actual new-field intrinsic ideal. -/
theorem valuativeMultiplierIdeal_fieldTensorEquiv
    {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra L M] [CharZero k]
    (C : Subalgebra k K) [IsFractionRing C K]
    (D : Subalgebra L M) [IsFractionRing D M] [Algebra k D] [IsScalarTower k L D]
    (e : (L ⊗[k] C) ≃ₐ[L] D) {n : ℕ}
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    letI : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
    (valuativeMultiplierIdeal C I hI q).map
        (FieldTensorModelEquivalence.coefficientMap (A := .of C) (D := .of D) e).toRingHom =
      valuativeMultiplierIdeal D
        (I.map (FieldTensorModelEquivalence.coefficientMap (A := .of C) (D := .of D) e).toRingHom)
        (valuativeFieldTargetIdeal_ne_bot (.of C) (.of D) e I hI) q := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  let f := affineStructuralMap k (.of C)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let : SmoothOfRelativeDimension n (S.composite ≫ affineStructuralMap k (.of C)) :=
    affinePrincipalization_smoothOfRelativeDimension f n I hI
  let : SmoothOfRelativeDimension n (S.composite ≫
      Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    (inferInstance : SmoothOfRelativeDimension n (S.composite ≫ affineStructuralMap k (.of C)))
  let : IsIso (S.composite ∣_ (specIdealSheaf I).support.compl) :=
    affinePrincipalization_isIso_restrict f n I hI
  let J := (specIdealSheaf I).comap S.composite
  let hJ : J.IsIdealOfSncDivisor := affinePrincipalization_isIdealOfSncDivisor f n I hI
  obtain ⟨T, j, hopen, htriangle, hcover, v, hv⟩ :=
    exists_resolvedSequence_etale_cover C n I hI z hz S hJ
  let : ∀ i, IsOpenImmersion (j i) := hopen
  let B (i : T.LeafIndex) : CommRingCat.{u} := .of (T.leafAlgebra i)
  let φ (i : T.LeafIndex) : C →ₐ[k] B i :=
    Subalgebra.inclusion (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))
  have hOld := RoundedCanonicalModule.specPushedQuotientKernel_eq_valuativeMultiplierIdeal_of_sequence
    C n I hI z hz S hJ q
  let a := FieldTensorModelEquivalence.coefficientMap (A := .of C) (D := .of D) e
  let ID := I.map a.toRingHom
  have hID : ID ≠ ⊥ := valuativeFieldTargetIdeal_ne_bot (.of C) (.of D) e I hI
  let p := Spec.map (CommRingCat.ofHom a.toRingHom)
  have hpField := FieldTensorModelEquivalence.isPullback_coefficients (A := .of C) (D := .of D) e
  let : Flat p := property_of_isPullback @Flat hpField
    (flat_and_surjective_specMap (algebraMap k L)).1
  let SD := S.pullback p
  have hsquare := isPullback_pullbackLastHom S p
  have hwholeField := hsquare.paste_vert hpField
  let : SmoothOfRelativeDimension n (SD.composite ≫ affineStructuralMap L (.of D)) :=
    smoothOfRelativeDimension_of_isPullback_specMap hwholeField n
  let : SmoothOfRelativeDimension n (SD.composite ≫
      Spec.map (CommRingCat.ofHom (algebraMap L D))) :=
    (inferInstance : SmoothOfRelativeDimension n (SD.composite ≫ affineStructuralMap L (.of D)))
  let hSmoothLiteral : Smooth (S.composite ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (CommRingCat.of C)))) :=
    @SmoothOfRelativeDimension.smooth n _ _ _
      (inferInstance : SmoothOfRelativeDimension n
        (S.composite ≫ affineStructuralMap k (.of C)))
  have hPulledSNC : (J.comap (S.pullbackLastHom p)).IsIdealOfSncDivisor :=
    @RoundedSncIdealSheaf.isIdealOfSncDivisor_comap_of_isPullback_specMap
      k L inferInstance inferInstance inferInstance S.last SD.last (algebraMap k L)
      (S.pullbackLastHom p)
      (S.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap k (CommRingCat.of C))))
      (SD.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap L (CommRingCat.of D))))
      hwholeField hSmoothLiteral J hJ
  have hIDSheaf : specIdealSheaf ID = (specIdealSheaf I).comap p :=
    (comap_specIdealSheaf_Spec_map a.toRingHom I).symm
  have hJD : (specIdealSheaf ID).comap SD.composite = J.comap (S.pullbackLastHom p) := by
    rw [hIDSheaf, ← Scheme.IdealSheafData.comap_comp]
    change _ = ((specIdealSheaf I).comap S.composite).comap (S.pullbackLastHom p)
    rw [← Scheme.IdealSheafData.comap_comp]
    exact congrArg (fun t => (specIdealSheaf I).comap t) hsquare.w.symm
  have hJDsnc : ((specIdealSheaf ID).comap SD.composite).IsIdealOfSncDivisor :=
    hJD.symm ▸ hPulledSNC
  have hsupport : (specIdealSheaf ID).support.compl = p ⁻¹ᵁ (specIdealSheaf I).support.compl := by
    rw [hIDSheaf, Scheme.IdealSheafData.support_comap]
    rfl
  let : IsIso (SD.composite ∣_ (specIdealSheaf ID).support.compl) := by
    rw [hsupport]
    exact isIso_pullback_composite_restrict S p (specIdealSheaf I).support.compl
  let zD : Fin n → D := fun i => e (fieldTensorCoordinates (k := k) (L := L) z i)
  let hzD := etale_coordinates_sourceAlgEquiv e _ (etale_fieldTensorCoordinates z hz)
  have hNew := RoundedCanonicalModule.specPushedQuotientKernel_eq_valuativeMultiplierIdeal_of_sequence
    D n ID hID zD hzD SD hJDsnc q
  obtain ⟨TD, jD, hopenD, htriangleD, hcoverD, vD, hvD⟩ :=
    exists_resolvedSequence_etale_cover D n ID hID zD hzD SD hJDsnc
  let : ∀ i, IsOpenImmersion (jD i) := hopenD
  let BD (i : TD.LeafIndex) : CommRingCat.{u} := .of (TD.leafAlgebra i)
  let φD (i : TD.LeafIndex) : D →ₐ[L] BD i :=
    Subalgebra.inclusion (TD.root_le_of_mem_leaves (TD.leafAlgebra_mem_leaves i))
  let E := hsquare.isoPullback
  let : Smooth (SD.composite ≫ affineStructuralMap L (.of D)) :=
    SmoothOfRelativeDimension.smooth n _
  have hIso := RoundedCanonicalModule.specPushedQuotientKernel_modelIso (.of D) SD.composite E
    zD hzD ((specIdealSheaf ID).comap SD.composite) hJDsnc q
    BD φD jD htriangleD hcoverD
  have hgInv : E.inv ≫ SD.composite = pullback.snd S.composite p :=
    hsquare.isoPullback_inv_snd
  have hJInv : ((specIdealSheaf ID).comap SD.composite).comap E.inv =
      J.comap (pullback.fst S.composite p) := by
    rw [hJD, ← Scheme.IdealSheafData.comap_comp]
    exact congrArg (fun t => J.comap t) hsquare.isoPullback_inv_fst
  let hJTarget : (J.comap (pullback.fst S.composite p)).IsIdealOfSncDivisor :=
    FieldEquivalentGlobalKernel.model_snc (k := k) (L := L) (.of C) (.of D) e S.composite n J hJ
  have hIso' := hIso.trans (pushedKernel_congr (k := L) (.of D) hgInv zD hzD hJInv _ hJTarget q)
  have hField := RoundedCanonicalModule.specPushedQuotientKernel_fieldTensorEquiv (k := k) (L := L)
    (.of C) (.of D) e S.composite z hz J hJ q B φ j htriangle hcover v hv
  rw [hOld] at hField
  exact hField.trans (hIso'.symm.trans hNew)

end EnvelopeProperty.Char0
