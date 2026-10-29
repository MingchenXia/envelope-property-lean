import EnvelopeProperty.Char0.ValuativeFieldTensor
import EnvelopeProperty.Char0.PushedKernelSourceLocalization

/-! # Full original multiplier ideals on genuine integral opens of a possibly split field tensor -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EnvelopeProperty.CanonicalGeometry
open scoped TensorProduct
namespace EnvelopeProperty.Char0
attribute [local instance] Algebra.TensorProduct.rightAlgebra
universe u

/-- The SAME original coefficient map through the actual field tensor and actual open. -/
def tensorOpenCoefficientMap
    {k L C D : Type u} [Field k] [Field L] [CommRing C] [CommRing D]
    [Algebra k L] [Algebra k C] [Algebra L D]
    (φ : (L ⊗[k] C) →ₐ[L] D) : C →+* D :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := k) (A := L)).toRingHom

/-- Original coefficients are injective on an actual nonempty open of the field tensor. -/
theorem tensorOpenCoefficientMap_injective
    {k L C D : Type u} [Field k] [Field L] [CommRing C] [IsDomain C]
    [CommRing D] [Nontrivial D] [Algebra k L] [Algebra k C] [Algebra L D]
    (φ : (L ⊗[k] C) →ₐ[L] D)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))] :
    Function.Injective (tensorOpenCoefficientMap φ) := by
  let B := L ⊗[k] C
  let : Algebra C B := Algebra.TensorProduct.rightAlgebra
  let : Module.Flat C B := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight k C L).symm.toLinearEquiv
  have hfield : (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := C)).toRingHom.Flat :=
    RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat C B)
  have hopen : φ.toRingHom.Flat :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom φ.toRingHom)).mp inferInstance
  let : Algebra C D := (tensorOpenCoefficientMap φ).toAlgebra
  let : Module.Flat C D := hfield.comp hopen
  change Function.Injective (algebraMap C D)
  exact FaithfulSMul.algebraMap_injective C D

private theorem tensorOpen_pushedKernel_congr
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

private theorem valuativeMultiplierIdeal_tensorOpen_of_sequence
    {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra L M] [CharZero k] [CharZero L]
    (C : Subalgebra k K) [IsFractionRing C K]
    (D : Subalgebra L M) [IsFractionRing D M]
    (φ : (L ⊗[k] C) →ₐ[L] D)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    {n : ℕ} (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ)
    (S : Scheme.BlowUpSequence (Spec (.of C)))
    [SmoothOfRelativeDimension n (S.composite ≫ affineStructuralMap k (.of C))]
    [IsIso (S.composite ∣_ (specIdealSheaf I).support.compl)]
    (hJ : ((specIdealSheaf I).comap S.composite).IsIdealOfSncDivisor) :
    (valuativeMultiplierIdeal C I hI q).map (tensorOpenCoefficientMap φ) =
      valuativeMultiplierIdeal D (I.map (tensorOpenCoefficientMap φ))
        ((Ideal.map_eq_bot_iff_of_injective (tensorOpenCoefficientMap_injective φ)).mp.mt hI) q := by
  let B : CommRingCat.{u} := .of (L ⊗[k] C)
  let : Algebra B D := φ.toAlgebra
  let : IsScalarTower L B D := IsScalarTower.of_algebraMap_eq (R := L) (S := B) (A := D)
    fun a => (φ.commutes a).symm
  let p₀ := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := C)).toRingHom)
  let p₁ := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let : Flat p₀ := property_of_isPullback @Flat
    (isPullback_fieldTensor (k := k) (L := L) (A := C))
    (flat_and_surjective_specMap (algebraMap k L)).1
  let : Flat p₁ := inferInstance
  let : Module.Flat B D := RingHom.flat_algebraMap_iff.mp
    ((HasRingHomProperty.Spec_iff (P := @Flat)
      (φ := CommRingCat.ofHom (algebraMap B D))).mp (inferInstance : Flat p₁))
  let J := (specIdealSheaf I).comap S.composite
  let YB := FlatGlobalSections.baseChange (S := L ⊗[k] C) S.composite
  let gB : YB ⟶ Spec B := FlatGlobalSections.structureMap (S := L ⊗[k] C) S.composite
  let uB : YB ⟶ S.last := FlatGlobalSections.firstProjection (S := L ⊗[k] C) S.composite
  let JB := J.comap uB
  let hJB : JB.IsIdealOfSncDivisor := FieldTensorGlobalKernel.model_snc (L := L) (.of C)
    S.composite n J hJ
  let zB := fieldTensorCoordinates (k := k) (L := L) z
  let hzB := etale_fieldTensorCoordinates (k := k) (L := L) z hz
  let : SmoothOfRelativeDimension n (gB ≫ affineStructuralMap L B) :=
    FieldTensorGlobalKernel.model_smoothOfRelativeDimension (L := L) (.of C) S.composite n
  let : Smooth (gB ≫ affineStructuralMap L B) := SmoothOfRelativeDimension.smooth n _
  let fC := affineStructuralMap k (.of C)
  let : SmoothOfRelativeDimension n fC := smoothOfRelativeDimension_of_etale_coordinates z hz
  let : Smooth fC := SmoothOfRelativeDimension.smooth n _
  let : IsLocallyNoetherian (Spec (.of C)) := LocallyOfFiniteType.isLocallyNoetherian fC
  let : IsProper S.composite := S.isProper_composite
  let : IsProper gB := inferInstance
  let : CompactSpace YB := QuasiCompact.compactSpace_of_compactSpace gB
  let : YB.IsSeparated := ⟨by rw [← terminal.comp_from gB]; infer_instance⟩
  obtain ⟨T₀, j₀, hopen₀, htriangle₀, hcover₀, v₀, hv₀⟩ :=
    exists_resolvedSequence_etale_cover C n I hI z hz S hJ
  let : ∀ i, IsOpenImmersion (j₀ i) := hopen₀
  let B₀ (i : T₀.LeafIndex) : CommRingCat.{u} := .of (T₀.leafAlgebra i)
  let φ₀ (i : T₀.LeafIndex) : C →ₐ[k] B₀ i :=
    Subalgebra.inclusion (T₀.root_le_of_mem_leaves (T₀.leafAlgebra_mem_leaves i))
  let : SmoothOfRelativeDimension n
      (S.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    (inferInstance : SmoothOfRelativeDimension n (S.composite ≫ affineStructuralMap k (.of C)))
  have hOld := RoundedCanonicalModule.specPushedQuotientKernel_eq_valuativeMultiplierIdeal_of_sequence
    C n I hI z hz S hJ q
  have hField := RoundedCanonicalModule.specPushedQuotientKernel_fieldTensor (k := k) (L := L)
    (.of C) S.composite z hz J hJ q B₀ φ₀ j₀ htriangle₀ hcover₀ v₀ hv₀
  have hOpen := RoundedCanonicalModule.specPushedQuotientKernel_openBase (k := L)
    B (.of D) gB zB hzB JB hJB q
  let SL := S.pullback p₀
  let T := SL.pullback p₁
  have sq₀ := isPullback_pullbackLastHom S p₀
  have sq₁ := isPullback_pullbackLastHom SL p₁
  let E₀ := sq₀.isoPullback
  let u : T.last ⟶ YB := SL.pullbackLastHom p₁ ≫ E₀.hom
  have eSquare : IsPullback E₀.hom SL.composite gB (𝟙 (Spec B)) := by
    apply IsPullback.of_horiz_isIso
    constructor
    rw [Category.comp_id]
    change E₀.hom ≫ pullback.snd S.composite p₀ = SL.composite
    exact sq₀.isoPullback_hom_snd
  have hCan : IsPullback u T.composite gB p₁ := by
    have h := sq₁.paste_horiz eSquare
    rw [Category.comp_id] at h
    exact h
  have hBtriangle : uB ≫ S.composite = gB ≫ p₀ := by
    change pullback.fst S.composite p₀ ≫ S.composite = pullback.snd S.composite p₀ ≫ p₀
    exact pullback.condition
  let : IsOpenImmersion u := property_of_isPullback @IsOpenImmersion hCan inferInstance
  have hstruct : p₁ ≫ affineStructuralMap L B = affineStructuralMap L (.of D) :=
    SourceOpenPushedKernel.structuralMap B (.of D)
  let : SmoothOfRelativeDimension n (T.composite ≫ affineStructuralMap L (.of D)) := by
    rw [← hstruct, ← Category.assoc, ← hCan.w, Category.assoc]
    exact (Nat.zero_add n) ▸
      (smoothOfRelativeDimension_comp (f := u) (n := 0) (m := n)
        (gB ≫ affineStructuralMap L B))
  let : SmoothOfRelativeDimension n (T.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap L D))) :=
    (inferInstance : SmoothOfRelativeDimension n (T.composite ≫ affineStructuralMap L (.of D)))
  let a := tensorOpenCoefficientMap φ
  let ID := I.map a
  have hID : ID ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (tensorOpenCoefficientMap_injective φ)).mp.mt hI
  have hCoeff : p₁ ≫ p₀ = Spec.map (CommRingCat.ofHom a) := by
    rw [← Spec.map_comp]
    rfl
  have hIDSheaf : specIdealSheaf ID = (specIdealSheaf I).comap (p₁ ≫ p₀) := by
    rw [hCoeff]
    exact (comap_specIdealSheaf_Spec_map a I).symm
  have hJT : (specIdealSheaf ID).comap T.composite = JB.comap u := by
    rw [hIDSheaf, ← Scheme.IdealSheafData.comap_comp]
    change (specIdealSheaf I).comap (T.composite ≫ (p₁ ≫ p₀)) =
      (((specIdealSheaf I).comap S.composite).comap uB).comap u
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    apply congrArg (fun t => (specIdealSheaf I).comap t)
    calc
      T.composite ≫ (p₁ ≫ p₀) = (T.composite ≫ p₁) ≫ p₀ := by rw [Category.assoc]
      _ = (u ≫ gB) ≫ p₀ := by rw [hCan.w]
      _ = u ≫ (gB ≫ p₀) := by rw [Category.assoc]
      _ = u ≫ (uB ≫ S.composite) := by rw [hBtriangle]
  have hJTs : ((specIdealSheaf ID).comap T.composite).IsIdealOfSncDivisor :=
    hJT.symm ▸ hJB.comap_of_smooth (gB ≫ affineStructuralMap L B) u
  have hsupport : (specIdealSheaf ID).support.compl =
      (p₁ ≫ p₀) ⁻¹ᵁ (specIdealSheaf I).support.compl := by
    rw [hIDSheaf, Scheme.IdealSheafData.support_comap]
    rfl
  let : IsIso (T.composite ∣_ (specIdealSheaf ID).support.compl) := by
    rw [hsupport]
    exact isIso_restrict_of_isPullback (sq₁.paste_horiz sq₀) (specIdealSheaf I).support.compl
  let zD := fun i => φ (zB i)
  let hzD := SourceOpenPushedKernel.etale_coordinates B (.of D) zB hzB
  have hNew := RoundedCanonicalModule.specPushedQuotientKernel_eq_valuativeMultiplierIdeal_of_sequence
    D n ID hID zD hzD T hJTs q
  obtain ⟨TD, jD, hopenD, htriangleD, hcoverD, vD, hvD⟩ :=
    exists_resolvedSequence_etale_cover D n ID hID zD hzD T hJTs
  let : ∀ i, IsOpenImmersion (jD i) := hopenD
  let BD (i : TD.LeafIndex) : CommRingCat.{u} := .of (TD.leafAlgebra i)
  let φD (i : TD.LeafIndex) : D →ₐ[L] BD i :=
    Subalgebra.inclusion (TD.root_le_of_mem_leaves (TD.leafAlgebra_mem_leaves i))
  let E := hCan.isoPullback
  let : Smooth (T.composite ≫ affineStructuralMap L (.of D)) := SmoothOfRelativeDimension.smooth n _
  have hIso := RoundedCanonicalModule.specPushedQuotientKernel_modelIso (.of D) T.composite E
    zD hzD ((specIdealSheaf ID).comap T.composite) hJTs q
    BD φD jD htriangleD hcoverD
  have hgInv : E.inv ≫ T.composite = pullback.snd gB p₁ := hCan.isoPullback_inv_snd
  have hJInv : ((specIdealSheaf ID).comap T.composite).comap E.inv =
      JB.comap (pullback.fst gB p₁) := by
    rw [hJT, ← Scheme.IdealSheafData.comap_comp, hCan.isoPullback_inv_fst]
  let hJTarget : (JB.comap (pullback.fst gB p₁)).IsIdealOfSncDivisor :=
    SourceOpenPushedKernel.model_snc (k := L) B (.of D) gB n JB hJB
  have hIso' := hIso.trans
    (tensorOpen_pushedKernel_congr (.of D) hgInv zD hzD hJInv _ hJTarget q)
  have hTotal := congrArg (fun K : Ideal B => K.map φ.toRingHom) hField
  rw [hOld, Ideal.map_map] at hTotal
  exact hTotal.trans (hOpen.trans (hIso'.symm.trans hNew))

/-- Entire original all-divisorial multiplier ideals commute with actual integral
open parts of a field tensor. The tensor itself need not be integral. -/
theorem valuativeMultiplierIdeal_tensorOpen
    {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra L M] [CharZero k] [CharZero L]
    (C : Subalgebra k K) [IsFractionRing C K]
    (D : Subalgebra L M) [IsFractionRing D M]
    (φ : (L ⊗[k] C) →ₐ[L] D)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    {n : ℕ} (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale)
    (I : Ideal C) (hI : I ≠ ⊥) (q : ℚ) :
    (valuativeMultiplierIdeal C I hI q).map (tensorOpenCoefficientMap φ) =
      valuativeMultiplierIdeal D (I.map (tensorOpenCoefficientMap φ))
        ((Ideal.map_eq_bot_iff_of_injective (tensorOpenCoefficientMap_injective φ)).mp.mt hI) q := by
  let f := affineStructuralMap k (.of C)
  let : SmoothOfRelativeDimension n f := smoothOfRelativeDimension_of_etale_coordinates z hz
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let : SmoothOfRelativeDimension n (S.composite ≫ f) :=
    affinePrincipalization_smoothOfRelativeDimension f n I hI
  let : IsIso (S.composite ∣_ (specIdealSheaf I).support.compl) :=
    affinePrincipalization_isIso_restrict f n I hI
  exact valuativeMultiplierIdeal_tensorOpen_of_sequence C D φ z hz I hI q S
    (affinePrincipalization_isIdealOfSncDivisor f n I hI)

end EnvelopeProperty.Char0
