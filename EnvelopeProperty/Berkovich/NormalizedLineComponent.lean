/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.AffineLineComponents
import EnvelopeProperty.Berkovich.SchemeCurveNormalization
import EnvelopeProperty.Berkovich.SpectrumIntegralRational
import EnvelopeProperty.Berkovich.SchemeIntegralMaps

/-!
# Actual normalization of a minimal component of the original line preimage

The original transverse equations determine a genuine minimal-prime quotient.
Its actual integral closure in its fraction field is finite; the constructed
open-line coefficient map is finite, free and flat. All original ring elements,
scheme triangles, geometric ideals and prescribed field valuations are kept.
No smoothness, proper-model existence or analytic potential comparison is claimed.
-/

open scoped NNReal Polynomial
open CategoryTheory AlgebraicGeometry Topology
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.AffineLine
open Berkovich
variable {F σ B : Type u} [Field F] [CommRing B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B) (P : Ideal B)
variable (hP : P ∈ ((lineIdeal a b j).map
  (φ.toRingHom.comp (algebraMap _ (Localization.Away g)))).minimalPrimes)

include hP in
/-- The actual minimal component is a domain, rather than an assumed component witness. -/
theorem componentQuotient_isDomain : IsDomain (B ⧸ P) := by
  let : P.IsPrime := hP.isPrime
  infer_instance

/-- Finiteness of the original ambient map gives finite type of the actual component over its original field. -/
theorem componentQuotient_finiteType [Fintype σ] (hφ : φ.toRingHom.Finite) :
    Algebra.FiniteType F (B ⧸ P) := by
  let R := Localization.Away g
  let : Algebra R B := φ.toRingHom.toAlgebra
  let : IsScalarTower F R B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let : Module.Finite R B := hφ
  let : Algebra.FinitePresentation (MvPolynomial σ F) R := IsLocalization.Away.finitePresentation g
  let : Algebra.FiniteType F R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F (MvPolynomial σ F))
    (inferInstance : Algebra.FiniteType (MvPolynomial σ F) R)
  let : Algebra.FiniteType F B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F R) (inferInstance : Algebra.FiniteType R B)
  infer_instance

/-- The whole genuine component-line map followed by its literal normalization inclusion. -/
def normalizedComponentLineHom : OpenLineRing (subst a b g) →ₐ[F]
    CurveNormalization.Ring (B ⧸ P) :=
  (IsScalarTower.toAlgHom F (B ⧸ P) (CurveNormalization.Ring (B ⧸ P))).comp
    (componentLineHom a b j g hb φ P hP)

/-- Every original localized ambient element is retained by the complete normalized-component diagram. -/
theorem normalizedComponentLineHom_principalLineHom (r : Localization.Away g) :
    normalizedComponentLineHom a b j g hb φ P hP (principalLineHom a b g r) =
      CurveNormalization.inclusion (B ⧸ P) (Ideal.Quotient.mk P (φ r)) := by
  change algebraMap (B ⧸ P) (CurveNormalization.Ring (B ⧸ P))
    (componentLineHom a b j g hb φ P hP (principalLineHom a b g r)) = _
  rw [componentLineHom_principalLineHom]
  rfl

include hP in
/-- Perfect-field finite normalization makes the literal component normalization inclusion finite. -/
theorem componentNormalization_inclusion_finite [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) : (CurveNormalization.inclusion (B ⧸ P)).Finite := by
  let : IsDomain (B ⧸ P) := componentQuotient_isDomain a b j g φ P hP
  let : Algebra.FiniteType F (B ⧸ P) := componentQuotient_finiteType g φ P hφ
  exact CurveNormalization.finite_inclusion F (B ⧸ P)

/-- The actual normalized line coefficient homomorphism is finite, with no separability hypothesis. -/
theorem normalizedComponentLineHom_finite [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) : (normalizedComponentLineHom a b j g hb φ P hP).toRingHom.Finite :=
  (componentNormalization_inclusion_finite a b j g φ P hP hφ).comp
    (componentLineHom_finite a b j g hb φ P hP hφ)

/-- The actual positive-dimensional component map stays injective after literal normalization. -/
theorem normalizedComponentLineHom_injective [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Function.Injective (normalizedComponentLineHom a b j g hb φ P hP) := by
  let : IsDomain (B ⧸ P) := componentQuotient_isDomain a b j g φ P hP
  exact (CurveNormalization.inclusion_injective (B ⧸ P)).comp
    (componentLineHom_injective a b j g hb φ P hP hg hline hφ hiφ)

include hb hP in
/-- True normality and integral dimension descent give the actual normalized component a Dedekind structure. -/
theorem componentNormalization_isDedekindDomain [Fintype σ] [PerfectField F]
    (hline : subst a b g ≠ 0) (hφ : φ.toRingHom.Finite) :
    IsDedekindDomain (CurveNormalization.Ring (B ⧸ P)) := by
  let A := OpenLineRing (subst a b g)
  let D := B ⧸ P
  let : IsDomain D := componentQuotient_isDomain a b j g φ P hP
  let : Algebra.FiniteType F D := componentQuotient_finiteType g φ P hφ
  let : IsDedekindDomain A := openLineRing_isDedekindDomain _ hline
  let : Algebra A D := (componentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
  let : Module.Finite A D := componentLineHom_finite a b j g hb φ P hP hφ
  exact CurveNormalization.isDedekindDomain_ring F A D

/-- Every actual open-line ring remains a principal ideal ring, including the empty-open ring. -/
theorem openLineRing_isPrincipalIdealRing (p : F[X]) : IsPrincipalIdealRing (OpenLineRing p) := by
  constructor
  intro I
  rw [← IsLocalization.map_under (Submonoid.powers p) (OpenLineRing p) I]
  infer_instance

/-- The original open line is a principal domain, and the actual injective component action makes its finite normalization module free. -/
theorem normalizedComponentLineHom_free [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    letI := (normalizedComponentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
    Module.Free (OpenLineRing (subst a b g)) (CurveNormalization.Ring (B ⧸ P)) := by
  let A := OpenLineRing (subst a b g)
  let D := B ⧸ P
  let : IsDomain A := openLineRing_isDomain _ hline
  let : IsPrincipalIdealRing A := openLineRing_isPrincipalIdealRing _
  let : IsDomain D := componentQuotient_isDomain a b j g φ P hP
  let : Algebra.FiniteType F D := componentQuotient_finiteType g φ P hφ
  let : Algebra A D := (componentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
  let : Module.Finite A D := componentLineHom_finite a b j g hb φ P hP hφ
  exact CurveNormalization.free_coefficientMap F A D
    (componentLineHom_injective a b j g hb φ P hP hg hline hφ hiφ)

/-- Flatness is derived from the real finite free normalization module for the exact line homomorphism. -/
theorem normalizedComponentLineHom_flat [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    (normalizedComponentLineHom a b j g hb φ P hP).toRingHom.Flat := by
  let := (normalizedComponentLineHom a b j g hb φ P hP).toRingHom.toAlgebra
  let : Module.Free (OpenLineRing (subst a b g)) (CurveNormalization.Ring (B ⧸ P)) :=
    normalizedComponentLineHom_free a b j g hb φ P hP hg hline hφ hiφ
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_free (R := OpenLineRing (subst a b g)) (M := CurveNormalization.Ring (B ⧸ P)))

/-- The literal normalized component scheme maps to the original open line. -/
def normalizedComponentLineSchemeMap : CurveNormalization.scheme (B ⧸ P) ⟶
    openLineScheme (subst a b g) :=
  Spec.map (CommRingCat.ofHom (normalizedComponentLineHom a b j g hb φ P hP).toRingHom)

/-- The entire normalization projection and original component-line scheme map commute. -/
theorem normalizedComponentLineSchemeMap_factor :
    normalizedComponentLineSchemeMap a b j g hb φ P hP =
      CurveNormalization.projection (B ⧸ P) ≫ componentLineSchemeMap a b j g hb φ P hP := by
  rw [normalizedComponentLineSchemeMap, CurveNormalization.projection,
    componentLineSchemeMap, ← Spec.map_comp]
  rfl

/-- The complete original ambient square, retaining every original B element and the actual component quotient. -/
theorem normalizedComponentLineSchemeMap_square :
    normalizedComponentLineSchemeMap a b j g hb φ P hP ≫ principalLineSchemeMap a b g =
      CurveNormalization.projection (B ⧸ P) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫
          Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [normalizedComponentLineSchemeMap_factor, Category.assoc, componentLineSchemeMap_square]

/-- The whole original field coefficient structure is preserved by the normalized line map. -/
theorem normalizedComponentLineSchemeMap_over_field :
    normalizedComponentLineSchemeMap a b j g hb φ P hP ≫ openLineStructure (subst a b g) =
      Spec.map (CommRingCat.ofHom (algebraMap F (CurveNormalization.Ring (B ⧸ P)))) :=
  RelativeSchemeValuedPoint.affineStructureMap_commutes
    (normalizedComponentLineHom a b j g hb φ P hP)

/-- The actual normalized component scheme morphism is finite. -/
theorem normalizedComponentLineSchemeMap_isFinite [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) : IsFinite (normalizedComponentLineSchemeMap a b j g hb φ P hP) :=
  (IsFinite.SpecMap_iff _).mpr (normalizedComponentLineHom_finite a b j g hb φ P hP hφ)

/-- Actual module freeness gives flatness of the literal normalized open-line scheme map. -/
theorem normalizedComponentLineSchemeMap_flat [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    AlgebraicGeometry.Flat (normalizedComponentLineSchemeMap a b j g hb φ P hP) :=
  Flat.SpecMap_iff.mpr (normalizedComponentLineHom_flat a b j g hb φ P hP hg hline hφ hiφ)

/-- Every genuine scheme point of the original open line lifts to the actual normalized component. -/
theorem normalizedComponentLineSchemeMap_surjective [Fintype σ] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) :
    Function.Surjective (normalizedComponentLineSchemeMap a b j g hb φ P hP) := by
  let : IsDomain (B ⧸ P) := componentQuotient_isDomain a b j g φ P hP
  rw [normalizedComponentLineSchemeMap_factor]
  exact (componentLineSchemeMap_surjective a b j g hb φ P hP hg hline hφ hiφ).1.comp
    (CurveNormalization.projection_surjective (B := B ⧸ P))

/-- The actual normalized line map on native points preserves the whole prescribed field valuation, possibly unbounded. -/
def normalizedComponentLineNativeMap (v : Valuation F ℝ≥0) :
    RelativeSchemeValuedPoint v
      (Spec.map (CommRingCat.ofHom (algebraMap F (CurveNormalization.Ring (B ⧸ P))))) →
      RelativeSchemeValuedPoint v (openLineStructure (subst a b g)) :=
  RelativeSchemeValuedPoint.map (normalizedComponentLineSchemeMap a b j g hb φ P hP)
    (normalizedComponentLineSchemeMap_over_field a b j g hb φ P hP)

/-- The entire native normalized component map is continuous for any prescribed field seminorm. -/
@[fun_prop]
theorem continuous_normalizedComponentLineNativeMap (v : Valuation F ℝ≥0) :
    Continuous (normalizedComponentLineNativeMap a b j g hb φ P hP v) :=
  RelativeSchemeValuedPoint.continuous_map _ _

/-- Actual finite normalization makes the native normalized line map proper for every field valuation. -/
theorem isProperMap_normalizedComponentLineNativeMap [Fintype σ] [PerfectField F]
    (hφ : φ.toRingHom.Finite) (v : Valuation F ℝ≥0) :
    IsProperMap (normalizedComponentLineNativeMap a b j g hb φ P hP v) := by
  let := normalizedComponentLineSchemeMap_isFinite a b j g hb φ P hP hφ
  exact RelativeSchemeValuedPoint.isProperMap_map_of_isIntegralHom _ _

/-- Every whole native open-line point lifts to the actual normalized component while retaining all prescribed field values. -/
theorem normalizedComponentLineNativeMap_surjective [Fintype σ] [PerfectField F] [IsDomain B]
    (hg : g ≠ 0) (hline : subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ) (v : Valuation F ℝ≥0) :
    Function.Surjective (normalizedComponentLineNativeMap a b j g hb φ P hP v) := by
  let := normalizedComponentLineSchemeMap_isFinite a b j g hb φ P hP hφ
  exact RelativeSchemeValuedPoint.map_surjective_of_isIntegralHom _ _
    (normalizedComponentLineSchemeMap_surjective a b j g hb φ P hP hg hline hφ hiφ)

/-- The actual whole inclusion of the normalized component into the original ambient curve scheme. -/
def normalizedComponentInclusionSchemeMap : CurveNormalization.scheme (B ⧸ P) ⟶
    Spec (CommRingCat.of B) :=
  CurveNormalization.projection (B ⧸ P) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))

/-- The actual normalized component inclusion retains the original full quotient and normalization ring map. -/
theorem normalizedComponentInclusionSchemeMap_eq_specMap :
    normalizedComponentInclusionSchemeMap (B := B) P = Spec.map (CommRingCat.ofHom
      ((CurveNormalization.inclusion (B ⧸ P)).comp (Ideal.Quotient.mk P))) := by
  rw [normalizedComponentInclusionSchemeMap, CurveNormalization.projection, ← Spec.map_comp]
  rfl

/-- The original ambient ideal pulls back to its entire component and normalization image, without radical replacement. -/
theorem normalizedComponentInclusion_idealSheaf_comap (J : Ideal B) :
    (CurveNormalization.idealSheaf B J).comap (normalizedComponentInclusionSchemeMap P) =
      CurveNormalization.idealSheaf (CurveNormalization.Ring (B ⧸ P))
        ((J.map (Ideal.Quotient.mk P)).map (CurveNormalization.inclusion (B ⧸ P))) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.comap_ideal_top_of_isAffine_native]
  simp only [CurveNormalization.idealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  rw [normalizedComponentInclusionSchemeMap_eq_specMap]
  congr 1
  change ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
    (Spec.map (CommRingCat.ofHom ((CurveNormalization.inclusion (B ⧸ P)).comp
      (Ideal.Quotient.mk P)))).appTop).hom =
    ((CommRingCat.ofHom ((CurveNormalization.inclusion (B ⧸ P)).comp (Ideal.Quotient.mk P))) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (CurveNormalization.Ring (B ⧸ P)))).inv).hom
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality _).symm

/-- At every actual normalized component point the original ideal stalk image is the true entire stalk-map image. -/
theorem normalizedComponentInclusion_stalkIdeal_comap
    (I : (Spec (CommRingCat.of B)).IdealSheafData) (x : CurveNormalization.scheme (B ⧸ P)) :
    (I.comap (normalizedComponentInclusionSchemeMap P)).stalkIdeal x =
      (I.stalkIdeal (normalizedComponentInclusionSchemeMap P x)).map
        ((normalizedComponentInclusionSchemeMap P).stalkMap x).hom :=
  I.paperStalkIdeal_comap _ _

/-- The actual normalization map above the original component is a whole prescribed-field native map. -/
def componentNormalizationNativeMap (v : Valuation F ℝ≥0) :
    RelativeSchemeValuedPoint v
      (Spec.map (CommRingCat.ofHom (algebraMap F (CurveNormalization.Ring (B ⧸ P))))) →
      RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap F (B ⧸ P)))) :=
  RelativeSchemeValuedPoint.map (CurveNormalization.projection (B ⧸ P))
    (RelativeSchemeValuedPoint.affineStructureMap_commutes
      (IsScalarTower.toAlgHom F (B ⧸ P) (CurveNormalization.Ring (B ⧸ P))))

include hP in
/-- Original component native points admit actual normalized-component lifts preserving their entire prescribed field seminorm. -/
theorem componentNormalizationNativeMap_surjective (v : Valuation F ℝ≥0) :
    Function.Surjective (componentNormalizationNativeMap (B := B) P v) := by
  let : IsDomain (B ⧸ P) := componentQuotient_isDomain a b j g φ P hP
  let : IsIntegralHom (CurveNormalization.projection (B ⧸ P)) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  exact RelativeSchemeValuedPoint.map_surjective_of_isIntegralHom _ _
    (CurveNormalization.projection_surjective (B := B ⧸ P))

/-- Actual integral normalization induces a proper whole native component map for arbitrary, possibly unbounded, field seminorms. -/
theorem isProperMap_componentNormalizationNativeMap (v : Valuation F ℝ≥0) :
    IsProperMap (componentNormalizationNativeMap (B := B) P v) := by
  let : IsIntegralHom (CurveNormalization.projection (B ⧸ P)) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  exact RelativeSchemeValuedPoint.isProperMap_map_of_isIntegralHom _ _

include hP in
/-- Every rational original component point has an actual whole evaluator on its normalization over an algebraically closed field. -/
theorem exists_componentNormalization_rationalEval [IsAlgClosed F]
    (e : B →ₐ[F] F) (he : P ≤ RingHom.ker e.toRingHom) :
    ∃ d : CurveNormalization.Ring (B ⧸ P) →ₐ[F] F,
      ∀ r : B, d (CurveNormalization.inclusion (B ⧸ P) (Ideal.Quotient.mk P r)) = e r := by
  let : IsDomain (B ⧸ P) := componentQuotient_isDomain a b j g φ P hP
  let eP : B ⧸ P →ₐ[F] F := Ideal.Quotient.liftₐ P e (fun r hr => RingHom.mem_ker.mp (he hr))
  obtain ⟨d, hd⟩ := Spectrum.exists_rationalEval_of_injective_isIntegral
    (B := CurveNormalization.Ring (B ⧸ P)) eP (CurveNormalization.inclusion_injective (B ⧸ P))
  refine ⟨d, fun r => ?_⟩
  exact congrArg (fun q : B ⧸ P →ₐ[F] F => q (Ideal.Quotient.mk P r)) hd

include hP in
/-- A given rational original point lifts to an actual normalized native point, retaining the entire original point and every original element, for any prescribed field valuation. -/
theorem exists_componentNormalization_rationalNativeLift [IsAlgClosed F]
    (v : Valuation F ℝ≥0) (e : B →ₐ[F] F) (he : P ≤ RingHom.ker e.toRingHom) :
    ∃ d : CurveNormalization.Ring (B ⧸ P) →ₐ[F] F,
      ∃ y : RelativeSchemeValuedPoint v
        (Spec.map (CommRingCat.ofHom (algebraMap F (CurveNormalization.Ring (B ⧸ P))))),
        (∀ r : B, d (CurveNormalization.inclusion (B ⧸ P) (Ideal.Quotient.mk P r)) = e r) ∧
        SchemeValuedPoint.map (normalizedComponentInclusionSchemeMap P) y.1 =
          SchemeValuedPoint.spectrumHomeomorph.symm (Spectrum.ofValuation (v.comap e.toRingHom)) ∧
        (SchemeValuedPoint.spectrumHomeomorph y.1).val = v.comap d.toRingHom := by
  obtain ⟨d, hd⟩ := exists_componentNormalization_rationalEval a b j g φ P hP e he
  let x : RelativeSpectrum v (CurveNormalization.Ring (B ⧸ P)) :=
    ⟨⟨v.comap d.toRingHom⟩, fun c => by
      change v (d (algebraMap F _ c)) = v c
      rw [d.commutes, Algebra.algebraMap_self, RingHom.id_apply]⟩
  let y := RelativeSchemeValuedPoint.affineSpectrumHomeomorph.symm x
  refine ⟨d, y, hd, ?_, ?_⟩
  · apply SchemeValuedPoint.spectrumHomeomorph.injective
    rw [normalizedComponentInclusionSchemeMap_eq_specMap, SchemeValuedPoint.spectrumHomeomorph_map,
      Homeomorph.apply_symm_apply]
    change Spectrum.comap _ (SchemeValuedPoint.spectrumHomeomorph
      (SchemeValuedPoint.spectrumHomeomorph.symm x.1)) = _
    rw [Homeomorph.apply_symm_apply]
    apply Spectrum.ext_val
    intro r
    exact congrArg v (hd r)
  · change (SchemeValuedPoint.spectrumHomeomorph
      (SchemeValuedPoint.spectrumHomeomorph.symm x.1)).val = _
    rw [Homeomorph.apply_symm_apply]

end EnvelopeProperty.AffineLine
