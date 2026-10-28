import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationGaussPoint

/-! # The genuine original Cartesian unit-open Gauss point

The original residue coefficient map, actual Laurent coefficient transport,
and already proved original TC Cartesian square construct every map and point.
No commuting square, Gauss comparison, or point comparison is supplied.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped NNReal LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
open Berkovich

/-- The ACTUAL Laurent coefficient map preserves every original constant. -/
theorem originalLaurentCoefficientMap_C {A B : Type u} [CommRing A] [CommRing B]
    (ρ : A →+* B) (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ ρ (LaurentPolynomial.C a) = LaurentPolynomial.C (ρ a) := by
  change AddMonoidAlgebra.mapRingHom ℤ ρ (AddMonoidAlgebra.single 0 a) =
    AddMonoidAlgebra.single 0 (ρ a)
  exact AddMonoidAlgebra.mapRingHom_single ρ 0 a

/-- The ACTUAL Laurent coefficient map preserves every original integer monomial. -/
theorem originalLaurentCoefficientMap_T {A B : Type u} [CommRing A] [CommRing B]
    (ρ : A →+* B) (n : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ ρ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ ρ (AddMonoidAlgebra.single n 1) =
    AddMonoidAlgebra.single n 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/-- The true coefficientwise Laurent ring map transports the ENTIRE genuine
Gauss point, using actual finite coefficients; no injectivity assumption. -/
theorem originalLaurentGauss_comap {A B : Type u} [CommRing A] [CommRing B]
    (ρ : A →+* B) (v : Valuation B ℝ≥0) (r : ℝ≥0) (hr : 0 < r) :
    Spectrum.comap (AddMonoidAlgebra.mapRingHom ℤ ρ) (Spectrum.laurentGauss v r hr) =
      Spectrum.laurentGauss (v.comap ρ) r hr := by
  classical
  apply Spectrum.ext_val
  intro F
  change (Spectrum.laurentGauss v r hr).val (AddMonoidAlgebra.mapRingHom ℤ ρ F) =
    (Spectrum.laurentGauss (v.comap ρ) r hr).val F
  apply le_antisymm
  · have hF : F = ∑ n ∈ F.coeff.support, AddMonoidAlgebra.single n (F.coeff n) := by
      simpa only [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single F).symm
    have hm := congrArg (AddMonoidAlgebra.mapRingHom ℤ ρ) hF
    simp only [map_sum, AddMonoidAlgebra.mapRingHom_single] at hm
    rw [hm]
    exact (Spectrum.laurentGauss v r hr).val.map_sum_le fun n _ => by
      rw [LaurentPolynomial.single_eq_C_mul_T, map_mul,
        Spectrum.laurentGauss_val_C, Spectrum.laurentGauss_val_T]
      exact Spectrum.le_laurentGauss_val (v.comap ρ) r hr F n
  · rw [Spectrum.laurentGauss_val_eq_sup (v.comap ρ) r hr F]
    apply Finset.sup_le
    intro n _
    have h := Spectrum.le_laurentGauss_val v r hr (AddMonoidAlgebra.mapRingHom ℤ ρ F) n
    simpa only [AddMonoidAlgebra.coeff_mapRingHom, Valuation.comap_apply] using h

/-- The genuine native scheme point obeys the ACTUAL coefficient-map Gauss law. -/
theorem originalNativeLaurentGaussPoint_map_coefficients
    {A B : Type u} [CommRing A] [CommRing B]
    (ρ : A →+* B) (v : Valuation B ℝ≥0) (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ ρ)))
        (originalNativeLaurentGaussPoint v r hr) =
      originalNativeLaurentGaussPoint (v.comap ρ) r hr := by
  apply (SchemeValuedPoint.spectrumHomeomorph (A := A[T;T⁻¹])).injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map, originalNativeLaurentGaussPoint,
    Homeomorph.apply_symm_apply, originalNativeLaurentGaussPoint, Homeomorph.apply_symm_apply]
  exact originalLaurentGauss_comap ρ v r hr

/-- The ORIGINAL residue coefficient map derives its ENTIRE actual scheme
triangle, with no coefficient boundedness or square comparison premise. -/
theorem originalNativeResidueBaseMap_square {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)}
    (x : RelativeSchemeValuedPoint v f) :
    Y.fromSpecResidueField x.1.point ≫ f =
      Spec.map (CommRingCat.ofHom (RelativeSchemeValuedPoint.residueBaseMap x)) := by
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (Y.fromSpecResidueField x.1.point ≫ f).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (RelativeSchemeValuedPoint.residueBaseMap x))).appTop
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality]
  apply (cancel_mono (Scheme.ΓSpecIso (Y.residueField x.1.point)).hom).mp
  simp only [Category.assoc, SchemeValuedPoint.fromSpecResidueField_appTop]
  have hi : (Scheme.ΓSpecIso (CommRingCat.of (Y.residueField x.1.point))).inv ≫
      (Scheme.ΓSpecIso (Y.residueField x.1.point)).hom = 𝟙 _ :=
    (Scheme.ΓSpecIso (Y.residueField x.1.point)).inv_hom_id
  rw [hi, Category.comp_id]
  apply CommRingCat.hom_ext
  ext a
  change Y.Γevaluation x.1.point (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) =
    RelativeSchemeValuedPoint.residueBaseMap x a
  simp only [RelativeSchemeValuedPoint.residueBaseMap, RingHom.comp_apply,
    SchemeValuedPoint.sectionBaseMap_apply, homOfLE_refl, op_id]
  rw [Y.presheaf.map_id]
  rfl

/-- The SAME original residue coefficient map has the ENTIRE prescribed valuation. -/
theorem originalNativeResidueBaseMap_valuation {R : Type u} [CommRing R]
    {v : Valuation R ℝ≥0} {Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)}
    (x : RelativeSchemeValuedPoint v f) :
    x.1.residueVal.comap (RelativeSchemeValuedPoint.residueBaseMap x) = v :=
  Valuation.ext (fun a => RelativeSchemeValuedPoint.residueBaseMap_val x a)

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))}
  (C : NativeTestConfiguration.TestConfiguration k X) {v : Valuation k ℝ≥0}
  (x : RelativeSchemeValuedPoint v X.hom)

/-- The actual original residue Laurent components DERIVE their compatibility
in the SAME original test-configuration Cartesian square. -/
theorem originalTestConfigurationGaussMorph_compatibility :
    (Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.C : X.left.residueField x.1.point →+*
          (X.left.residueField x.1.point)[T;T⁻¹])) ≫
        X.left.fromSpecResidueField x.1.point) ≫ X.hom =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k[T;T⁻¹])) := by
  rw [Category.assoc, originalNativeResidueBaseMap_square,
    ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change LaurentPolynomial.C (RelativeSchemeValuedPoint.residueBaseMap x a) =
    AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x)
      (LaurentPolynomial.C a)
  exact (originalLaurentCoefficientMap_C _ a).symm

/-- The ACTUAL original Cartesian universal property constructs the whole
original unit-open morphism from the SAME original residue Laurent scheme. -/
def originalTestConfigurationGaussMorph :
    Spec (CommRingCat.of (X.left.residueField x.1.point)[T;T⁻¹]) ⟶ C.unitOpen.toScheme :=
  (originalTestConfigurationUnitCartesian C).lift
    (Spec.map (CommRingCat.ofHom
      (LaurentPolynomial.C : X.left.residueField x.1.point →+*
        (X.left.residueField x.1.point)[T;T⁻¹])) ≫
      X.left.fromSpecResidueField x.1.point)
    (Spec.map (CommRingCat.ofHom
      (AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x))))
    (originalTestConfigurationGaussMorph_compatibility x)

/-- The entire FIRST original geometric projection retains the actual residue morphism. -/
theorem originalTestConfigurationGaussMorph_projection :
    originalTestConfigurationGaussMorph C x ≫ originalTestConfigurationUnitProjection C =
      Spec.map (CommRingCat.ofHom
        (LaurentPolynomial.C : X.left.residueField x.1.point →+*
          (X.left.residueField x.1.point)[T;T⁻¹])) ≫
        X.left.fromSpecResidueField x.1.point :=
  (originalTestConfigurationUnitCartesian C).lift_fst _ _ _

/-- The entire SECOND original geometric projection retains the actual Laurent map. -/
theorem originalTestConfigurationGaussMorph_parameter :
    originalTestConfigurationGaussMorph C x ≫ originalTestConfigurationUnitParameter C =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapRingHom ℤ (RelativeSchemeValuedPoint.residueBaseMap x))) :=
  (originalTestConfigurationUnitCartesian C).lift_snd _ _ _

/-- The SAME original test configuration has its CONSTRUCTED true unit-open
Gauss point, from the original point and genuine Laurent Gauss localization. -/
def originalTestConfigurationUnitGaussPoint (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint C.unitOpen.toScheme :=
  SchemeValuedPoint.map (originalTestConfigurationGaussMorph C x)
    (originalNativeLaurentGaussPoint x.1.residueVal r hr)

/-- Its ENTIRE first original valued projection is the SAME original point. -/
theorem originalTestConfigurationUnitGaussPoint_projection (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (originalTestConfigurationUnitProjection C)
        (originalTestConfigurationUnitGaussPoint C x r hr) = x.1 := by
  rw [originalTestConfigurationUnitGaussPoint, ← SchemeValuedPoint.map_comp,
    originalTestConfigurationGaussMorph_projection, originalNativeResidueLaurentGaussPoint_map]

/-- Its ENTIRE original Laurent parameter point is the actual Gauss point
of the original prescribed coefficient valuation, with no comparison input. -/
theorem originalTestConfigurationUnitGaussPoint_parameter (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map (originalTestConfigurationUnitParameter C)
        (originalTestConfigurationUnitGaussPoint C x r hr) =
      originalNativeLaurentGaussPoint v r hr := by
  rw [originalTestConfigurationUnitGaussPoint, ← SchemeValuedPoint.map_comp,
    originalTestConfigurationGaussMorph_parameter, originalNativeLaurentGaussPoint_map_coefficients,
    originalNativeResidueBaseMap_valuation]

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
