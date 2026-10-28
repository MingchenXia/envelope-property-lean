/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.NativeCharts
import EnvelopeProperty.Projective.PolynomialGrading
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Actual polynomial projective base change

For every homomorphism of arbitrary commutative coefficient rings, the actual
Mathlib graded Proj map preserves the whole coordinate section maps. Genuine
polynomial tensor pushouts and the true coordinate scheme cover prove the
entire coefficient square cartesian, including both projection identities.
The polynomial-coefficient specialization is the actual projective-space
product with the affine-line base. No coefficient injectivity, field,
reducedness, Noetherianity or analytic coherent-sheaf comparison is assumed.
-/

open scoped Classical Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjBerk
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

/-- The actual coefficient map preserves every total-degree homogeneous component. -/
def coefficientGradedMap (φ : R →+* S) : ProjectiveGrading R n →+*ᵍ ProjectiveGrading S n where
  __ := MvPolynomial.map φ
  map_mem := fun h => h.map φ

@[simp]
theorem coefficientGradedMap_apply (φ : R →+* S) (F : MvPolynomial (Fin (n + 1)) R) :
    coefficientGradedMap φ F = MvPolynomial.map φ F := rfl

/-- Every target irrelevant generator is the image of the same original coordinate. -/
theorem coefficientGradedMap_irrelevant_le (φ : R →+* S) :
    HomogeneousIdeal.irrelevant (ProjectiveGrading S n) ≤
      (HomogeneousIdeal.irrelevant (ProjectiveGrading R n)).map (coefficientGradedMap φ) := by
  rw [← toIdeal_le_toIdeal_iff]
  change (HomogeneousIdeal.irrelevant (ProjectiveGrading S n)).toIdeal ≤
    (HomogeneousIdeal.irrelevant (ProjectiveGrading R n)).toIdeal.map (MvPolynomial.map φ)
  rw [irrelevant_eq_idealOfVars, irrelevant_eq_idealOfVars, idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change (X i : MvPolynomial (Fin (n + 1)) S) ∈ Ideal.map (MvPolynomial.map φ) (idealOfVars (Fin (n + 1)) R)
  simpa only [MvPolynomial.map_X] using
    (Ideal.mem_map_of_mem (MvPolynomial.map φ)
      (show (X i : MvPolynomial (Fin (n + 1)) R) ∈ idealOfVars (Fin (n + 1)) R from
        Ideal.subset_span ⟨i, rfl⟩))

/-- Actual polynomial Proj restriction along its full coefficient-ring map. -/
def nativeCoefficientMap (φ : R →+* S) : NativeProjectiveScheme S n ⟶ NativeProjectiveScheme R n :=
  AlgebraicGeometry.Proj.map (coefficientGradedMap φ) (coefficientGradedMap_irrelevant_le φ)

/-- The full native coordinate-open preimage is the same coordinate open over the new base. -/
theorem nativeCoefficientMap_preimage_coordinateOpen (φ : R →+* S) (j : Fin (n + 1)) :
    nativeCoefficientMap φ ⁻¹ᵁ nativeCoordinateOpen j = nativeCoordinateOpen (R := S) j := by
  change AlgebraicGeometry.Proj.map _ _ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen _ (X j) = _
  rw [AlgebraicGeometry.Proj.map_preimage_basicOpen]
  simp only [coefficientGradedMap_apply, MvPolynomial.map_X]
  rfl

/-- The actual homogeneous coordinate localization map, with the mapped denominator identified. -/
def homogeneousCoordinateMap (φ : R →+* S) (j : Fin (n + 1)) :
    HomogeneousChartRing R j →+* HomogeneousChartRing S j := by
  exact HomogeneousLocalization.map (coefficientGradedMap φ)
    (P := Submonoid.powers (X j)) (Q := Submonoid.powers (X j)) (by
      rintro _ ⟨d, rfl⟩
      exact ⟨d, by simp only [map_pow, coefficientGradedMap_apply, MvPolynomial.map_X]⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The entire homogeneous chart square, before replacing actual fractions by affine coordinates. -/
theorem nativeCoefficientMap_homogeneousChart (φ : R →+* S) (j : Fin (n + 1)) :
    (nativeHomogeneousChartSchemeIso (R := S) j).inv ≫ (nativeCoordinateOpen j).ι ≫
      nativeCoefficientMap φ =
        Spec.map (CommRingCat.ofHom (homogeneousCoordinateMap φ j)) ≫
          (nativeHomogeneousChartSchemeIso (R := R) j).inv ≫ (nativeCoordinateOpen j).ι := by
  rw [nativeHomogeneousChartSchemeIso_eq, nativeHomogeneousChartSchemeIso_eq]
  change _ ≫ (AlgebraicGeometry.Proj.basicOpen (ProjectiveGrading S n) (X j)).ι ≫ _ =
    _ ≫ _ ≫ (AlgebraicGeometry.Proj.basicOpen (ProjectiveGrading R n) (X j)).ι
  rw [← Category.assoc]
  erw [AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
  erw [AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
  have aux (s : MvPolynomial (Fin (n + 1)) S)
      (hs : s ∈ ProjectiveGrading S n 1) (he : coefficientGradedMap φ (X j) = s) :
      AlgebraicGeometry.Proj.awayι (ProjectiveGrading S n) s hs (by decide : 0 < (1 : ℕ)) ≫
        nativeCoefficientMap φ =
          Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (coefficientGradedMap φ)
            (P := Submonoid.powers (X j)) (Q := Submonoid.powers s) (by
              rintro _ ⟨d, rfl⟩
              exact ⟨d, by simp only [map_pow, he]⟩))) ≫
            AlgebraicGeometry.Proj.awayι (ProjectiveGrading R n) (X j)
              (MvPolynomial.isHomogeneous_X R j) (by decide : 0 < (1 : ℕ)) := by
    subst s
    exact AlgebraicGeometry.Proj.awayι_comp_map (coefficientGradedMap φ)
      (coefficientGradedMap_irrelevant_le φ) (by decide : 0 < (1 : ℕ))
      (X j) (MvPolynomial.isHomogeneous_X R j)
  exact aux (X j) (MvPolynomial.isHomogeneous_X S j)
    (by simp only [coefficientGradedMap_apply, MvPolynomial.map_X])

/-- Dehomogenizing commutes with the entire coefficient polynomial map. -/
theorem coordinateDehom_map (φ : R →+* S) (j : Fin (n + 1))
    (F : MvPolynomial (Fin (n + 1)) R) :
    coordinateDehom j (MvPolynomial.map φ F) = MvPolynomial.map φ (coordinateDehom j F) := by
  induction F using MvPolynomial.induction_on with
  | C r =>
    simp only [MvPolynomial.map_C, coordinateDehom, MvPolynomial.aeval_C]
    exact (MvPolynomial.map_C φ r).symm
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    simp only [map_mul, MvPolynomial.map_X, coordinateDehom, MvPolynomial.aeval_X] at *
    rw [hF]
    congr 1
    by_cases h : i = j
    · simp only [coordinateDehomCoord, dif_pos h, map_one]
    · simp only [coordinateDehomCoord, dif_neg h, MvPolynomial.map_X]

set_option backward.isDefEq.respectTransparency false in
/-- The actual homogeneous coordinate map preserves every original dehomogenized fraction. -/
theorem homogeneousCoordinateMap_dehom (φ : R →+* S) (j : Fin (n + 1))
    (a : HomogeneousChartRing R j) :
    homogeneousChartDehom j (homogeneousCoordinateMap φ j a) =
      MvPolynomial.map φ (homogeneousChartDehom j a) := by
  obtain ⟨d, F, hF, rfl⟩ := a.mk_surjective (ProjectiveGrading R n) (MvPolynomial.isHomogeneous_X R j)
  have he : homogeneousCoordinateMap φ j
      (HomogeneousLocalization.Away.mk (ProjectiveGrading R n)
        (MvPolynomial.isHomogeneous_X R j) d F hF) =
        HomogeneousLocalization.Away.mk (ProjectiveGrading S n)
          (MvPolynomial.isHomogeneous_X S j) d (MvPolynomial.map φ F) (hF.map φ) := by
    apply HomogeneousLocalization.val_injective
    dsimp only [homogeneousCoordinateMap, HomogeneousLocalization.Away.mk]
    rw [HomogeneousLocalization.map_mk]
    simp only [HomogeneousLocalization.val_mk, coefficientGradedMap_apply]
    congr 1
    apply Subtype.ext
    simp only [map_pow, MvPolynomial.map_X]
  rw [he]
  rw [homogeneousChartDehom_mk, homogeneousChartDehom_mk]
  exact coordinateDehom_map φ j F

/-- The entire homogeneous-coordinate-ring map is conjugate to coefficient polynomial mapping. -/
theorem homogeneousCoordinateMap_equiv (φ : R →+* S) (j : Fin (n + 1)) :
    (homogeneousChartEquiv (R := S) j).toRingHom.comp (homogeneousCoordinateMap φ j) =
      (MvPolynomial.map φ).comp (homogeneousChartEquiv (R := R) j).toRingHom := by
  apply RingHom.ext
  intro a
  exact homogeneousCoordinateMap_dehom φ j a

set_option backward.isDefEq.respectTransparency false in
/-- Every actual scheme coordinate chart preserves the whole coefficient polynomial map. -/
theorem nativeCoefficientMap_coordinateChart (φ : R →+* S) (j : Fin (n + 1)) :
    nativeCoordinateInclusion (R := S) j ≫ nativeCoefficientMap φ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j)) ≫
        nativeCoordinateInclusion (R := R) j := by
  have h : Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := S) j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (homogeneousCoordinateMap φ j)) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j)) ≫
          Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact homogeneousCoordinateMap_equiv φ j
  change (Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := S) j).toRingHom) ≫
    (nativeHomogeneousChartSchemeIso j).inv ≫ (nativeCoordinateOpen j).ι) ≫ _ =
      _ ≫ Spec.map (CommRingCat.ofHom (homogeneousChartEquiv (R := R) j).toRingHom) ≫
        (nativeHomogeneousChartSchemeIso j).inv ≫ (nativeCoordinateOpen j).ι
  simp only [Category.assoc]
  rw [nativeCoefficientMap_homogeneousChart, ← Category.assoc, h, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The actual restriction between coordinate opens is the entire coefficient polynomial scheme map. -/
theorem nativeCoefficientMap_coordinateRestriction (φ : R →+* S) (j : Fin (n + 1)) :
    (nativeCoordinateSchemeIso (R := S) j).inv ≫
      (nativeCoefficientMap φ).resLE (nativeCoordinateOpen j) (nativeCoordinateOpen j)
        (by rw [nativeCoefficientMap_preimage_coordinateOpen]) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j)) ≫
        (nativeCoordinateSchemeIso (R := R) j).inv := by
  apply (cancel_mono (nativeCoordinateOpen (R := R) j).ι).mp
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  exact nativeCoefficientMap_coordinateChart φ j

set_option backward.isDefEq.respectTransparency false in
/-- Every original affine polynomial section is pulled back by the whole coefficient map. -/
theorem nativeCoefficientMap_coordinateSections (φ : R →+* S) (j : Fin (n + 1)) :
    (nativeCoordinateSectionsIso (R := R) j).hom ≫
      (nativeCoefficientMap φ).appLE (nativeCoordinateOpen j) (nativeCoordinateOpen j)
        (by rw [nativeCoefficientMap_preimage_coordinateOpen]) =
      CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j) ≫
        (nativeCoordinateSectionsIso (R := S) j).hom := by
  let gr := (nativeCoefficientMap φ).resLE (nativeCoordinateOpen j) (nativeCoordinateOpen j)
    (by rw [nativeCoefficientMap_preimage_coordinateOpen])
  have hΓ : gr.appTop ≫ (nativeCoordinateSchemeIso (R := S) j).inv.appTop =
      (nativeCoordinateSchemeIso (R := R) j).inv.appTop ≫
        (Spec.map (CommRingCat.ofHom
          (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j))).appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg Scheme.Hom.appTop (nativeCoefficientMap_coordinateRestriction φ j)
  have hg : (nativeCoordinateOpen (R := R) j).topIso.hom ≫
      (nativeCoefficientMap φ).appLE (nativeCoordinateOpen j) (nativeCoordinateOpen j)
        (by rw [nativeCoefficientMap_preimage_coordinateOpen]) ≫
      (nativeCoordinateOpen (R := S) j).topIso.inv = gr.appTop := by
    exact (Scheme.Hom.resLE_app_top (nativeCoefficientMap φ)
      (by rw [nativeCoefficientMap_preimage_coordinateOpen])).symm
  have hg' : (nativeCoefficientMap φ).appLE (nativeCoordinateOpen j) (nativeCoordinateOpen j)
        (by rw [nativeCoefficientMap_preimage_coordinateOpen]) ≫
      (nativeCoordinateOpen (R := S) j).topIso.inv =
      (nativeCoordinateOpen (R := R) j).topIso.inv ≫ gr.appTop := by
    rw [← cancel_epi (nativeCoordinateOpen (R := R) j).topIso.hom,
      Iso.hom_inv_id_assoc, hg]
  apply (cancel_mono ((nativeCoordinateOpen (R := S) j).topIso.inv ≫
    (nativeCoordinateSchemeIso (R := S) j).inv.appTop)).mp
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (nativeCoordinateSchemeIso (R := S) j).inv.appTop]
  rw [hg', Category.assoc, hΓ]
  rw [reassoc_of% nativeCoordinateSectionsIso_cancel (R := R) j,
    nativeCoordinateSectionsIso_cancel]
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

/-- The coefficient chart square is a genuine open-immersion pullback. -/
theorem isPullback_nativeCoefficientMap_coordinateChart (φ : R →+* S) (j : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map φ : CoordinateRing R j →+* CoordinateRing S j)))
      (nativeCoordinateInclusion (R := S) j) (nativeCoordinateInclusion (R := R) j)
      (nativeCoefficientMap φ) := by
  have := nativeCoordinateInclusion_isOpenImmersion (R := R) j
  have := nativeCoordinateInclusion_isOpenImmersion (R := S) j
  apply IsOpenImmersion.isPullback
  · exact nativeCoefficientMap_coordinateChart φ j
  · rw [nativeCoordinateInclusion_opensRange, nativeCoordinateInclusion_opensRange,
      nativeCoefficientMap_preimage_coordinateOpen]

/-- A genuine scheme coordinate cover, with the actual affine polynomial chart inclusions. -/
def nativeCoordinateCover : (NativeProjectiveScheme R n).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin (n + 1))
    (fun j => Spec (CommRingCat.of (CoordinateRing R j))) (fun j => nativeCoordinateInclusion j)
    (by
      intro p
      have hp : p ∈ ⨆ j : Fin (n + 1), nativeCoordinateOpen (R := R) j := by
        have htop : (⨆ i : Fin (n + 1), nativeCoordinateOpen (R := R) i) = ⊤ := by
          apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
          rw [irrelevant_eq_idealOfVars, MvPolynomial.idealOfVars]
        rw [htop]
        trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
      have := nativeCoordinateInclusion_isOpenImmersion (R := R) j
      have hmem : p ∈ Set.range (nativeCoordinateInclusion (R := R) j) := by
        change p ∈ (nativeCoordinateInclusion (R := R) j).opensRange
        rw [nativeCoordinateInclusion_opensRange]
        exact hj
      obtain ⟨q, hq⟩ := hmem
      exact ⟨j, q, hq⟩)
    (fun j => nativeCoordinateInclusion_isOpenImmersion j)

/-- The actual polynomial coordinate tensor square becomes a genuine affine scheme pullback. -/
theorem isPullback_coordinatePolynomialBaseChange [Algebra R S] (j : Fin (n + 1)) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.map (algebraMap R S) : CoordinateRing R j →+* CoordinateRing S j)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (CoordinateRing S j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let : Algebra (CoordinateRing R j) (CoordinateRing S j) := MvPolynomial.algebraMvPolynomial
  have h := CommRingCat.isPushout_of_isPushout R S (CoordinateRing R j) (CoordinateRing S j)
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ h
  exact hp.flip

set_option backward.isDefEq.respectTransparency false in
/-- The actual original-base polynomial Proj square is cartesian over every coefficient homomorphism. -/
theorem isPullback_nativeCoefficientBaseChange (φ : R →+* S) :
    IsPullback (nativeCoefficientMap (n := n) φ) (nativeStructureMap (R := S) (n := n))
      (nativeStructureMap (R := R) (n := n)) (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra R S := φ.toAlgebra
  apply Scheme.isPullback_of_openCover _ _ _ _ (nativeCoordinateCover (R := R) (n := n))
  intro j
  change Fin (n + 1) at j
  change IsPullback (pullback.snd (nativeCoefficientMap φ) (nativeCoordinateInclusion j))
    (pullback.fst (nativeCoefficientMap φ) (nativeCoordinateInclusion j) ≫ nativeStructureMap)
    (nativeCoordinateInclusion j ≫ nativeStructureMap) (Spec.map (CommRingCat.ofHom φ))
  have hR : nativeCoordinateInclusion (R := R) j ≫ nativeStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j))) :=
    nativeCoordinateChart_over_base j
  have hS : nativeCoordinateInclusion (R := S) j ≫ nativeStructureMap =
      Spec.map (CommRingCat.ofHom (algebraMap S (CoordinateRing S j))) :=
    nativeCoordinateChart_over_base j
  rw [hR]
  let e := (isPullback_nativeCoefficientMap_coordinateChart φ j).flip.isoPullback
  apply (isPullback_coordinatePolynomialBaseChange (R := R) (S := S) j).of_iso e
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · exact (isPullback_nativeCoefficientMap_coordinateChart φ j).flip.isoPullback_hom_snd.symm
  · change _ = e.hom ≫ pullback.fst (nativeCoefficientMap φ) (nativeCoordinateInclusion j) ≫ _
    rw [← Category.assoc,
      (isPullback_nativeCoefficientMap_coordinateChart φ j).flip.isoPullback_hom_fst, hS]
    exact Category.comp_id _
  · rfl
  · rfl

/-- The actual coefficient structure diagram commutes on the entire schemes. -/
theorem nativeCoefficientMap_over_base (φ : R →+* S) :
    nativeCoefficientMap (n := n) φ ≫ nativeStructureMap =
      nativeStructureMap ≫ Spec.map (CommRingCat.ofHom φ) :=
  (isPullback_nativeCoefficientBaseChange φ).w

/-- The canonical actual polynomial projective scalar-extension isomorphism. -/
def nativeCoefficientBaseChangeIso (φ : R →+* S) :
    NativeProjectiveScheme S n ≅ pullback (nativeStructureMap (R := R) (n := n))
      (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_nativeCoefficientBaseChange φ).isoPullback

/-- The whole projective projection is the actual graded coefficient map. -/
@[reassoc]
theorem nativeCoefficientBaseChangeIso_hom_fst (φ : R →+* S) :
    (nativeCoefficientBaseChangeIso (n := n) φ).hom ≫ pullback.fst _ _ = nativeCoefficientMap φ :=
  (isPullback_nativeCoefficientBaseChange φ).isoPullback_hom_fst

/-- The whole coefficient projection is the actual original-coefficient structure map. -/
@[reassoc]
theorem nativeCoefficientBaseChangeIso_hom_snd (φ : R →+* S) :
    (nativeCoefficientBaseChangeIso (n := n) φ).hom ≫ pullback.snd _ _ = nativeStructureMap :=
  (isPullback_nativeCoefficientBaseChange φ).isoPullback_hom_snd

/-- The model over the polynomial coefficient ring is the actual projective-line-base product. -/
def nativePolynomialLineProductIso (R : Type u) [CommRing R] (n : ℕ) :
    NativeProjectiveScheme R[X] n ≅ pullback (nativeStructureMap (R := R) (n := n))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))) :=
  nativeCoefficientBaseChangeIso Polynomial.C

end EnvelopeProperty.ProjBerk
