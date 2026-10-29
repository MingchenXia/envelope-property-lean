import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonSectionRelations

/-! # Original homogeneous coefficients on the actual global native fraction spectrum -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Alterations Alterations.Geometry.ProjectiveIdeal
  Alterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem global_spectrumOriginalForm_scalar
    {R S : Type u} [CommRing R] [CommRing S] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (U : X.affineOpens) (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i)
    (d : ℕ) (φ : Γ(X, U) →+* S) (f : Spec (CommRingCat.of S) ⟶ X)
    (hf : Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = f)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) :
    SchemeLineSectionEvaluation.pullbackSectionHom f
        (SchemeLineSectionEvaluation.pullbackSectionHom j
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)) ≫
      (Scheme.Modules.frameViaFactor (Spec.map (CommRingCat.ofHom φ)) U.2.fromSpec f hf
        (originalFormSpecFrame j U i hi d)).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ (pulledForm j U i hi F))) := by
  have hs := SchemeLineSectionEvaluation.frameViaFactor_sectionHom_scalar
    (Spec.map (CommRingCat.ofHom φ)) U.2.fromSpec f hf
    (originalFormSpecFrame j U i hi d)
    (SchemeLineSectionEvaluation.pullbackSectionHom j
      (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF))
    (originalFormSpecCoefficient j U i hi F) (originalFormSpecFrame_scalar j U i hi d F hF)
  have hr : (Spec.map (CommRingCat.ofHom φ)).appTop.hom
      (originalFormSpecCoefficient j U i hi F) =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ (pulledForm j U i hi F)) :=
    congrArg (fun q : Γ(X, U) ⟶ Γ(Spec (CommRingCat.of S), ⊤) =>
      q.hom (pulledForm j U i hi F))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  exact hs.trans (congrArg ModularCurves.unitEndomorphismOfTopSection hr)

private theorem global_tensorIdealInclusion_mono {W : Scheme.{u}} (L : W.Modules)
    (hL : Scheme.Modules.IsInvertible L) (K : W.IdealSheafData) :
    Mono (SchemeTensorObjMorphisms.tensorObjIdealMap L K.toModules K.toModulesInclusion) := by
  let i : K.toModules ⟶ Scheme.Modules.unitObj W := K.toModulesInclusion
  let : Mono i := K.toModulesInclusion_mono
  let : Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i) :=
    SchemeTensorObjMorphisms.mono_tensorObjMap_left L hL i
  change Mono (SchemeTensorObjMorphisms.tensorObjMap (𝟙 L) i ≫
    (Scheme.Modules.tensorObjUnitIso L).hom)
  exact mono_comp _ _

private theorem global_liftedForm_scalarRelation_of_included
    {R : Type u} [CommRing R] {n : ℕ} {X W : Scheme.{u}}
    (f : W ⟶ X) (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F G : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hFJ : F ∈ J.toIdeal) (hGJ : G ∈ J.toIdeal) (r : Γ(W, ⊤))
    (h : SchemeLineSectionEvaluation.pullbackSectionHom f
        (SchemeLineSectionEvaluation.pullbackSectionHom j
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)) =
      ModularCurves.unitEndomorphismOfTopSection r ≫
        SchemeLineSectionEvaluation.pullbackSectionHom f
          (SchemeLineSectionEvaluation.pullbackSectionHom j
            (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d G hG))) :
    liftedFormSection f j J d F hF hFJ =
      ModularCurves.unitEndomorphismOfTopSection r ≫ liftedFormSection f j J d G hG hGJ := by
  let L := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d))
  let K := ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).comap f
  let t := SchemeTensorObjMorphisms.tensorObjIdealMap L K.toModules K.toModulesInclusion
  have hL : Scheme.Modules.IsInvertible L :=
    ((coordinateHyperplanePoleSheafPower_isInvertible (R := R) (0 : Fin (n+1)) d).pullback j).pullback f
  let : Mono t := global_tensorIdealInclusion_mono L hL K
  apply (cancel_mono t).mp
  exact (liftedFormSection_inclusion f j J d F hF hFJ).trans
    (h.trans ((congrArg (fun q => ModularCurves.unitEndomorphismOfTopSection r ≫ q)
      (liftedFormSection_inclusion f j J d G hG hGJ).symm).trans
        (Category.assoc _ _ _).symm))


private theorem global_spectrumOriginalForm_scalarRelation
    {R S : Type u} [CommRing R] [CommRing S] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (U : X.affineOpens) (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i)
    (d : ℕ) (φ : Γ(X, U) →+* S) (f : Spec (CommRingCat.of S) ⟶ X)
    (hf : Spec.map (CommRingCat.ofHom φ) ≫ U.2.fromSpec = f)
    (F G : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (b : S) (hb : φ (pulledForm j U i hi F) = b * φ (pulledForm j U i hi G)) :
    SchemeLineSectionEvaluation.pullbackSectionHom f
        (SchemeLineSectionEvaluation.pullbackSectionHom j
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d F hF)) =
      ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom b) ≫
        SchemeLineSectionEvaluation.pullbackSectionHom f
          (SchemeLineSectionEvaluation.pullbackSectionHom j
            (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (n+1)) d G hG)) := by
  let r := (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom b
  let e := Scheme.Modules.frameViaFactor (Spec.map (CommRingCat.ofHom φ)) U.2.fromSpec f hf
    (originalFormSpecFrame j U i hi d)
  have hsF := global_spectrumOriginalForm_scalar j U i hi d φ f hf F hF
  have hsG := global_spectrumOriginalForm_scalar j U i hi d φ f hf G hG
  have hcoeff : (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ (pulledForm j U i hi F)) =
      r * (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (φ (pulledForm j U i hi G)) :=
    (congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom hb).trans (map_mul _ _ _)
  apply (cancel_mono e.hom).mp
  exact hsF.trans ((congrArg ModularCurves.unitEndomorphismOfTopSection hcoeff).trans
    ((ModularCurves.unitEndomorphismOfTopSection_comp r _).symm.trans
      ((congrArg (fun q => ModularCurves.unitEndomorphismOfTopSection r ≫ q) hsG.symm).trans
        (Category.assoc _ _ _).symm)))


private theorem global_originalRatioPulledForm_mem
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : MvPolynomial (Fin (n+1)) R) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) (i : Fin (n+1)) (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) :
    pulledForm j U i hi F ∈
      ((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).ideal U := by
  let v : J.toIdeal → MvPolynomial (Fin (n+1)) R := Subtype.val
  have hspan : Ideal.span (Set.range v) = J.toIdeal := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact a.property
    · intro a ha
      exact Ideal.subset_span ⟨⟨a, ha⟩, rfl⟩
  have hm : pulledForm j U i hi F ∈
      Ideal.span (Set.range (fun a : J.toIdeal => pulledForm j U i hi (v a))) :=
    Ideal.subset_span ⟨⟨F, hFJ⟩, rfl⟩
  rwa [pulledForm_span j U J v hspan i hi] at hm

/-- The same original GLOBAL old form lifts have their actual native fraction ratio
on the whole pullback by the original global fraction inclusion. Both native structure
triangles, ideal membership and the same original coefficients are derived internally. -/
theorem liftedFormSection_pullback_ratio_on_originalGlobalFractionChart
    {R : Type u} [hR : CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F G : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (hFJ : F ∈ J.toIdeal) (hGJ : G ∈ J.toIdeal)
    (U : X.affineOpens) [hΓ : IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi G ≠ 0) :
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g : Γ(X, U) := pulledForm j U i hi G
    let hg : g ∈ D.ideal U := global_originalRatioPulledForm_mem j J G hGJ U i hi
    let hFmem : pulledForm j U i hi F ∈ D.ideal U :=
      global_originalRatioPulledForm_mem j J F hFJ U i hi
    let S := affineBlowupFractionChart (D.ideal U) g
    let B : Scheme.{u} := affineBlowup (D.ideal U)
    let W : Scheme.{u} := Spec (CommRingCat.of S)
    let Z : Scheme.{u} := Alterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := Alterations.Geometry.BlowupGluing.blowupStructure D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
    let k : B ⟶ Z := Alterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩
    let v : W ⟶ Z := c ≫ k
    let r : Γ(W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
      (affineBlowupChartRatio (D.ideal U) g (pulledForm j U i hi F) hFmem)
    SchemeLineSectionEvaluation.pullbackSectionHom v (liftedFormSection μ j J d F hF hFJ) =
      ModularCurves.unitEndomorphismOfTopSection r ≫
        SchemeLineSectionEvaluation.pullbackSectionHom v (liftedFormSection μ j J d G hG hGJ) := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g : Γ(X, U) := pulledForm j U i hi G
  let hg : g ∈ D.ideal U := global_originalRatioPulledForm_mem j J G hGJ U i hi
  let hFmem : pulledForm j U i hi F ∈ D.ideal U :=
    global_originalRatioPulledForm_mem j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let B : Scheme.{u} := affineBlowup (D.ideal U)
  let W : Scheme.{u} := Spec (CommRingCat.of S)
  let V : Scheme.{u} := Spec Γ(X, U)
  let s : B ⟶ V := affineBlowupStructure (D.ideal U)
  let a : V ⟶ X := U.2.fromSpec
  let Z : Scheme.{u} := Alterations.Geometry.BlowupGluing.blowup D
  let μ : Z ⟶ X := Alterations.Geometry.BlowupGluing.blowupStructure D
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
  let k : B ⟶ Z := Alterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩
  let v : W ⟶ Z := c ≫ k
  let φ : Γ(X, U) →+* S := algebraMap Γ(X, U) S
  let b : S := affineBlowupChartRatio (D.ideal U) g (pulledForm j U i hi F) hFmem
  let r : Γ(W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom b
  have hcs : c ≫ s = Spec.map (CommRingCat.ofHom φ) :=
    affineBlowupChartInclusion_structure (D.ideal U) g hg hg0
  have hkm : k ≫ μ = s ≫ a :=
    Alterations.Geometry.BlowupGluing.chartInclusion_structure D ⟨U.1, U.2⟩
  have hf : Spec.map (CommRingCat.ofHom φ) ≫ a = v ≫ μ :=
    (congrArg (fun f : W ⟶ V => f ≫ a) hcs.symm).trans
      ((Category.assoc c s a).trans
        ((congrArg (fun f : B ⟶ X => c ≫ f) hkm.symm).trans (Category.assoc c k μ).symm))
  have hb : φ (pulledForm j U i hi F) = b * φ g :=
    (affineBlowupFractionChart_mul_ratio (D.ideal U) g hg0 (pulledForm j U i hi F) hFmem).symm.trans
      (mul_comm (φ g) b)
  have hraw := global_spectrumOriginalForm_scalarRelation j U i hi d φ (v ≫ μ) hf F G hF hG b hb
  have hcomp := global_liftedForm_scalarRelation_of_included (v ≫ μ) j J d F G hF hG hFJ hGJ r hraw
  let hcOpen : IsOpenImmersion c :=
    affineBlowupChartInclusion_isOpenImmersion (D.ideal U) g hg hg0
  let hkOpen : IsOpenImmersion k :=
    Alterations.Geometry.BlowupGluing.chartInclusion_isOpenImmersion D ⟨U.1, U.2⟩
  let := hcOpen
  let := hkOpen
  let hvOpen : IsOpenImmersion v := inferInstance
  exact @liftedFormSection_open_scalarRelation R hR n X Z W μ v hvOpen
    j J d F G hF hG hFJ hGJ r hcomp

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
