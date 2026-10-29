import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonOpenTransfer

/-! # The same old blowup lift on its actual original fraction charts -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Alterations Alterations.Geometry.ProjectiveIdeal
  Alterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem originalPulledForm_mem
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

private theorem originalFractionChart_isOpenImmersion
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : MvPolynomial (Fin (n+1)) R) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) [IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi F ≠ 0) :
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g : Γ(X, U) := pulledForm j U i hi F
    let hg : g ∈ D.ideal U := originalPulledForm_mem j J F hFJ U i hi
    let S := affineBlowupFractionChart (D.ideal U) g
    let B : Scheme.{u} := affineBlowup (D.ideal U)
    let W : Scheme.{u} := Spec (CommRingCat.of S)
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
    @IsOpenImmersion W B c := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g : Γ(X, U) := pulledForm j U i hi F
  let hg : g ∈ D.ideal U := originalPulledForm_mem j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let B : Scheme.{u} := affineBlowup (D.ideal U)
  let W : Scheme.{u} := Spec (CommRingCat.of S)
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
  change @IsOpenImmersion W B c
  exact affineBlowupChartInclusion_isOpenImmersion (R := Γ(X, U))
    (I := D.ideal U) (g := g) (hg := hg) (hg0 := hg0)


private theorem compositeLift_isIso_on_originalFractionChart
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) [IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi F ≠ 0) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g : Γ(X, U) := pulledForm j U i hi F
    let hg : g ∈ D.ideal U := originalPulledForm_mem j J F hFJ U i hi
    let S := affineBlowupFractionChart (D.ideal U) g
    let B : Scheme.{u} := affineBlowup (D.ideal U)
    let W : Scheme.{u} := Spec (CommRingCat.of S)
    let V : Scheme.{u} := Spec Γ(X, U)
    let s : B ⟶ V := affineBlowupStructure (D.ideal U)
    let a : V ⟶ X := U.2.fromSpec
    let μ : B ⟶ X := s ≫ a
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
    let T' : W.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback (c ≫ μ)).obj M)
      (D.comap (c ≫ μ)).toModules
    @IsIso W.Modules _ (Scheme.Modules.unitObj W) T'
      (liftedFormSection (R := R) (n := n) (X := X) (Z := W) (c ≫ μ) j J d F hF hFJ) := by
  let M : X.Modules := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g : Γ(X, U) := pulledForm j U i hi F
  let hg : g ∈ D.ideal U := originalPulledForm_mem j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let B : Scheme.{u} := affineBlowup (D.ideal U)
  let W : Scheme.{u} := Spec (CommRingCat.of S)
  let V : Scheme.{u} := Spec Γ(X, U)
  let s : B ⟶ V := affineBlowupStructure (D.ideal U)
  let a : V ⟶ X := U.2.fromSpec
  let μ : B ⟶ X := s ≫ a
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
  let T' : W.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback (c ≫ μ)).obj M)
    (D.comap (c ≫ μ)).toModules
  let γ : Scheme.Modules.unitObj W ⟶ T' :=
    liftedFormSection (R := R) (n := n) (X := X) (Z := W) (c ≫ μ) j J d F hF hFJ
  change @IsIso W.Modules _ (Scheme.Modules.unitObj W) T' γ
  have hb := liftedFormSection_isIso_on_originalFractionChart
    (R := R) (n := n) (X := X) j J d F hF hFJ U i hi hg0
  have hf : (c ≫ s) ≫ a = c ≫ μ :=
    @Category.assoc Scheme.{u} _ W B V X c s a
  exact Eq.mp (congrArg (fun f : W ⟶ X => @IsIso W.Modules _ (Scheme.Modules.unitObj W)
    (Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj M) (D.comap f).toModules)
    (liftedFormSection (R := R) (n := n) (X := X) (Z := W) f j J d F hF hFJ)) hf) hb


/-- The same old homogeneous-form lift on the whole original affine blowup is
an actual basis after pullback to its native specified-generator fraction chart.
Its composite basis and the canonical open comparison are derived internally. -/
theorem liftedFormSection_pullback_isIso_on_originalFractionChart
    {R : Type u} [hR : CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) [hΓ : IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi F ≠ 0) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g : Γ(X, U) := pulledForm j U i hi F
    let hg : g ∈ D.ideal U := originalPulledForm_mem j J F hFJ U i hi
    let S := affineBlowupFractionChart (D.ideal U) g
    let B : Scheme.{u} := affineBlowup (D.ideal U)
    let W : Scheme.{u} := Spec (CommRingCat.of S)
    let V : Scheme.{u} := Spec Γ(X, U)
    let s : B ⟶ V := affineBlowupStructure (D.ideal U)
    let a : V ⟶ X := U.2.fromSpec
    let μ : B ⟶ X := s ≫ a
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
    let T : B.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
      (D.comap μ).toModules
    @IsIso W.Modules _ (Scheme.Modules.unitObj W) ((Scheme.Modules.pullback c).obj T)
      (SchemeLineSectionEvaluation.pullbackSectionHom (M := T) c
        (liftedFormSection (R := R) (n := n) (X := X) (Z := B) μ j J d F hF hFJ)) := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g : Γ(X, U) := pulledForm j U i hi F
  let hg : g ∈ D.ideal U := originalPulledForm_mem j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let B : Scheme.{u} := affineBlowup (D.ideal U)
  let W : Scheme.{u} := Spec (CommRingCat.of S)
  let V : Scheme.{u} := Spec Γ(X, U)
  let s : B ⟶ V := affineBlowupStructure (D.ideal U)
  let a : V ⟶ X := U.2.fromSpec
  let μ : B ⟶ X := s ≫ a
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
  let hcOpen : @IsOpenImmersion W B c :=
    @originalFractionChart_isOpenImmersion R hR n X j J F hFJ U hΓ i hi hg0
  have hc := @compositeLift_isIso_on_originalFractionChart R hR n X
    j J d F hF hFJ U hΓ i hi hg0
  exact @liftedFormSection_isIso_pullback_of_composite R hR n X B W μ c hcOpen
    j J d F hF hFJ hc

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
