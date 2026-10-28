import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonFractionLift

/-! # The same old global blowup lift on its actual original fraction charts -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
  DeJongAlterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem globalOriginalPulledForm_mem
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ DeJongAlterations.projectiveSpace R n)
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


private theorem nativeGlobalFraction_isOpenImmersion {X : Scheme.{u}}
    (D : X.IdealSheafData) (U : X.affineOpens) [IsDomain Γ(X, U)]
    (g : Γ(X, U)) (hg : g ∈ D.ideal U) (hg0 : g ≠ 0) :
    IsOpenImmersion (affineBlowupChartInclusion (D.ideal U) g hg hg0 ≫
      DeJongAlterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩) := by
  let hc : IsOpenImmersion (affineBlowupChartInclusion (D.ideal U) g hg hg0) :=
    affineBlowupChartInclusion_isOpenImmersion (R := Γ(X, U))
      (I := D.ideal U) (g := g) (hg := hg) (hg0 := hg0)
  let hk : IsOpenImmersion
      (DeJongAlterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩) :=
    DeJongAlterations.Geometry.BlowupGluing.chartInclusion_isOpenImmersion D ⟨U.1, U.2⟩
  let := hc
  let := hk
  infer_instance

private theorem globalCompositeLift_isIso_on_originalFractionChart
    {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) [IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi F ≠ 0) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g : Γ(X, U) := pulledForm j U i hi F
    let hg : g ∈ D.ideal U := globalOriginalPulledForm_mem j J F hFJ U i hi
    let S := affineBlowupFractionChart (D.ideal U) g
    let B : Scheme.{u} := affineBlowup (D.ideal U)
    let W : Scheme.{u} := Spec (CommRingCat.of S)
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
    let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩
    let v : W ⟶ Z := c ≫ k
    let T' : W.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback (v ≫ μ)).obj M)
      (D.comap (v ≫ μ)).toModules
    @IsIso W.Modules _ (Scheme.Modules.unitObj W) T'
      (liftedFormSection (R := R) (n := n) (X := X) (Z := W) (v ≫ μ) j J d F hF hFJ) := by
  let M : X.Modules := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g : Γ(X, U) := pulledForm j U i hi F
  let hg : g ∈ D.ideal U := globalOriginalPulledForm_mem j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let B : Scheme.{u} := affineBlowup (D.ideal U)
  let W : Scheme.{u} := Spec (CommRingCat.of S)
  let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
  let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
  let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩
  let v : W ⟶ Z := c ≫ k
  let V : Scheme.{u} := Spec Γ(X, U)
  let s : B ⟶ V := affineBlowupStructure (D.ideal U)
  let a : V ⟶ X := U.2.fromSpec
  have ht : k ≫ μ = s ≫ a :=
    DeJongAlterations.Geometry.BlowupGluing.chartInclusion_structure D ⟨U.1, U.2⟩
  have hf : (c ≫ s) ≫ a = v ≫ μ :=
    (@Category.assoc Scheme.{u} _ W B V X c s a).trans
      ((congrArg (fun f : B ⟶ X => c ≫ f) ht.symm).trans
        (@Category.assoc Scheme.{u} _ W B Z X c k μ).symm)
  have hb := liftedFormSection_isIso_on_originalFractionChart
    (R := R) (n := n) (X := X) j J d F hF hFJ U i hi hg0
  exact Eq.mp (congrArg (fun f : W ⟶ X => @IsIso W.Modules _ (Scheme.Modules.unitObj W)
    (Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj M) (D.comap f).toModules)
    (liftedFormSection (R := R) (n := n) (X := X) (Z := W) f j J d F hF hFJ)) hf) hb

/-- The same old lift on the entire actual glued global ideal blowup is a
basis after pullback by its actual original native fraction-chart inclusion.
The global structure triangle, open immersion and composite basis are derived. -/
theorem liftedFormSection_pullback_isIso_on_originalGlobalFractionChart
    {R : Type u} [hR : CommRing R] {n : ℕ} {X : Scheme.{u}}
    (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : MvPolynomial (Fin (n+1)) R) (hF : F.IsHomogeneous d) (hFJ : F ∈ J.toIdeal)
    (U : X.affineOpens) [hΓ : IsDomain Γ(X, U)] (i : Fin (n+1))
    (hi : U.1 ≤ j ⁻¹ᵁ nativeCoordinateOpen i) (hg0 : pulledForm j U i hi F ≠ 0) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let g : Γ(X, U) := pulledForm j U i hi F
    let hg : g ∈ D.ideal U := globalOriginalPulledForm_mem j J F hFJ U i hi
    let S := affineBlowupFractionChart (D.ideal U) g
    let B : Scheme.{u} := affineBlowup (D.ideal U)
    let W : Scheme.{u} := Spec (CommRingCat.of S)
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
    let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩
    let v : W ⟶ Z := c ≫ k
    let T : Z.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
      (D.comap μ).toModules
    @IsIso W.Modules _ (Scheme.Modules.unitObj W) ((Scheme.Modules.pullback v).obj T)
      (SchemeLineSectionEvaluation.pullbackSectionHom (M := T) v
        (liftedFormSection (R := R) (n := n) (X := X) (Z := Z) μ j J d F hF hFJ)) := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let g : Γ(X, U) := pulledForm j U i hi F
  let hg : g ∈ D.ideal U := globalOriginalPulledForm_mem j J F hFJ U i hi
  let S := affineBlowupFractionChart (D.ideal U) g
  let B : Scheme.{u} := affineBlowup (D.ideal U)
  let W : Scheme.{u} := Spec (CommRingCat.of S)
  let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
  let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U) g hg hg0
  let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D ⟨U.1, U.2⟩
  let v : W ⟶ Z := c ≫ k
  let hvOpen : @IsOpenImmersion W Z v :=
    @nativeGlobalFraction_isOpenImmersion X D U hΓ g hg hg0
  have hc := @globalCompositeLift_isIso_on_originalFractionChart R hR n X
    j J d F hF hFJ U hΓ i hi hg0
  exact @liftedFormSection_isIso_pullback_of_composite R hR n X Z W μ v hvOpen
    j J d F hF hFJ hc

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
