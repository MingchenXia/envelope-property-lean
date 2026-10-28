import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonCoordinateSections
import DeJongAlterations.Geometry.BlowupProjectiveEmbedding

/-! # The original global Rees coordinates on their actual prescribed fraction spectra -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
  DeJongAlterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem originalGlobalFractionMap_eq_affine
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal)
    (U : SubordinateAffineSite j) [IsDomain Γ(X, U.1.1)] (pivot : Fin (m+1))
    (hp : pulledForm j ⟨U.1.1, U.1.2⟩ (subordinateCoordinate j U)
      (subordinateCoordinate_le j U) (F pivot) ≠ 0) :
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
    let g : Fin (m+1) → Γ(X, U₀) := fun row =>
      pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
    let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
      pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
    let B : Scheme.{u} := affineBlowup (D.ideal U₀)
    let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
      (generator_mem (D.ideal U₀) g hgs pivot) hp
    let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D U.1
    let v : W ⟶ Z := c ≫ k
    let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    let q' : B ⟶ DeJongAlterations.projectiveSpace R m :=
      affineProjectiveMap (affineBaseCoefficients p U₀) (D.ideal U₀) g hgs
    v ≫ q = c ≫ q' := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
  let g : Fin (m+1) → Γ(X, U₀) := fun row =>
    pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
  let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
    pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
  let B : Scheme.{u} := affineBlowup (D.ideal U₀)
  let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
  let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
    (generator_mem (D.ideal U₀) g hgs pivot) hp
  let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D U.1
  let v : W ⟶ Z := c ≫ k
  let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
    projectiveBlowupMapOfForms p j J F hspan hF
  let q' : B ⟶ DeJongAlterations.projectiveSpace R m :=
    affineProjectiveMap (affineBaseCoefficients p U₀) (D.ideal U₀) g hgs
  change v ≫ q = c ≫ q'
  have hq : k ≫ q = q' := projectiveBlowupMapOfForms_restrict p j J F hspan hF U
  exact (Category.assoc c k q).trans (congrArg (fun f : B ⟶ DeJongAlterations.projectiveSpace R m =>
    c ≫ f) hq)

/-- The same original global projective pivot is a basis on its actual native fraction spectrum. -/
theorem originalGlobalFractionCoordinateSection_isIso
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal)
    (U : SubordinateAffineSite j) [IsDomain Γ(X, U.1.1)] (pivot : Fin (m+1))
    (hp : pulledForm j ⟨U.1.1, U.1.2⟩ (subordinateCoordinate j U)
      (subordinateCoordinate_le j U) (F pivot) ≠ 0) :
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
    let g : Fin (m+1) → Γ(X, U₀) := fun row =>
      pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
    let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
      pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
    let B : Scheme.{u} := affineBlowup (D.ideal U₀)
    let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
      (generator_mem (D.ideal U₀) g hgs pivot) hp
    let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D U.1
    let v : W ⟶ Z := c ≫ k
    let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    IsIso (SchemeLineSectionEvaluation.pullbackSectionHom (v ≫ q)
      (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X pivot)
        (MvPolynomial.isHomogeneous_X R pivot))) := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
  let g : Fin (m+1) → Γ(X, U₀) := fun row =>
    pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
  let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
    pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
  let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
  have ht := originalGlobalFractionMap_eq_affine p j J d F hF hspan U pivot hp
  have hb := originalFractionCoordinateSection_isIso (affineBaseCoefficients p U₀)
    (D.ideal U₀) g hgs pivot hp 0
  exact Eq.mp (congrArg (fun f : W ⟶ DeJongAlterations.projectiveSpace R m =>
    IsIso (SchemeLineSectionEvaluation.pullbackSectionHom f
      (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X pivot)
        (MvPolynomial.isHomogeneous_X R pivot)))) ht.symm) hb

/-- The original global coordinates retain all the same original native generator ratios. -/
theorem originalGlobalFractionCoordinateSection_ratio
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal)
    (U : SubordinateAffineSite j) [IsDomain Γ(X, U.1.1)] (pivot : Fin (m+1))
    (hp : pulledForm j ⟨U.1.1, U.1.2⟩ (subordinateCoordinate j U)
      (subordinateCoordinate_le j U) (F pivot) ≠ 0) (row : Fin (m+1)) :
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
    let g : Fin (m+1) → Γ(X, U₀) := fun row =>
      pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
    let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
      pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
    let B : Scheme.{u} := affineBlowup (D.ideal U₀)
    let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
      (generator_mem (D.ideal U₀) g hgs pivot) hp
    let k : B ⟶ Z := DeJongAlterations.Geometry.BlowupGluing.chartInclusion D U.1
    let v : W ⟶ Z := c ≫ k
    let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    SchemeLineSectionEvaluation.pullbackSectionHom (v ≫ q)
      (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X row)
        (MvPolynomial.isHomogeneous_X R row)) =
      ModularCurves.unitEndomorphismOfTopSection
        ((Scheme.ΓSpecIso (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))).inv.hom
          (originalFractionRatioTuple (D.ideal U₀) g hgs pivot row)) ≫
        SchemeLineSectionEvaluation.pullbackSectionHom (v ≫ q)
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X pivot)
        (MvPolynomial.isHomogeneous_X R pivot)) := by
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
  let g : Fin (m+1) → Γ(X, U₀) := fun row =>
    pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
  let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
    pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
  let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
  let r : Γ(W, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))).inv.hom
      (originalFractionRatioTuple (D.ideal U₀) g hgs pivot row)
  have ht := originalGlobalFractionMap_eq_affine p j J d F hF hspan U pivot hp
  have hb := originalFractionCoordinateSection_ratio (affineBaseCoefficients p U₀)
    (D.ideal U₀) g hgs pivot hp 0 row
  exact Eq.mp (congrArg (fun f : W ⟶ DeJongAlterations.projectiveSpace R m =>
    SchemeLineSectionEvaluation.pullbackSectionHom f
      (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X row)
        (MvPolynomial.isHomogeneous_X R row)) = ModularCurves.unitEndomorphismOfTopSection r ≫
      SchemeLineSectionEvaluation.pullbackSectionHom f
        (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X pivot)
        (MvPolynomial.isHomogeneous_X R pivot))) ht.symm) hb

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
