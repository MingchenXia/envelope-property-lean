import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonGlobalFractionLine
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonGlobalCover
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonGlobalFractionLift
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonOpenCoverGluing

/-! # The same original whole tautological line on the entire native global ideal blowup -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry.ProjectiveIdeal
  DeJongAlterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem globalOriginalFiniteForm_mem
    {R : Type u} [CommRing R] {n m : ℕ}
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (row : Fin (m+1)) : F row ∈ J.toIdeal := by
  rw [← hspan]
  exact Ideal.subset_span ⟨row, rfl⟩

private theorem existsWholeComparisonOfSections
    {B : Scheme.{u}} {ι κ : Type*} {W : ι → Scheme.{u}} {M N : B.Modules}
    (c : ∀ a, W a ⟶ B) [∀ a, IsOpenImmersion (c a)]
    (hc : ∀ x : B, ∃ a, x ∈ (c a).opensRange)
    (e : ∀ a, (Scheme.Modules.pullback (c a)).obj M ≅ (Scheme.Modules.pullback (c a)).obj N)
    (α : κ → (Scheme.Modules.unitObj B ⟶ M))
    (β : κ → (Scheme.Modules.unitObj B ⟶ N)) (pivot : ι → κ)
    (hβ : ∀ a, IsIso (SchemeLineSectionEvaluation.pullbackSectionHom (c a) (β (pivot a))))
    (hpres : ∀ a j, SchemeLineSectionEvaluation.pullbackSectionHom (c a) (α j) ≫ (e a).hom =
      SchemeLineSectionEvaluation.pullbackSectionHom (c a) (β j)) :
    ∃ E : M ≅ N, ∀ row, α row ≫ E.hom = β row :=
  ⟨SchemeModuleOpenImages.glueOfOpenImmersionSections c hc e α β pivot hβ hpres,
    fun row => SchemeModuleOpenImages.glueOfOpenImmersionSections_section
      c hc e α β pivot hβ hpres row⟩

private theorem existsOriginalGlobalWholeLineIso
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
    let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    let O : (DeJongAlterations.projectiveSpace R m).Modules :=
      coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
    let T : Z.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
      (D.comap μ).toModules
    ∃ E : (Scheme.Modules.pullback q).obj O ≅ T,
      ∀ row : Fin (m+1),
        SchemeLineSectionEvaluation.pullbackSectionHom q
            (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1
              (MvPolynomial.X row) (MvPolynomial.isHomogeneous_X R row)) ≫ E.hom =
          liftedFormSection μ j J d (F row) (hF row)
            (globalOriginalFiniteForm_mem J F hspan row) := by
  let M : X.Modules := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
  let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
  let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
    projectiveBlowupMapOfForms p j J F hspan hF
  let O : (DeJongAlterations.projectiveSpace R m).Modules :=
    coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
  let T : Z.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
    (D.comap μ).toModules
  let A := {U : SubordinateAffineSite j // Nonempty U.1.1}
  let U₀ (a : A) : X.affineOpens := ⟨a.1.1.1, a.1.1.2⟩
  let _ (a : A) : IsDomain Γ(X, U₀ a) := by
    let : Nonempty a.1.1.1 := a.2
    exact IsIntegral.component_integral a.1.1.1
  let g (a : A) : Fin (m+1) → Γ(X, U₀ a) := fun row =>
    pulledForm j (U₀ a) (subordinateCoordinate j a.1) (subordinateCoordinate_le j a.1) (F row)
  let hgs (a : A) : Ideal.span (Set.range (g a)) = D.ideal (U₀ a) :=
    pulledForm_span_fin j (U₀ a) J F hspan
      (subordinateCoordinate j a.1) (subordinateCoordinate_le j a.1)
  let ι := Σ a : A, {row : Fin (m+1) // g a row ≠ 0}
  let W (a : ι) : Scheme.{u} :=
    Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal (U₀ a.1)) (g a.1 a.2.val)))
  let f (a : ι) : W a ⟶ Z :=
    affineBlowupChartInclusion (D.ideal (U₀ a.1)) (g a.1 a.2.val)
      (generator_mem (D.ideal (U₀ a.1)) (g a.1) (hgs a.1) a.2.val) a.2.property ≫
      DeJongAlterations.Geometry.BlowupGluing.chartInclusion D a.1.1.1
  let hfOpen : ∀ a : ι, IsOpenImmersion (f a) := by
    intro a
    let hc : IsOpenImmersion (affineBlowupChartInclusion (D.ideal (U₀ a.1)) (g a.1 a.2.val)
        (generator_mem (D.ideal (U₀ a.1)) (g a.1) (hgs a.1) a.2.val) a.2.property) :=
      affineBlowupChartInclusion_isOpenImmersion (D.ideal (U₀ a.1)) (g a.1 a.2.val)
        (generator_mem (D.ideal (U₀ a.1)) (g a.1) (hgs a.1) a.2.val) a.2.property
    let hk : IsOpenImmersion (DeJongAlterations.Geometry.BlowupGluing.chartInclusion D a.1.1.1) :=
      DeJongAlterations.Geometry.BlowupGluing.chartInclusion_isOpenImmersion D a.1.1.1
    let := hc
    let := hk
    infer_instance
  let := hfOpen
  let α : Fin (m+1) → (Scheme.Modules.unitObj Z ⟶ (Scheme.Modules.pullback q).obj O) := fun row =>
    SchemeLineSectionEvaluation.pullbackSectionHom q
      (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X row)
        (MvPolynomial.isHomogeneous_X R row))
  let β : Fin (m+1) → (Scheme.Modules.unitObj Z ⟶ T) := fun row =>
    liftedFormSection μ j J d (F row) (hF row) (globalOriginalFiniteForm_mem J F hspan row)
  let e : ∀ a : ι, (Scheme.Modules.pullback (f a)).obj ((Scheme.Modules.pullback q).obj O) ≅
      (Scheme.Modules.pullback (f a)).obj T := fun a =>
    originalGlobalFractionWholeLineIso p j J d F hF hspan a.1.1 a.2.val a.2.property
  let C := specifiedOriginalGlobalFractionOpenCover j J F hspan
  have hc : ∀ z : Z, ∃ a : ι, z ∈ (f a).opensRange :=
    fun z => ⟨C.idx z, C.covers z⟩
  have hb := fun (a : ι) =>
    liftedFormSection_pullback_isIso_on_originalGlobalFractionChart j J d (F a.2.val) (hF a.2.val)
      (globalOriginalFiniteForm_mem J F hspan a.2.val) (U₀ a.1)
      (subordinateCoordinate j a.1.1) (subordinateCoordinate_le j a.1.1) a.2.property
  have hpres := fun (a : ι) (row : Fin (m+1)) =>
    originalGlobalFractionWholeLineIso_section p j J d F hF hspan a.1.1 a.2.val a.2.property row
  exact existsWholeComparisonOfSections
    (B := Z) (ι := ι) (κ := Fin (m+1)) (W := W)
    (M := (Scheme.Modules.pullback q).obj O) (N := T) f hc e α β
    (fun a => a.2.val) hb hpres


/-- The same original global comparison, chosen together with preservation of all original sections. -/
def originalGlobalWholeLineIso
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
    let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    let O : (DeJongAlterations.projectiveSpace R m).Modules :=
      coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
    let T : Z.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
      (D.comap μ).toModules
    (Scheme.Modules.pullback q).obj O ≅ T :=
  Classical.choose (existsOriginalGlobalWholeLineIso p j J d F hF hspan)

/-- Every same prescribed coordinate is sent to its original old lift on the entire native blowup. -/
theorem originalGlobalWholeLineIso_section
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ DeJongAlterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (row : Fin (m+1)) :
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let Z : Scheme.{u} := DeJongAlterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := DeJongAlterations.Geometry.BlowupGluing.blowupStructure D
    let q : Z ⟶ DeJongAlterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    SchemeLineSectionEvaluation.pullbackSectionHom q
        (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X row)
          (MvPolynomial.isHomogeneous_X R row)) ≫
      (originalGlobalWholeLineIso p j J d F hF hspan).hom =
      liftedFormSection μ j J d (F row) (hF row) (globalOriginalFiniteForm_mem J F hspan row) :=
  Classical.choose_spec (existsOriginalGlobalWholeLineIso p j J d F hF hspan) row

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
