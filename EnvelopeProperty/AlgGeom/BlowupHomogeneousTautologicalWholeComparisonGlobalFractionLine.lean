import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonGlobalCoordinateSections
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonGlobalFractionRelations
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonGlobalFractionLift

/-! # The same original global whole line from its actual original pivot bases and ratios -/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Alterations Alterations.Geometry.ProjectiveIdeal
  Alterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private def globalUnitBasisComparison {C : Type u} [Category C] {A M N : C}
    (α : A ⟶ M) (β : A ⟶ N) (hα : IsIso α) (hβ : IsIso β) : M ≅ N := by
  let := hα
  let := hβ
  exact (asIso α).symm ≪≫ asIso β

private theorem globalUnitBasisComparison_section {C : Type u} [Category C] {A M N : C}
    (α : A ⟶ M) (β : A ⟶ N) (hα : IsIso α) (hβ : IsIso β)
    (a : A ⟶ A) (s : A ⟶ M) (t : A ⟶ N) (hs : s = a ≫ α) (ht : t = a ≫ β) :
    s ≫ (globalUnitBasisComparison α β hα hβ).hom = t := by
  let := hα
  let := hβ
  change s ≫ ((asIso α).inv ≫ β) = t
  rw [hs, ht]
  change (a ≫ (asIso α).hom) ≫ ((asIso α).inv ≫ β) = a ≫ β
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private def globalPulledBasisIso {W Z P : Scheme.{u}} (v : W ⟶ Z) (q : Z ⟶ P)
    (O : P.Modules) (N : W.Modules) (σp : Scheme.Modules.unitObj P ⟶ O)
    (βp : Scheme.Modules.unitObj W ⟶ N)
    (hα : IsIso (SchemeLineSectionEvaluation.pullbackSectionHom (v ≫ q) σp)) (hβ : IsIso βp) :
    (Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback q).obj O) ≅ N :=
  ((Scheme.Modules.pullbackComp v q).app O) ≪≫ globalUnitBasisComparison _ βp hα hβ

private theorem globalPulledBasisIso_section {W Z P : Scheme.{u}} (v : W ⟶ Z) (q : Z ⟶ P)
    (O : P.Modules) (N : W.Modules) (σp : Scheme.Modules.unitObj P ⟶ O)
    (βp : Scheme.Modules.unitObj W ⟶ N)
    (hα : IsIso (SchemeLineSectionEvaluation.pullbackSectionHom (v ≫ q) σp)) (hβ : IsIso βp)
    (σ : Scheme.Modules.unitObj P ⟶ O) (β : Scheme.Modules.unitObj W ⟶ N)
    (a : Scheme.Modules.unitObj W ⟶ Scheme.Modules.unitObj W)
    (hs : SchemeLineSectionEvaluation.pullbackSectionHom (v ≫ q) σ =
      a ≫ SchemeLineSectionEvaluation.pullbackSectionHom (v ≫ q) σp)
    (ht : β = a ≫ βp) :
    SchemeLineSectionEvaluation.pullbackSectionHom v
        (SchemeLineSectionEvaluation.pullbackSectionHom q σ) ≫
      (globalPulledBasisIso v q O N σp βp hα hβ).hom = β := by
  let C := (Scheme.Modules.pullbackComp v q).app O
  let e := globalUnitBasisComparison _ βp hα hβ
  have hb := globalUnitBasisComparison_section _ βp hα hβ a _ β hs ht
  have hn := SchemeLineSectionEvaluation.pullbackSectionHom_comp v q σ
  change SchemeLineSectionEvaluation.pullbackSectionHom v
    (SchemeLineSectionEvaluation.pullbackSectionHom q σ) ≫ (C.hom ≫ e.hom) = β
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun w => w ≫ e.hom) hn).trans hb)

private theorem globalFractionOriginalForm_mem
    {R : Type u} [CommRing R] {n m : ℕ}
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (row : Fin (m+1)) : F row ∈ J.toIdeal := by
  rw [← hspan]
  exact Ideal.subset_span ⟨row, rfl⟩

/-- The entire actual native global fraction spectrum carries the same original whole line comparison. -/
def originalGlobalFractionWholeLineIso
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal)
    (U : SubordinateAffineSite j) [IsDomain Γ(X, U.1.1)] (pivot : Fin (m+1))
    (hp : pulledForm j ⟨U.1.1, U.1.2⟩ (subordinateCoordinate j U)
      (subordinateCoordinate_le j U) (F pivot) ≠ 0) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
    let g : Fin (m+1) → Γ(X, U₀) := fun row =>
      pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
    let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
      pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
    let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
    let B : Scheme.{u} := affineBlowup (D.ideal U₀)
    let Z : Scheme.{u} := Alterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := Alterations.Geometry.BlowupGluing.blowupStructure D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
      (generator_mem (D.ideal U₀) g hgs pivot) hp
    let k : B ⟶ Z := Alterations.Geometry.BlowupGluing.chartInclusion D U.1
    let v : W ⟶ Z := c ≫ k
    let q : Z ⟶ Alterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    let O : (Alterations.projectiveSpace R m).Modules :=
      coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
    let T : Z.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
      (D.comap μ).toModules
    (Scheme.Modules.pullback v).obj ((Scheme.Modules.pullback q).obj O) ≅
      (Scheme.Modules.pullback v).obj T := by
  let M : X.Modules := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
  let g : Fin (m+1) → Γ(X, U₀) := fun row =>
    pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
  let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
    pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
  let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
  let B : Scheme.{u} := affineBlowup (D.ideal U₀)
  let Z : Scheme.{u} := Alterations.Geometry.BlowupGluing.blowup D
  let μ : Z ⟶ X := Alterations.Geometry.BlowupGluing.blowupStructure D
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
    (generator_mem (D.ideal U₀) g hgs pivot) hp
  let k : B ⟶ Z := Alterations.Geometry.BlowupGluing.chartInclusion D U.1
  let v : W ⟶ Z := c ≫ k
  let q : Z ⟶ Alterations.projectiveSpace R m :=
    projectiveBlowupMapOfForms p j J F hspan hF
  let O : (Alterations.projectiveSpace R m).Modules :=
    coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
  let T : Z.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
    (D.comap μ).toModules
  let β (row : Fin (m+1)) := SchemeLineSectionEvaluation.pullbackSectionHom v
    (liftedFormSection μ j J d (F row) (hF row) (globalFractionOriginalForm_mem J F hspan row))
  have hα := originalGlobalFractionCoordinateSection_isIso p j J d F hF hspan U pivot hp
  have hβ := liftedFormSection_pullback_isIso_on_originalGlobalFractionChart j J d
    (F pivot) (hF pivot) (globalFractionOriginalForm_mem J F hspan pivot) U₀
    (subordinateCoordinate j U) (subordinateCoordinate_le j U) hp
  exact globalPulledBasisIso v q O ((Scheme.Modules.pullback v).obj T)
    (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X pivot)
      (MvPolynomial.isHomogeneous_X R pivot)) (β pivot) hα hβ

/-- Every same prescribed original section is preserved by the actual global fraction comparison. -/
theorem originalGlobalFractionWholeLineIso_section
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Alterations.projectiveSpace R n)
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
    let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
    let B : Scheme.{u} := affineBlowup (D.ideal U₀)
    let Z : Scheme.{u} := Alterations.Geometry.BlowupGluing.blowup D
    let μ : Z ⟶ X := Alterations.Geometry.BlowupGluing.blowupStructure D
    let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
      (generator_mem (D.ideal U₀) g hgs pivot) hp
    let k : B ⟶ Z := Alterations.Geometry.BlowupGluing.chartInclusion D U.1
    let v : W ⟶ Z := c ≫ k
    let q : Z ⟶ Alterations.projectiveSpace R m :=
      projectiveBlowupMapOfForms p j J F hspan hF
    SchemeLineSectionEvaluation.pullbackSectionHom v
        (SchemeLineSectionEvaluation.pullbackSectionHom q
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X row)
            (MvPolynomial.isHomogeneous_X R row))) ≫
      (originalGlobalFractionWholeLineIso p j J d F hF hspan U pivot hp).hom =
      SchemeLineSectionEvaluation.pullbackSectionHom v
        (liftedFormSection μ j J d (F row) (hF row) (globalFractionOriginalForm_mem J F hspan row)) := by
  let M : X.Modules := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let U₀ : X.affineOpens := ⟨U.1.1, U.1.2⟩
  let g : Fin (m+1) → Γ(X, U₀) := fun row =>
    pulledForm j U₀ (subordinateCoordinate j U) (subordinateCoordinate_le j U) (F row)
  let hgs : Ideal.span (Set.range g) = D.ideal U₀ :=
    pulledForm_span_fin j U₀ J F hspan (subordinateCoordinate j U) (subordinateCoordinate_le j U)
  let W : Scheme.{u} := Spec (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))
  let B : Scheme.{u} := affineBlowup (D.ideal U₀)
  let Z : Scheme.{u} := Alterations.Geometry.BlowupGluing.blowup D
  let μ : Z ⟶ X := Alterations.Geometry.BlowupGluing.blowupStructure D
  let c : W ⟶ B := affineBlowupChartInclusion (D.ideal U₀) (g pivot)
    (generator_mem (D.ideal U₀) g hgs pivot) hp
  let k : B ⟶ Z := Alterations.Geometry.BlowupGluing.chartInclusion D U.1
  let v : W ⟶ Z := c ≫ k
  let q : Z ⟶ Alterations.projectiveSpace R m :=
    projectiveBlowupMapOfForms p j J F hspan hF
  let O : (Alterations.projectiveSpace R m).Modules :=
    coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
  let T : Z.Modules := Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M)
    (D.comap μ).toModules
  let β (row : Fin (m+1)) := SchemeLineSectionEvaluation.pullbackSectionHom v
    (liftedFormSection μ j J d (F row) (hF row) (globalFractionOriginalForm_mem J F hspan row))
  have hα := originalGlobalFractionCoordinateSection_isIso p j J d F hF hspan U pivot hp
  have hβ := liftedFormSection_pullback_isIso_on_originalGlobalFractionChart j J d
    (F pivot) (hF pivot) (globalFractionOriginalForm_mem J F hspan pivot) U₀
    (subordinateCoordinate j U) (subordinateCoordinate_le j U) hp
  have hcoord := originalGlobalFractionCoordinateSection_ratio p j J d F hF hspan U pivot hp row
  have hform := liftedFormSection_pullback_ratio_on_originalGlobalFractionChart j J d
    (F row) (F pivot) (hF row) (hF pivot) (globalFractionOriginalForm_mem J F hspan row)
    (globalFractionOriginalForm_mem J F hspan pivot) U₀
    (subordinateCoordinate j U) (subordinateCoordinate_le j U) hp
  exact globalPulledBasisIso_section v q O ((Scheme.Modules.pullback v).obj T)
    (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X pivot)
      (MvPolynomial.isHomogeneous_X R pivot)) (β pivot) hα hβ
    (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1 (MvPolynomial.X row)
      (MvPolynomial.isHomogeneous_X R row)) (β row)
    (ModularCurves.unitEndomorphismOfTopSection
      ((Scheme.ΓSpecIso (CommRingCat.of (affineBlowupFractionChart (D.ideal U₀) (g pivot)))).inv.hom
        (originalFractionRatioTuple (D.ideal U₀) g hgs pivot row))) hcoord hform

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
