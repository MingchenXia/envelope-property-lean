import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalWholeComparisonGlobalLine
import EnvelopeProperty.AlgGeom.HironakaDeJongBlowupComparison
import EnvelopeProperty.AlgGeom.BlowupHomogeneousTautologicalOpenNaturality
import EnvelopeProperty.Alterations.Geometry.BlowupProjectiveEmbeddingProduct

/-! # The original forms product graph on the original all-affine Rees blowup -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Alterations Alterations.Geometry.ProjectiveIdeal
  Alterations.Geometry.BlowupProjectiveEmbedding
universe u
namespace EnvelopeProperty.BlowupHomogeneousTautologicalLine
attribute [local instance] MvPolynomial.gradedAlgebra homogeneousChartAlgebra

private theorem nativeProductFiniteForm_mem
    {R : Type u} [CommRing R] {n m : ℕ}
    (J : HomogeneousIdeal (ProjectiveGrading R n))
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (row : Fin (m+1)) : F row ∈ J.toIdeal := by
  rw [← hspan]
  exact Ideal.subset_span ⟨row, rfl⟩

private theorem sectionComparison_inverse_step {C : Type*} [Category C] {U A B N : C}
    (a : U ⟶ A) (b : U ⟶ B) (β : U ⟶ N) (K : B ≅ A) (e : B ≅ N)
    (ha : b ≫ K.hom = a) (hb : b ≫ e.hom = β) :
    a ≫ (K.symm ≪≫ e).hom = β := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← ha]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hb

private theorem sectionPullback_postcomp {B Z : Scheme.{u}} (c : B ⟶ Z)
    {M N : Z.Modules} (α : Scheme.Modules.unitObj Z ⟶ M) (φ : M ⟶ N) :
    SchemeLineSectionEvaluation.pullbackSectionHom c α ≫ (Scheme.Modules.pullback c).map φ =
      SchemeLineSectionEvaluation.pullbackSectionHom c (α ≫ φ) := by
  simp only [SchemeLineSectionEvaluation.pullbackSectionHom, Functor.map_comp, Category.assoc]

private theorem existsWholeComparisonPullback {Z W P : Scheme.{u}} {κ : Type*}
    (c : W ⟶ Z) (q : Z ⟶ P) {O : P.Modules} {T : Z.Modules}
    (e : (Scheme.Modules.pullback q).obj O ≅ T)
    {σ : κ → (Scheme.Modules.unitObj P ⟶ O)}
    {β : κ → (Scheme.Modules.unitObj Z ⟶ T)}
    (he : ∀ row, SchemeLineSectionEvaluation.pullbackSectionHom q (σ row) ≫ e.hom = β row) :
    ∃ Ec : (Scheme.Modules.pullback (c ≫ q)).obj O ≅ (Scheme.Modules.pullback c).obj T,
      ∀ row, SchemeLineSectionEvaluation.pullbackSectionHom (c ≫ q) (σ row) ≫ Ec.hom =
        SchemeLineSectionEvaluation.pullbackSectionHom c (β row) := by
  let K := (Scheme.Modules.pullbackComp c q).app O
  refine ⟨K.symm ≪≫ (Scheme.Modules.pullback c).mapIso e, ?_⟩
  intro row
  have hs : SchemeLineSectionEvaluation.pullbackSectionHom c
      (SchemeLineSectionEvaluation.pullbackSectionHom q (σ row)) ≫ K.hom =
      SchemeLineSectionEvaluation.pullbackSectionHom (c ≫ q) (σ row) := by
    have h := congrArg
      (fun t : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback q).obj O) ⟶
          (Scheme.Modules.pullback (c ≫ q)).obj O =>
        SchemeLineSectionEvaluation.pullbackSectionHom c
          (SchemeLineSectionEvaluation.pullbackSectionHom q (σ row)) ≫ t)
      (Iso.app_hom (Scheme.Modules.pullbackComp c q) O)
    exact h.trans (SchemeLineSectionEvaluation.pullbackSectionHom_comp c q (σ row))
  have hp := (sectionPullback_postcomp c
    (SchemeLineSectionEvaluation.pullbackSectionHom q (σ row)) e.hom).trans
      (congrArg (fun t => SchemeLineSectionEvaluation.pullbackSectionHom c t) (he row))
  have hp' : SchemeLineSectionEvaluation.pullbackSectionHom c
      (SchemeLineSectionEvaluation.pullbackSectionHom q (σ row)) ≫
      ((Scheme.Modules.pullback c).mapIso e).hom =
      SchemeLineSectionEvaluation.pullbackSectionHom c (β row) := by
    simpa only [Functor.mapIso_hom] using hp
  exact sectionComparison_inverse_step _ _ _ K ((Scheme.Modules.pullback c).mapIso e) hs hp' 

private theorem existsSectionComparisonPostcomp {C : Type*} [Category C]
    {U A N T : C} {κ : Type*} (e : A ≅ N) {ρ : N ⟶ T} [IsIso ρ]
    {a : κ → (U ⟶ A)} {β : κ → (U ⟶ N)} {γ : κ → (U ⟶ T)}
    (he : ∀ row, a row ≫ e.hom = β row)
    (hn : ∀ row, β row ≫ ρ = γ row) :
    ∃ E : A ≅ T, ∀ row, a row ≫ E.hom = γ row := by
  refine ⟨e ≪≫ asIso ρ, ?_⟩
  intro row
  change a row ≫ (e.hom ≫ ρ) = γ row
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ ρ) (he row)).trans (hn row))


private theorem existsOriginalComparisonAfterOpenFactor
    {R : Type u} [CommRing R] {n m : ℕ} {X Z W : Scheme.{u}}
    (μ : Z ⟶ X) (c : W ⟶ Z) [IsOpenImmersion c] (f : W ⟶ X) (hf : c ≫ μ = f)
    (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal)
    (q : Z ⟶ Alterations.projectiveSpace R m)
    (e : (Scheme.Modules.pullback q).obj
        (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1) ≅
      Scheme.Modules.tensorObj
        ((Scheme.Modules.pullback μ).obj ((Scheme.Modules.pullback j).obj
          (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)))
        (((GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j).comap μ).toModules)
    (he : ∀ row : Fin (m+1),
      SchemeLineSectionEvaluation.pullbackSectionHom q
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1
            (MvPolynomial.X row) (MvPolynomial.isHomogeneous_X R row)) ≫ e.hom =
        liftedFormSection μ j J d (F row) (hF row) (nativeProductFiniteForm_mem J F hspan row)) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let O := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
    ∃ E : (Scheme.Modules.pullback (c ≫ q)).obj O ≅
        Scheme.Modules.tensorObj ((Scheme.Modules.pullback f).obj M) (D.comap f).toModules,
      ∀ row : Fin (m+1),
        SchemeLineSectionEvaluation.pullbackSectionHom (c ≫ q)
            (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1
              (MvPolynomial.X row) (MvPolynomial.isHomogeneous_X R row)) ≫ E.hom =
          liftedFormSection f j J d (F row) (hF row) (nativeProductFiniteForm_mem J F hspan row) := by
  subst f
  obtain ⟨Ec, hEc⟩ := existsWholeComparisonPullback c q e he
  have hn := fun row : Fin (m+1) => liftedFormSection_openNaturality μ c j J d (F row) (hF row)
    (nativeProductFiniteForm_mem J F hspan row)
  exact existsSectionComparisonPostcomp (C := W.Modules) Ec hEc hn


private theorem existsFactorSectionComparison {B C P : Scheme.{u}} {κ : Type*}
    (g : B ⟶ C) (b : C ⟶ P) (q : B ⟶ P) (hq : g ≫ b = q)
    (O : P.Modules) (N : B.Modules) (σ : κ → (Scheme.Modules.unitObj P ⟶ O))
    (β : κ → (Scheme.Modules.unitObj B ⟶ N))
    (e : (Scheme.Modules.pullback q).obj O ≅ N)
    (he : ∀ row, SchemeLineSectionEvaluation.pullbackSectionHom q (σ row) ≫ e.hom = β row) :
    ∃ E : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj O) ≅ N,
      ∀ row, SchemeLineSectionEvaluation.pullbackSectionHom g
        (SchemeLineSectionEvaluation.pullbackSectionHom b (σ row)) ≫ E.hom = β row := by
  refine ⟨Scheme.Modules.frameFactorIso g b q hq O ≪≫ e, ?_⟩
  intro row
  change SchemeLineSectionEvaluation.pullbackSectionHom g
    (SchemeLineSectionEvaluation.pullbackSectionHom b (σ row)) ≫
    ((Scheme.Modules.frameFactorIso g b q hq O).hom ≫ e.hom) = β row
  rw [← Category.assoc, SchemeLineSectionFactorization.pullbackSectionHom_factor]
  exact he row

private theorem existsOriginalNativeProductWholeLineIso
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let μ : D.blowUp ⟶ X := D.blowUpπ
    let b : D.blowUp ⟶ pullback p (projectiveSpaceStructure R m) :=
      (HironakaDeJongBlowupComparison.globalIso D).inv ≫ formsProductMap p j J F hspan hF
    let O := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
    ∃ E : (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback (pullback.snd p (projectiveSpaceStructure R m))).obj O) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M) (D.comap μ).toModules,
      ∀ row : Fin (m+1),
        SchemeLineSectionEvaluation.pullbackSectionHom b
            (SchemeLineSectionEvaluation.pullbackSectionHom (pullback.snd p (projectiveSpaceStructure R m))
              (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1
                (MvPolynomial.X row) (MvPolynomial.isHomogeneous_X R row))) ≫ E.hom =
          liftedFormSection μ j J d (F row) (hF row) (nativeProductFiniteForm_mem J F hspan row) := by
  let M : X.Modules := (Scheme.Modules.pullback j).obj
    (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
  let D : X.IdealSheafData :=
    (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
  let μ := Alterations.Geometry.BlowupGluing.blowupStructure D
  let q := projectiveBlowupMapOfForms p j J F hspan hF
  let c := (HironakaDeJongBlowupComparison.globalIso D).inv
  let π : D.blowUp ⟶ X := D.blowUpπ
  let b := c ≫ formsProductMap p j J F hspan hF
  let O := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
  let T := Scheme.Modules.tensorObj ((Scheme.Modules.pullback π).obj M) (D.comap π).toModules
  have hf : c ≫ μ = π := by
    change (HironakaDeJongBlowupComparison.globalIso D).inv ≫
      Alterations.Geometry.BlowupGluing.blowupStructure D = D.blowUpπ
    rw [← HironakaDeJongBlowupComparison.globalIso_structure D, Iso.inv_hom_id_assoc]
  have hq : b ≫ pullback.snd p (projectiveSpaceStructure R m) = c ≫ q := by
    rw [Category.assoc, formsProductMap_snd]
  obtain ⟨E, hE⟩ := existsOriginalComparisonAfterOpenFactor μ c π hf j J d F hF hspan q
    (originalGlobalWholeLineIso p j J d F hF hspan)
    (fun row => originalGlobalWholeLineIso_section p j J d F hF hspan row)
  exact existsFactorSectionComparison b (pullback.snd p (projectiveSpaceStructure R m))
    (c ≫ q) hq O T
    (fun row => ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1
      (MvPolynomial.X row) (MvPolynomial.isHomogeneous_X R row))
    (fun row => liftedFormSection π j J d (F row) (hF row) (nativeProductFiniteForm_mem J F hspan row)) E hE

/-- Whole second-factor O(1) for the SAME original product graph under the actual whole Rees identity. -/
def originalNativeProductWholeLineIso
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) :
    let M : X.Modules := (Scheme.Modules.pullback j).obj
      (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let μ : D.blowUp ⟶ X := D.blowUpπ
    let b : D.blowUp ⟶ pullback p (projectiveSpaceStructure R m) :=
      (HironakaDeJongBlowupComparison.globalIso D).inv ≫ formsProductMap p j J F hspan hF
    let O := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
    (Scheme.Modules.pullback b).obj
        ((Scheme.Modules.pullback (pullback.snd p (projectiveSpaceStructure R m))).obj O) ≅
      Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M) (D.comap μ).toModules :=
  Classical.choose (existsOriginalNativeProductWholeLineIso p j J d F hF hspan)

/-- Every same prescribed section is retained on the original all-affine blowup. -/
theorem originalNativeProductWholeLineIso_section
    {R : Type u} [CommRing R] {n m : ℕ} {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Alterations.projectiveSpace R n)
    (J : HomogeneousIdeal (ProjectiveGrading R n)) (d : ℕ)
    (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R) (hF : ∀ row, (F row).IsHomogeneous d)
    (hspan : Ideal.span (Set.range F) = J.toIdeal) (row : Fin (m+1)) :
    let D : X.IdealSheafData :=
      (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
    let μ : D.blowUp ⟶ X := D.blowUpπ
    let b : D.blowUp ⟶ pullback p (projectiveSpaceStructure R m) :=
      (HironakaDeJongBlowupComparison.globalIso D).inv ≫ formsProductMap p j J F hspan hF
    SchemeLineSectionEvaluation.pullbackSectionHom b
        (SchemeLineSectionEvaluation.pullbackSectionHom (pullback.snd p (projectiveSpaceStructure R m))
          (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1
            (MvPolynomial.X row) (MvPolynomial.isHomogeneous_X R row))) ≫
      (originalNativeProductWholeLineIso p j J d F hF hspan).hom =
        liftedFormSection μ j J d (F row) (hF row) (nativeProductFiniteForm_mem J F hspan row) :=
  Classical.choose_spec (existsOriginalNativeProductWholeLineIso p j J d F hF hspan) row


/-- The original ideal's own same-degree product embedding retains its whole line and ALL rows. -/
theorem exists_originalNativeProductWholeLine
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] (D₀ : X.IdealSheafData)
    (p : X ⟶ Spec (CommRingCat.of R)) (j : X ⟶ Alterations.projectiveSpace R n)
    [IsClosedImmersion j] :
    ∃ (m d : ℕ) (F : Fin (m+1) → MvPolynomial (Fin (n+1)) R)
      (J : HomogeneousIdeal (ProjectiveGrading R n))
      (hF : ∀ row, (F row).IsHomogeneous d)
      (hspan : Ideal.span (Set.range F) = J.toIdeal),
      let D : X.IdealSheafData :=
        (GradedQuotient.quotientIdealSheaf (ProjectiveGrading R n) J).comap j
      D = D₀ ∧
      let M : X.Modules := (Scheme.Modules.pullback j).obj
        (coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (n+1)) d)
      let μ : D.blowUp ⟶ X := D.blowUpπ
      let b : D.blowUp ⟶ pullback p (projectiveSpaceStructure R m) :=
        (HironakaDeJongBlowupComparison.globalIso D).inv ≫ formsProductMap p j J F hspan hF
      let O := coordinateHyperplanePoleSheafPower (R := R) (0 : Fin (m+1)) 1
      IsClosedImmersion b ∧
      b ≫ pullback.fst p (projectiveSpaceStructure R m) = μ ∧
      b ≫ pullback.snd p (projectiveSpaceStructure R m) =
        (HironakaDeJongBlowupComparison.globalIso D).inv ≫
          projectiveBlowupMapOfForms p j J F hspan hF ∧
      ∃ E : (Scheme.Modules.pullback b).obj
          ((Scheme.Modules.pullback (pullback.snd p (projectiveSpaceStructure R m))).obj O) ≅
          Scheme.Modules.tensorObj ((Scheme.Modules.pullback μ).obj M) (D.comap μ).toModules,
        ∀ row : Fin (m+1),
          SchemeLineSectionEvaluation.pullbackSectionHom b
              (SchemeLineSectionEvaluation.pullbackSectionHom (pullback.snd p (projectiveSpaceStructure R m))
                (ProjectiveHomogeneousSections.sectionHom (R := R) (0 : Fin (m+1)) 1
                  (MvPolynomial.X row) (MvPolynomial.isHomogeneous_X R row))) ≫ E.hom =
            liftedFormSection μ j J d (F row) (hF row) (nativeProductFiniteForm_mem J F hspan row) := by
  obtain ⟨m, d, F, J, hF, hspan, hD⟩ := exists_fin_sameDegree_representation D₀ j
  refine ⟨m, d, F, J, hF, hspan, hD, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · rw [Category.assoc, formsProductMap_fst,
      ← HironakaDeJongBlowupComparison.globalIso_structure, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, formsProductMap_snd]
  · exact existsOriginalNativeProductWholeLineIso p j J d F hF hspan

end EnvelopeProperty.BlowupHomogeneousTautologicalLine
