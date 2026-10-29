import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionNaturality

/-! # Whole original Hom sections under actual source-line isomorphisms

The comparison is the genuine adjunction mate of tensoring the original
line isomorphism. Its section identity is derived, never supplied.
-/

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
noncomputable section
universe u v w z

namespace EnvelopeProperty.Vanishing.NadelPrincipalizationHomSection

set_option backward.isDefEq.respectTransparency false

private theorem mate_homEquiv
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (A₁ : L₁ ⊣ R₁) (A₂ : L₂ ⊣ R₂)
    (e : L₂ ≅ L₁) (M : C) (N : D) (φ : L₁.obj M ⟶ N) :
    A₂.homEquiv M N (e.hom.app M ≫ φ) =
      A₁.homEquiv M N φ ≫ ((conjugateIsoEquiv A₁ A₂ e).hom.app N) := by
  have hu := unit_conjugateEquiv A₁ A₂ e.hom M
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
    Category.assoc, ← (conjugateEquiv A₁ A₂ e.hom).naturality φ,
    ← Category.assoc, ← Adjunction.homEquiv_unit]
  rfl

private noncomputable instance moduleMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

variable {X : Scheme.{u}} (A : X.Modules) (hA : Scheme.Modules.IsInvertible A)
    (A' : X.Modules) (hA' : Scheme.Modules.IsInvertible A') (e : A ≅ A')

private def leftLineIso :
    (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A' hA').functor ≅
      (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).functor :=
  (tensoringRight X.Modules).mapIso e.symm

private def rightLineIso :
    (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).inverse ≅
      (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A' hA').inverse :=
  conjugateIsoEquiv
    (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).toAdjunction
    (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A' hA').toAdjunction
    (leftLineIso A hA A' hA' e)

/-- An actual original line isomorphism gives the genuine whole
source-changing Hom-object isomorphism through the native tensor adjunction. -/
def lineHomIso (B : X.Modules) :
    Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A) ≅
      Scheme.Modules.tensorObj B (Scheme.Modules.dualObj A') :=
  (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).symm ≪≫
    (rightLineIso A hA A' hA' e).app B ≪≫
    ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A')

private theorem equiv_formula (B : X.Modules) (φ : A ⟶ B) :
    SchemeInvertibleHomSection.equiv A hA B φ =
      (ModularCurves.monoidalUnitObjIso X).inv ≫
        (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).toAdjunction.homEquiv _ _
          ((λ_ A).hom ≫ φ) ≫
        (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).hom := rfl

private theorem lineHomIso_hom (B : X.Modules) :
    (lineHomIso A hA A' hA' e B).hom =
      (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A)).inv ≫
        ((rightLineIso A hA A' hA' e).hom.app B) ≫
        (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A')).hom := rfl

private theorem rightLineIso_homEquiv (B : X.Modules) (φ : A ⟶ B) :
    (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A' hA').toAdjunction.homEquiv _ _
        ((λ_ A').hom ≫ e.inv ≫ φ) =
      (SchemeInvertibleTensorEquivalence.invertibleTensorEquivalence A hA).toAdjunction.homEquiv _ _
          ((λ_ A).hom ≫ φ) ≫ (rightLineIso A hA A' hA' e).hom.app B := by
  dsimp only [rightLineIso]
  have hl : (leftLineIso A hA A' hA' e).hom.app (𝟙_ X.Modules) ≫ (λ_ A).hom ≫ φ =
      (λ_ A').hom ≫ e.inv ≫ φ := by
    change (𝟙_ X.Modules ◁ e.inv) ≫ (λ_ A).hom ≫ φ = _
    rw [leftUnitor_naturality_assoc]
  rw [← hl]
  exact mate_homEquiv _ _ (leftLineIso A hA A' hA' e) (𝟙_ X.Modules) B ((λ_ A).hom ≫ φ)

/-- The comparison carries the SAME whole original map to precomposition
by the SAME original line isomorphism, without a frame or section certificate. -/
theorem lineHomIso_section (B : X.Modules) (φ : A ⟶ B) :
    SchemeInvertibleHomSection.equiv A hA B φ ≫ (lineHomIso A hA A' hA' e B).hom =
      SchemeInvertibleHomSection.equiv A' hA' B (e.inv ≫ φ) := by
  rw [equiv_formula, equiv_formula, lineHomIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply (cancel_epi (ModularCurves.monoidalUnitObjIso X).inv).mpr
  rw [← Category.assoc]
  apply (cancel_mono (ModularCurves.monoidalTensorObjIso B (Scheme.Modules.dualObj A')).hom).mpr
  exact (rightLineIso_homEquiv A hA A' hA' e B φ).symm

/-- A commutative square of ENTIRE actual maps transports their SAME
Hom sections through the genuine source-line and target isomorphisms. -/
theorem lineHomIso_square_section (B B' : X.Modules) (eB : B ≅ B')
    (φ : A ⟶ B) (φ' : A' ⟶ B') (hφ : φ ≫ eB.hom = e.hom ≫ φ') :
    SchemeInvertibleHomSection.equiv A hA B φ ≫ (lineHomIso A hA A' hA' e B).hom ≫
        (Scheme.Modules.tensorObjCongr eB (Iso.refl (Scheme.Modules.dualObj A'))).hom =
      SchemeInvertibleHomSection.equiv A' hA' B' φ' := by
  rw [← Category.assoc, lineHomIso_section]
  change SchemeInvertibleHomSection.equiv A' hA' B (e.inv ≫ φ) ≫
    SchemeTensorObjMorphisms.tensorObjMap eB.hom (𝟙 (Scheme.Modules.dualObj A')) = _
  rw [← SchemeInvertibleHomSection.equiv_comp]
  have hh : (e.inv ≫ φ) ≫ eB.hom = φ' := by
    rw [Category.assoc, hφ, Iso.inv_hom_id_assoc]
  rw [hh]

end EnvelopeProperty.Vanishing.NadelPrincipalizationHomSection
