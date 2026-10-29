import EnvelopeProperty.AlgGeom.HironakaDeJongReesComparison
import Hironaka.Scheme.BlowUp.Glue.BlowUp
import EnvelopeProperty.Alterations.Geometry.BlowupGluing
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # The whole two native glued blowups over the same original scheme -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.HironakaDeJongBlowupComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


variable {X : Scheme.{u}} (D : X.IdealSheafData)

private def allOpen (U : X.AffineZariskiSite) : X.affineOpens := ⟨U.1, U.2⟩

private instance hirDiagram_locallyDirected :
    ((relativeGluingDataOf D (affineBlowUpNatTrans_equifibered D)).functor ⋙
      Scheme.forget).IsLocallyDirected := inferInstance

private instance hirDiagram_hasColimit :
    HasColimit (relativeGluingDataOf D (affineBlowUpNatTrans_equifibered D)).functor :=
  ⟨_, Scheme.IsLocallyDirected.isColimit _⟩

private instance djDiagram_locallyDirected :
    ((Alterations.Geometry.BlowupGluing.relativeGluingData D).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

private instance djDiagram_hasColimit : HasColimit (Alterations.Geometry.BlowupGluing.relativeGluingData D).functor :=
  ⟨_, Scheme.IsLocallyDirected.isColimit _⟩

private theorem hirChart_naturality {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    affineBlowUp.mapOfEq (Alterations.Geometry.BlowupGluing.coefficientMap h) (Alterations.Geometry.BlowupGluing.center_map D h) ≫
        Scheme.IdealSheafData.blowUp.ι D (allOpen V) =
      Scheme.IdealSheafData.blowUp.ι D (allOpen U) := by
  let k : allOpen U ⟶ allOpen V :=
    homOfLE ((Scheme.AffineZariskiSite.toOpensFunctor X).map h).le
  exact colimit.w (relativeGluingDataOf D (affineBlowUpNatTrans_equifibered D)).functor k

private def comparisonCocone : Cocone (Alterations.Geometry.BlowupGluing.relativeGluingData D).functor where
  pt := D.blowUp
  ι :=
    { app := fun U => (HironakaDeJongReesComparison.affineIso (D.ideal (allOpen U))).hom ≫
        Scheme.IdealSheafData.blowUp.ι D (allOpen U)
      naturality := by
        intro U V h
        change Alterations.affineBlowupMapTo _ _ (Alterations.Geometry.BlowupGluing.coefficientMap h)
          (Alterations.Geometry.BlowupGluing.center_map D h) ≫ ((HironakaDeJongReesComparison.affineIso _).hom ≫ _) = _ ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, HironakaDeJongReesComparison.affineIso_naturality,
          Category.assoc, hirChart_naturality D h]
        rfl }

/-- The map from the whole original small-site blowup to the whole original
all-affine-open blowup is induced by the identity on every original Rees algebra. -/
def comparison : Alterations.Geometry.BlowupGluing.blowup D ⟶ D.blowUp :=
  colimit.desc (Alterations.Geometry.BlowupGluing.relativeGluingData D).functor (comparisonCocone D)

/-- Every original affine blowup chart has its prescribed entire comparison map. -/
theorem chart_comparison (U : X.AffineZariskiSite) :
    Alterations.Geometry.BlowupGluing.chartInclusion D U ≫ comparison D =
      (HironakaDeJongReesComparison.affineIso (D.ideal (allOpen U))).hom ≫
        Scheme.IdealSheafData.blowUp.ι D (allOpen U) :=
  colimit.ι_desc (comparisonCocone D) U

/-- The global comparison retains the literal original projection to X. -/
theorem comparison_projection :
    comparison D ≫ D.blowUpπ = Alterations.Geometry.BlowupGluing.blowupStructure D := by
  apply (Alterations.Geometry.BlowupGluing.blowupCover D).hom_ext
  intro U
  change Alterations.Geometry.BlowupGluing.chartInclusion D U ≫ (comparison D ≫ D.blowUpπ) =
    Alterations.Geometry.BlowupGluing.chartInclusion D U ≫ Alterations.Geometry.BlowupGluing.blowupStructure D
  rw [← Category.assoc, chart_comparison, Category.assoc,
    Scheme.IdealSheafData.blowUp.ι_π, ← Category.assoc,
    ← Category.assoc, HironakaDeJongReesComparison.affineIso_structure, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, Alterations.Geometry.BlowupGluing.chartInclusion_structure]
  rfl

/-- Each ENTIRE original affine Rees comparison is the actual base change of
the global comparison over the corresponding original affine chart. -/
theorem isPullback_chart_comparison (U : X.AffineZariskiSite) :
    IsPullback (HironakaDeJongReesComparison.affineIso (D.ideal (allOpen U))).hom
      (Alterations.Geometry.BlowupGluing.chartInclusion D U)
      (Scheme.IdealSheafData.blowUp.ι D (allOpen U)) (comparison D) := by
  refine IsPullback.of_right
    (h₁₂ := affineBlowUp.π (D.ideal (allOpen U)) ≫ U.2.isoSpec.inv)
    (h₂₂ := D.blowUpπ) ?_ (chart_comparison D U).symm
    (Scheme.IdealSheafData.blowUp.isPullback_ι D (allOpen U))
  rw [← Category.assoc, HironakaDeJongReesComparison.affineIso_structure,
    comparison_projection]
  exact Alterations.Geometry.BlowupGluing.isPullback_chartOpen D U

/-- The actual global comparison is an isomorphism, as its base changes on
the whole original affine blowup cover are the original Rees identity isomorphisms. -/
instance comparison_isIso : IsIso (comparison D) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    (relativeGluingDataOf D (affineBlowUpNatTrans_equifibered D)).cover).mpr fun U => ?_
  change IsIso (pullback.snd (comparison D)
    (Scheme.IdealSheafData.blowUp.ι D (allOpen ⟨U.1, U.2⟩)))
  have h := (isPullback_chart_comparison D ⟨U.1, U.2⟩).flip
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- The WHOLE two original native blowups are isomorphic over their SAME
original scheme; this is not an identification of just their affine charts. -/
def globalIso : Alterations.Geometry.BlowupGluing.blowup D ≅ D.blowUp :=
  asIso (comparison D)

/-- The original whole-blowup isomorphism preserves the literal original projection. -/
theorem globalIso_structure :
    (globalIso D).hom ≫ D.blowUpπ =
      Alterations.Geometry.BlowupGluing.blowupStructure D :=
  comparison_projection D

end EnvelopeProperty.HironakaDeJongBlowupComparison
