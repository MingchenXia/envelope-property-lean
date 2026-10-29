import EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveTuple
import EnvelopeProperty.Vanishing.NadelNefBigPaddedGenerators
import EnvelopeProperty.Vanishing.NadelNefBigTargetAtlas
import EnvelopeProperty.AlgGeom.HironakaDeJongReesComparison
import EnvelopeProperty.Alterations.Geometry.BlowupProjectiveEmbeddingAffine
import EnvelopeProperty.Alterations.Geometry.ProjectiveIdealCoordinateIdeal

noncomputable section
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveClosed
open NadelNefBigExceptionalGenerators NadelNefBigExceptionalFrames NadelNefBigExceptionalProjectiveCharts
open NadelNefBigExceptionalProjectiveTuple NadelNefBigTargetAtlas
open Alterations.Geometry.BlowupProjectiveEmbedding
variable {A : Type u} [CommRing A] (I : Ideal A) {ι : Type u} [Fintype ι]
    (g : ι → I) (hspan : Ideal.span (Set.range (fun i => (g i : A))) = I)

include hspan in
theorem projection_isProper : IsProper (affineBlowUp.π I) := by
  let a := SchemeGeneratedLineCoefficients.paddedCoefficients (fun i => (g i : A))
  let ha := NadelNefBigPaddedGenerators.span_padded I g hspan
  let e := affineGeneratorEmbedding I a ha
  let : IsClosedImmersion e := affineGeneratorEmbedding_isClosedImmersion I a ha
  have hp : IsProper (e ≫ Alterations.projectiveSpaceStructure A (Fintype.card ι)) := inferInstance
  have hπ : e ≫ Alterations.projectiveSpaceStructure A (Fintype.card ι) =
      Alterations.affineBlowupStructure I := affineGeneratorEmbedding_structure I a ha
  let : IsProper (Alterations.affineBlowupStructure I) := hπ ▸ hp
  have hc : (HironakaDeJongReesComparison.affineIso I).inv ≫
      Alterations.affineBlowupStructure I = affineBlowUp.π I := by
    rw [← HironakaDeJongReesComparison.affineIso_structure, Iso.inv_hom_id_assoc]
  exact hc ▸ (inferInstance : IsProper ((HironakaDeJongReesComparison.affineIso I).inv ≫
    Alterations.affineBlowupStructure I))

theorem projectiveMap_structure :
    projectiveMap I g hspan ≫ Alterations.projectiveSpaceStructure A (Fintype.card ι) =
      affineBlowUp.π I := by
  let G := generatingSections I g hspan
  let : Fintype G.I := (inferInstance : Fintype ι)
  exact GeneratedLineProjectiveMap.projectiveMap_structure (affineBlowUp.π I)
    (affineBlowUp.isInvertible_exceptionalIdeal I).isInvertibleModule_toModules G

theorem isImmersion : IsImmersion (projectiveMap I g hspan) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun j : Fin (Fintype.card ι + 1) => MvPolynomial.coordinateOpen (R := A) j)
    Alterations.Geometry.ProjectiveIdeal.iSup_nativeCoordinateOpen_eq_top
  intro j
  induction j using Fin.cases with
  | zero =>
    exact restrict_isImmersion_of_empty_preimage (projectiveMap I g hspan) _ (preimage_zero I g hspan)
  | succ j =>
    let i := (Fintype.equivFin ι).symm j
    have hi : ((Fintype.equivFin ι) i).succ = j.succ := congrArg Fin.succ ((Fintype.equivFin ι).apply_symm_apply j)
    let : IsImmersion (affineBlowUp.chart I (g i) ≫ projectiveMap I g hspan) := chart_isImmersion I g hspan i
    have hpre := preimage_coordinate I g hspan i
    rw [hi] at hpre
    exact restrict_isImmersion_of_exact_chart (projectiveMap I g hspan) (affineBlowUp.chart I (g i)) _ hpre

theorem isProper : IsProper (projectiveMap I g hspan) := by
  let : IsProper (affineBlowUp.π I) := projection_isProper I g hspan
  let : IsProper (projectiveMap I g hspan ≫
      Alterations.projectiveSpaceStructure A (Fintype.card ι)) :=
    (projectiveMap_structure I g hspan).symm ▸ inferInstance
  exact IsProper.of_comp (projectiveMap I g hspan)
    (Alterations.projectiveSpaceStructure A (Fintype.card ι))

theorem isClosedImmersion : IsClosedImmersion (projectiveMap I g hspan) := by
  let := isImmersion I g hspan
  let := isProper I g hspan
  exact IsClosedImmersion.of_isPreimmersion _ (projectiveMap I g hspan).isClosedMap.isClosed_range
end EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveClosed
