import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverChartsAlgebra

/-! # Genuine original single-section affine charts

Only the actual original frame and affineness of its original open are used.
The map to the original global cyclic cover and its cartesian square are proved
from the native original gluing theorem and the literal scalar equation.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
open NadelAuxiliaryMulticover CyclicSectionAlgebra
variable {X : Scheme.{u}} (U : X.Opens) [IsAffine U.toScheme]

private instance scalarToRootSpec_isIso (E : AuxiliarySection X) (e : Frame U E) :
    IsIso (CyclicSectionGlobalCover.toRootSpec U.toScheme E.degree (coefficient U E e)) := by
  change IsIso (Limits.pullback.snd U.toScheme.toSpecΓ
    (CyclicSectionAffineCover.structureMap E.degree (coefficient U E e)))
  infer_instance

/-- The actual scalar equation on the SAME original affine open is genuinely
isomorphic to the WHOLE original root-quotient spectrum. -/
def scalarRootIso (E : AuxiliarySection X) (e : Frame U E) :
    CyclicSectionGlobalCover.equation U.toScheme E.degree (coefficient U E e) ≅
      Spec (.of (RootRing E.degree (coefficient U E e))) :=
  asIso (CyclicSectionGlobalCover.toRootSpec U.toScheme E.degree (coefficient U E e))

/-- The actual head affine projection back to the SAME original open. -/
def singleBase (E : AuxiliarySection X) (e : Frame U E) :
    Spec (.of (RootRing E.degree (coefficient U E e))) ⟶ U.toScheme :=
  CyclicSectionAffineCover.structureMap E.degree (coefficient U E e) ≫ U.toScheme.isoSpec.inv

/-- The literal native scalar projection, with its actual affine identification. -/
theorem scalarRootIso_singleBase (E : AuxiliarySection X) (e : Frame U E) :
    (scalarRootIso U E e).hom ≫ singleBase U E e =
      CyclicSectionGlobalCover.projection U.toScheme E.degree (coefficient U E e) := by
  have h := (CyclicSectionGlobalCover.equation_isPullback U.toScheme E.degree
    (coefficient U E e)).w
  have hh := congrArg (fun k => k ≫ U.toScheme.isoSpec.inv) h
  change _ ≫ U.toScheme.isoSpec.hom ≫ U.toScheme.isoSpec.inv = _ at hh
  simpa only [singleBase, scalarRootIso, asIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] using hh.symm

/-- The genuine affine chart map to the SAME original global cyclic factor. -/
def singleMap (E : AuxiliarySection X) (e : Frame U E) :
    Spec (.of (RootRing E.degree (coefficient U E e))) ⟶ factorCover E :=
  (scalarRootIso U E e).inv ≫
    CyclicSectionGlobalCoverGluing.chartι E.line E.degree E.sectionHom ⟨U, e⟩

/-- The chart square with the actual original global factor is cartesian. -/
theorem single_isPullback (E : AuxiliarySection X) (e : Frame U E) :
    IsPullback (singleMap U E e) (singleBase U E e) (factorProjection E) U.ι := by
  exact (CyclicSectionGlobalCoverGluing.chart_isPullback E.line E.degree E.sectionHom
    ⟨U, e⟩).of_iso (scalarRootIso U E e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change _ ≫ 𝟙 _ = (scalarRootIso U E e).hom ≫ (scalarRootIso U E e).inv ≫ _
        exact (Category.comp_id (CyclicSectionGlobalCoverGluing.chartι E.line E.degree
          E.sectionHom ⟨U, e⟩)).trans
          (Iso.hom_inv_id_assoc (scalarRootIso U E e) _).symm)
      (by
        change CyclicSectionGlobalCover.projection U.toScheme E.degree (coefficient U E e) ≫
          𝟙 _ = (scalarRootIso U E e).hom ≫ singleBase U E e
        exact (Category.comp_id _).trans (scalarRootIso_singleBase U E e).symm)
      (by simp [factorProjection]) (by simp)

/-- The original head factor triangle, with no chart matching input. -/
theorem singleMap_over (E : AuxiliarySection X) (e : Frame U E) :
    singleMap U E e ≫ factorProjection E = singleBase U E e ≫ U.ι :=
  (single_isPullback U E e).w

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
