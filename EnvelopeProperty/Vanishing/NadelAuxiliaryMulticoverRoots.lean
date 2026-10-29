import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover

/-! # Every original auxiliary line section has its actual root on the WHOLE multicover

Original native tautological roots are pulled through actual factor maps.
Whole power identities use the native pullback and power comparison
coherences, retaining each original line, degree and section.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover

open Scheme.Modules CanonicalGeometry
open SchemeLineSectionEvaluation SchemeGlobalSectionTensorPowerNorms
open BundleTensorPowerPullback
open CyclicSectionGlobalCoverRootSectionLocal CyclicSectionGlobalCoverRootSectionPowers
open CyclicSectionGlobalCoverRootSectionPowerCoherence
open CyclicSectionGlobalCoverRootSection

variable {X : Scheme.{u}}

/-- The actual original native root pulled through an actual structural
factor triangle, into the SAME directly pulled original line. -/
def transportedRoot (E : AuxiliarySection X) {T : Scheme.{u}}
    (t : T ⟶ factorCover E) (π : T ⟶ X) (ht : t ≫ factorProjection E = π) :
    unitObj T ⟶ (Scheme.Modules.pullback π).obj E.line :=
  factorSection E.line t (factorProjection E) π ht
    (tautologicalRoot E.line E.degree E.sectionHom)

/-- Native section-power and factor coherence prove the WHOLE original
root equation after the actual factor transport. -/
theorem transportedRoot_power (E : AuxiliarySection X) {T : Scheme.{u}}
    (t : T ⟶ factorCover E) (π : T ⟶ X) (ht : t ≫ factorProjection E = π) :
    powerSectionHom (transportedRoot E t π ht) E.degree =
      pullbackSectionHom π E.sectionHom ≫ (pullbackIso π E.line E.degree).hom := by
  let τ : unitObj (factorCover E) ⟶
      (Scheme.Modules.pullback (factorProjection E)).obj E.line :=
    tautologicalRoot E.line E.degree E.sectionHom
  have hτ : powerSectionHom τ E.degree =
      pullbackSectionHom (factorProjection E) E.sectionHom ≫
        (pullbackIso (factorProjection E) E.line E.degree).hom :=
    tautologicalRoot_power E.line E.degree E.sectionHom
  change powerSectionHom (pullbackSectionHom t τ ≫
    (frameFactorIso t (factorProjection E) π ht E.line).hom) E.degree = _
  rw [← powerSectionHom_iso, ← pullback_powerSectionHom, hτ]
  have hc := congrArg Iso.hom (pullbackIso_factor E.line t (factorProjection E) π ht E.degree)
  change (Scheme.Modules.pullback t).map
      (pullbackIso (factorProjection E) E.line E.degree).hom ≫
      (pullbackIso t ((Scheme.Modules.pullback (factorProjection E)).obj E.line) E.degree).hom ≫
      (powerIso (frameFactorIso t (factorProjection E) π ht E.line) E.degree).hom =
    (frameFactorIso t (factorProjection E) π ht (bundleTensorPower E.line E.degree)).hom ≫
      (pullbackIso π E.line E.degree).hom at hc
  simp only [pullbackSectionHom, Functor.map_comp, Category.assoc]
  rw [hc]
  have hs := factorSection_pullback (bundleTensorPower E.line E.degree)
    t (factorProjection E) π ht E.sectionHom
  exact (by
    simpa only [factorSection, pullbackSectionHom, Functor.map_comp, Category.assoc] using
      congrArg (fun q => q ≫ (pullbackIso π E.line E.degree).hom) hs)

/-- The SAME original line at an original finite-list position, pulled
through the WHOLE multicover projection to the SAME original X. -/
def line (D : List (AuxiliarySection X)) (i : Fin D.length) : (rawScheme D).Modules :=
  (Scheme.Modules.pullback (projection D)).obj (D.get i).line

/-- Original invertibility is retained on that same actual whole pulled line. -/
theorem line_isInvertible (D : List (AuxiliarySection X)) (i : Fin D.length)
    (hL : ∀ E ∈ D, IsInvertible E.line) : IsInvertible (line D i) :=
  (hL (D.get i) (List.get_mem _ _)).pullback (projection D)

/-- The original section, pulled to the native tensor power of that
SAME original line on the WHOLE multicover. -/
def sectionPower (D : List (AuxiliarySection X)) (i : Fin D.length) :
    unitObj (rawScheme D) ⟶ bundleTensorPower (line D i) (D.get i).degree :=
  pullbackSectionHom (projection D) (D.get i).sectionHom ≫
    (pullbackIso (projection D) (D.get i).line (D.get i).degree).hom

/-- EVERY original list position has its actual global line-valued
root, built from its native root through its genuine original factor map. -/
def root (D : List (AuxiliarySection X)) (i : Fin D.length) :
    unitObj (rawScheme D) ⟶ line D i :=
  transportedRoot (D.get i) (factorMap D i) (projection D) (factorMap_over D i)

/-- The original native power of EVERY actual global root equals the
SAME original section pulled to the WHOLE covering scheme. -/
theorem root_power (D : List (AuxiliarySection X)) (i : Fin D.length) :
    powerSectionHom (root D i) (D.get i).degree = sectionPower D i :=
  transportedRoot_power (D.get i) (factorMap D i) (projection D) (factorMap_over D i)

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover
