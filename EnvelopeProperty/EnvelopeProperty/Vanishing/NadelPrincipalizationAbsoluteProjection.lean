import EnvelopeProperty.Vanishing.NadelPrincipalizationCanonicalContraction
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import EnvelopeProperty.Char0.RoundedCanonicalQuotient

/-! # Actual absolute canonical projection formula and entire rounded inclusion -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationAbsoluteProjection
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (L : X.Modules) (hL : IsInvertible L)

/-- Genuine native line projection formula on the SAME explicit whole sheaf tensors. -/
def tensorProjectionIso (M : Y.Modules) :
    Scheme.Modules.tensorObj ((pushforward g).obj M) L ≅
      (pushforward g).obj (Scheme.Modules.tensorObj M ((pullback g).obj L)) :=
  (ModularCurves.monoidalTensorObjIso ((pushforward g).obj M) L).symm ≪≫
    SchemeLineProjectionFormula.lineProjectionFormulaObj g L hL M ≪≫
      (pushforward g).mapIso (ModularCurves.monoidalTensorObjIso M ((pullback g).obj L))

/-- The same whole projection formula retains EVERY actual original module map. -/
theorem tensorProjectionIso_naturality {M N : Y.Modules} (φ : M ⟶ N) :
    SchemeTensorObjMorphisms.tensorObjMap ((pushforward g).map φ) (𝟙 L) ≫
      (tensorProjectionIso g L hL N).hom =
    (tensorProjectionIso g L hL M).hom ≫ (pushforward g).map
      (SchemeTensorObjMorphisms.tensorObjMap φ (𝟙 ((pullback g).obj L))) := by
  have ht : (ModularCurves.monoidalTensorObjIso M ((pullback g).obj L)).hom ≫
      SchemeTensorObjMorphisms.tensorObjMap φ (𝟙 ((pullback g).obj L)) =
      (φ ▷ (pullback g).obj L) ≫
        (ModularCurves.monoidalTensorObjIso N ((pullback g).obj L)).hom := by
    apply (cancel_mono (ModularCurves.monoidalTensorObjIso N ((pullback g).obj L)).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [SchemeTensorObjMorphisms.tensorObjMap_monoidal]
    simp only [Iso.hom_inv_id_assoc, tensorHom_id]
  dsimp only [tensorProjectionIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc (SchemeTensorObjMorphisms.tensorObjMap ((pushforward g).map φ) (𝟙 L))
      (ModularCurves.monoidalTensorObjIso ((pushforward g).obj N) L).inv,
    SchemeTensorObjMorphisms.tensorObjMap_monoidal, tensorHom_id]
  have hn := (SchemeLineProjectionFormula.lineProjectionFormula g L hL).hom.naturality φ
  change ((pushforward g).map φ ▷ L) ≫
      (SchemeLineProjectionFormula.lineProjectionFormulaObj g L hL N).hom =
      (SchemeLineProjectionFormula.lineProjectionFormulaObj g L hL M).hom ≫
        (pushforward g).map (φ ▷ (pullback g).obj L) at hn
  simp only [Category.assoc]
  rw [← (pushforward g).map_comp, ht, (pushforward g).map_comp]
  simpa only [Category.assoc] using congrArg
    (fun z => (ModularCurves.monoidalTensorObjIso ((pushforward g).obj M) L).inv ≫ z ≫
      (pushforward g).map (ModularCurves.monoidalTensorObjIso N ((pullback g).obj L)).hom) hn

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f]

/-- Actual whole relative canonical tensor contracts to original absolute canonical. -/
def relativeAbsoluteIso :
    Scheme.Modules.tensorObj (relative f g n) ((pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)) ≅
      CanonicalGeometry.canonicalLineSheaf (g ≫ f) n :=
  NadelPrincipalizationCanonicalContraction.contractionIso _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g) _

/-- The actual contraction recovers the ENTIRE ORIGINAL exterior differential. -/
theorem relativeAbsoluteIso_differential :
    SchemeTensorObjMorphisms.tensorObjMap (differentialSection f g n)
        (𝟙 ((pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n))) ≫
      (relativeAbsoluteIso g f n).hom =
    (NadelPrincipalizationCanonicalContraction.unitTensorIso
      ((pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n))).hom ≫
      CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n :=
  NadelPrincipalizationCanonicalContraction.contractionIso_section _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g) _ _

variable (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The original absolute rounded inclusion, with its entire actual ideal map. -/
def absoluteInclusion : absolute (g ≫ f) n J hJ q ⟶ CanonicalGeometry.canonicalLineSheaf (g ≫ f) n :=
  SchemeTensorObjMorphisms.tensorObjIdealMap (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n)
    (idealModule J hJ q) (idealModuleInclusion J hJ q)

/-- SAME original whole rounded module, with the actual dual canceled by native evaluation. -/
def roundedAbsoluteIso :
    Scheme.Modules.tensorObj (relativeRounded f g n J hJ q)
        ((pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)) ≅ absolute (g ≫ f) n J hJ q :=
  NadelPrincipalizationCanonicalContraction.roundedContractionIso _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g) _ (idealModule J hJ q)

/-- The ENTIRE original rounded inclusion is retained by the actual contraction. -/
theorem roundedAbsoluteIso_inclusion :
    (roundedAbsoluteIso g f n J hJ q).hom ≫ absoluteInclusion g f n J hJ q =
      SchemeTensorObjMorphisms.tensorObjMap (relativeRoundedInclusion f g n J hJ q)
        (𝟙 ((pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n))) ≫
        (relativeAbsoluteIso g f n).hom :=
  NadelPrincipalizationCanonicalContraction.roundedContractionIso_inclusion _
    ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g) _
    (idealModule J hJ q) (idealModuleInclusion J hJ q)

/-- Genuine line projection and native evaluation give the original absolute rounded pushforward. -/
def pushforwardAbsoluteIso :
    Scheme.Modules.tensorObj ((pushforward g).obj (relativeRounded f g n J hJ q))
      (CanonicalGeometry.canonicalLineSheaf f n) ≅
        (pushforward g).obj (absolute (g ≫ f) n J hJ q) :=
  tensorProjectionIso g _ (CanonicalGeometry.canonicalLineSheaf_isInvertible f n) _ ≪≫
    (pushforward g).mapIso (roundedAbsoluteIso g f n J hJ q)

/-- SAME whole relative pushforward contracts to the SAME original absolute canonical pushforward. -/
def pushforwardRelativeIso :
    Scheme.Modules.tensorObj ((pushforward g).obj (relative f g n))
      (CanonicalGeometry.canonicalLineSheaf f n) ≅
        (pushforward g).obj (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n) :=
  tensorProjectionIso g _ (CanonicalGeometry.canonicalLineSheaf_isInvertible f n) _ ≪≫
    (pushforward g).mapIso (relativeAbsoluteIso g f n)

/-- Whole projection/contraction retains the ENTIRE original pushed rounded inclusion. -/
theorem pushforwardAbsoluteIso_inclusion :
    (pushforwardAbsoluteIso g f n J hJ q).hom ≫ (pushforward g).map (absoluteInclusion g f n J hJ q) =
      SchemeTensorObjMorphisms.tensorObjMap
        ((pushforward g).map (relativeRoundedInclusion f g n J hJ q))
        (𝟙 (CanonicalGeometry.canonicalLineSheaf f n)) ≫ (pushforwardRelativeIso g f n).hom := by
  dsimp only [pushforwardAbsoluteIso, pushforwardRelativeIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← (pushforward g).map_comp, roundedAbsoluteIso_inclusion, (pushforward g).map_comp]
  rw [← Category.assoc, ← tensorProjectionIso_naturality]
  simp only [Category.assoc]

end EnvelopeProperty.Vanishing.NadelPrincipalizationAbsoluteProjection
