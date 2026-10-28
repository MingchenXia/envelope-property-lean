import EnvelopeProperty.Berkovich.SchemeLinePullbackSections
import EnvelopeProperty.AlgGeom.SchemeLineFramePullbackCoherence

/-! # Actual generic-fibre sections under the original residue-field map -/
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X Y : Scheme.{u}}

/-- The actual whole residue-fibre module pullback square, using the SAME
original residue-field map and the literal native generic morphisms. -/
def residueModulePullbackIso (g : X ⟶ Y) (x : X) (M : Y.Modules) :
    (Scheme.Modules.pullback (Spec.map (g.residueFieldMap x))).obj
      ((Scheme.Modules.pullback (Y.fromSpecResidueField (g x))).obj M) ≅
    (Scheme.Modules.pullback (X.fromSpecResidueField x)).obj ((Scheme.Modules.pullback g).obj M) :=
  Scheme.Modules.frameFactorIso (Spec.map (g.residueFieldMap x))
    (Y.fromSpecResidueField (g x)) (X.fromSpecResidueField x ≫ g)
    (g.SpecMap_residueFieldMap_fromSpecResidueField x) M ≪≫
      ((Scheme.Modules.pullbackComp (X.fromSpecResidueField x) g).app M).symm

/-- The actual native residue-module comparison and genuine factor transport
retain EVERY whole original residue-fibre frame. -/
theorem residueModulePullbackIso_frame (g : X ⟶ Y) (x : X) (M : Y.Modules)
    (e : (Scheme.Modules.pullback (Y.fromSpecResidueField (g x))).obj M ≅
      Scheme.Modules.unitObj (Spec (CommRingCat.of (Y.residueField (g x))))) :
    residueModulePullbackIso g x M ≪≫
      ((Scheme.Modules.pullbackComp (X.fromSpecResidueField x) g).app M ≪≫
        Scheme.Modules.frameViaFactor (Spec.map (g.residueFieldMap x))
          (Y.fromSpecResidueField (g x)) (X.fromSpecResidueField x ≫ g)
          (g.SpecMap_residueFieldMap_fromSpecResidueField x) e) =
    (Scheme.Modules.pullback (Spec.map (g.residueFieldMap x))).mapIso e ≪≫
      Scheme.Modules.pullbackUnitIso (Spec.map (g.residueFieldMap x)) :=
  Scheme.Modules.frameFactorIso_pairing (Spec.map (g.residueFieldMap x))
    (Y.fromSpecResidueField (g x)) (X.fromSpecResidueField x ≫ g)
    (g.SpecMap_residueFieldMap_fromSpecResidueField x)
    (M := M) (N := (Scheme.Modules.pullback (X.fromSpecResidueField x)).obj
      ((Scheme.Modules.pullback g).obj M))
    ((Scheme.Modules.pullbackComp (X.fromSpecResidueField x) g).app M) e

/-- The ACTUAL pulled-back arbitrary original residue-fibre section morphism;
it need not extend to a global section on the original target model. -/
def pullbackResidueSectionHom (g : X ⟶ Y) (x : X) {M : Y.Modules}
    (β : Scheme.Modules.unitObj (Spec (CommRingCat.of (Y.residueField (g x)))) ⟶
      (Scheme.Modules.pullback (Y.fromSpecResidueField (g x))).obj M) :
    Scheme.Modules.unitObj (Spec (CommRingCat.of (X.residueField x))) ⟶
      (Scheme.Modules.pullback (X.fromSpecResidueField x)).obj ((Scheme.Modules.pullback g).obj M) :=
  SchemeLineSectionEvaluation.pullbackSectionHom (Spec.map (g.residueFieldMap x)) β ≫
    (residueModulePullbackIso g x M).hom

/-- Every original generic-fibre section has its actual residue-field pullback
in the SAME original pulled model line, with no extension premise. -/
def pullbackResidueSection (g : X ⟶ Y) (x : X) {M : Y.Modules}
    (s : Γ((Scheme.Modules.pullback (Y.fromSpecResidueField (g x))).obj M, ⊤)) :
    Γ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj ((Scheme.Modules.pullback g).obj M), ⊤) :=
  SchemeLineSectionEvaluation.sectionAtOne
    (pullbackResidueSectionHom g x (Scheme.Modules.topSectionHom _ s))

end EnvelopeProperty.Berkovich.SchemeValuedPoint
