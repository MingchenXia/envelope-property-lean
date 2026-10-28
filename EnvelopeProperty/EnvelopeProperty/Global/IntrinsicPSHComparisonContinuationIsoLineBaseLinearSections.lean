import EnvelopeProperty.Global.IntrinsicPSHComparisonContinuationIsoLineTopSectionScalars

/-! Actual structure-induced base scalars on the SAME H0 comparison.
Route: owned `iso-line-base-linear-sections-route.tex`. -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveGlobalSections
open Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual constants are the genuine Spec/global-sections map followed by the actual structure map. -/
def structureBaseConstants {k : Type u} [CommRing k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) : k →+* Γ(W, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom

/-- Actual H0 restricts its ORIGINAL global-function action along actual structural constants. -/
abbrev structureH0BaseModule {k : Type u} [CommRing k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (L : W.Modules) : Module k Γ(L, ⊤) :=
  Module.compHom Γ(L, ⊤) (structureBaseConstants p)

/-- A genuine whole over-base scheme triangle supplies the entire actual base-constant equation. -/
theorem structureBaseConstants_mapOverBase {k : Type u} [CommRing k] {Z Y : Scheme.{u}}
    (f : Z ⟶ Y) (p : Z ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    (h : f ≫ q = p) (c : k) :
    f.appTop (structureBaseConstants q c) = structureBaseConstants p c := by
  have ht : q.appTop ≫ f.appTop = p.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using congrArg (fun g => g.appTop) h
  exact ConcreteCategory.congr_hom
    (congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ a) ht) c

/-- The SAME original H0 composite is linear for independently actual structure-induced actions. -/
def isoLineBaseSectionsLinearEquiv {k : Type u} [CommRing k] {Z Y : Scheme.{u}}
    (e : Z ≅ Y) (p : Z ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    (h : e.hom ≫ q = p) (L : Y.Modules) (P : Z.Modules)
    (a : (pullback e.hom).obj L ≅ P) :
    letI := structureH0BaseModule q L
    letI := structureH0BaseModule p P
    Γ(L, ⊤) ≃ₗ[k] Γ(P, ⊤) := by
  letI := structureH0BaseModule q L
  letI := structureH0BaseModule p P
  let H := (isoPullbackTopSections e L).symm ≪≫ asIso (a.hom.app ⊤)
  let E := H.addCommGroupIsoToAddEquiv
  exact {
    toFun := E
    invFun := E.symm
    left_inv := E.left_inv
    right_inv := E.right_inv
    map_add' := E.map_add
    map_smul' := fun c s => by
      change H.hom (structureBaseConstants q c • s) = structureBaseConstants p c • H.hom s
      exact (isoLineTopSections_global_smul e L P a (structureBaseConstants q c) s).trans
        (congrArg (fun r : Γ(Z, ⊤) => r • H.hom s)
          (structureBaseConstants_mapOverBase e.hom p q h c)) }

end EnvelopeProperty.ClosedProjectiveGlobalSections

#check @EnvelopeProperty.ClosedProjectiveGlobalSections.structureBaseConstants
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.structureBaseConstants
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.structureH0BaseModule
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.structureH0BaseModule
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.structureBaseConstants_mapOverBase
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.structureBaseConstants_mapOverBase
#check @EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineBaseSectionsLinearEquiv
#print axioms EnvelopeProperty.ClosedProjectiveGlobalSections.isoLineBaseSectionsLinearEquiv
