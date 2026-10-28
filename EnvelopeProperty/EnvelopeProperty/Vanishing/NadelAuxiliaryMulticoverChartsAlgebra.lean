import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover

/-! # Actual original common-frame coefficients and whole affine root algebras

The input frames are frames of the original finite list of line modules on one
original affine open. Every original degree and coefficient is retained. The
algebra follows the very same tail-first order as the original whole multicover.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
open NadelAuxiliaryMulticover Scheme.Modules CyclicSectionAlgebra

variable {X : Scheme.{u}} (U : X.Opens)

/-- An actual frame of an ORIGINAL auxiliary line on the SAME original open. -/
abbrev Frame (E : AuxiliarySection X) :=
  (Scheme.Modules.pullback U.ι).obj E.line ≅ unitObj U.toScheme

/-- Frames at EVERY original list position, including duplicate auxiliary data. -/
abbrev Frames (D : List (AuxiliarySection X)) := ∀ i : Fin D.length, Frame U (D.get i)

/-- The original native section coefficient in its actual original line frame. -/
def coefficient (E : AuxiliarySection X) (e : Frame U E) : Γ(U.toScheme, ⊤) :=
  CyclicSectionGlobalCoverGluing.coefficient E.line E.degree E.sectionHom ⟨U, e⟩

/-- The original actual affine-open coefficient ring. -/
abbrev baseRing : CommRingCat.{u} := Γ(U.toScheme, ⊤)

/-- The actual successive ORIGINAL root quotients, in the SAME tail-first order
as the original whole scheme fibre product. No degree is replaced or discarded. -/
def algebraObject : (D : List (AuxiliarySection X)) → Frames U D → Under (baseRing U)
  | [], _ => Under.mk (𝟙 _)
  | E :: D, e =>
      let B := algebraObject D (fun i => e i.succ)
      Under.mk (B.hom ≫ CommRingCat.ofHom
        (algebraMap B.right (RootRing E.degree (B.hom (coefficient U E (e 0))))))

/-- The WHOLE original common-frame algebra, retaining nilpotents and components. -/
abbrev ring (D : List (AuxiliarySection X)) (e : Frames U D) : CommRingCat.{u} :=
  (algebraObject U D e).right

/-- The SAME actual original coefficient-ring homomorphism. -/
def structureMap (D : List (AuxiliarySection X)) (e : Frames U D) : baseRing U ⟶ ring U D e :=
  (algebraObject U D e).hom

/-- The actual tail-stage inclusion in the whole monic quotient. -/
def tailMap (E : AuxiliarySection X) (D : List (AuxiliarySection X))
    (e : Frames U (E :: D)) : ring U D (fun i => e i.succ) ⟶ ring U (E :: D) e :=
  CommRingCat.ofHom (algebraMap _ _)

/-- The whole structure is literally the original tail structure followed by
its actual quotient inclusion. -/
theorem structureMap_cons (E : AuxiliarySection X) (D : List (AuxiliarySection X))
    (e : Frames U (E :: D)) :
    structureMap U (E :: D) e = structureMap U D (fun i => e i.succ) ≫ tailMap U E D e := rfl

/-- The ORIGINAL head quotient maps into the whole quotient by genuine native
AdjoinRoot base change, with the actual original coefficient map. -/
def headMap (E : AuxiliarySection X) (D : List (AuxiliarySection X))
    (e : Frames U (E :: D)) :
    CommRingCat.of (RootRing E.degree (coefficient U E (e 0))) ⟶ ring U (E :: D) e := by
  letI : Algebra (baseRing U) (ring U D (fun i => e i.succ)) :=
    (structureMap U D (fun i => e i.succ)).hom.toAlgebra
  exact CommRingCat.ofHom (CyclicSectionBaseChange.coefficientMap E.degree
    (coefficient U E (e 0)) ((structureMap U D (fun i => e i.succ)) (coefficient U E (e 0)))
    rfl).toRingHom

/-- The actual head and tail affine algebra square is cartesian after Spec. -/
theorem stage_isPullback (E : AuxiliarySection X) (D : List (AuxiliarySection X))
    (e : Frames U (E :: D)) :
    IsPullback (Spec.map (tailMap U E D e)) (Spec.map (headMap U E D e))
      (Spec.map (structureMap U D (fun i => e i.succ)))
      (CyclicSectionAffineCover.structureMap E.degree (coefficient U E (e 0))) := by
  let : Algebra (baseRing U) (ring U D (fun i => e i.succ)) :=
    (structureMap U D (fun i => e i.succ)).hom.toAlgebra
  exact CyclicSectionAffineCover.isPullback E.degree (coefficient U E (e 0))
    ((structureMap U D (fun i => e i.succ)) (coefficient U E (e 0))) rfl

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
