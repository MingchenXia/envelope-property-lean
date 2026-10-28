import EnvelopeProperty.AlgGeom.CyclicSectionGlobalCoverRootSection

/-! # The whole raw multicover of actual original auxiliary line sections

The input is only a finite list of original lines, root degrees and sections.
Every stage is the literal native fibre product of the whole preceding cover
with the whole original cyclic cover. Disconnected components are retained.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover

open Scheme.Modules CanonicalGeometry

/-- Original auxiliary geometric data only; no covering conclusion,
normalization map or smoothness certificate is stored. -/
structure AuxiliarySection (X : Scheme.{u}) where
  line : X.Modules
  degree : ℕ
  sectionHom : unitObj X ⟶ bundleTensorPower line degree

variable {X : Scheme.{u}}

/-- The SAME original native global cyclic cover of an original auxiliary section. -/
abbrev factorCover (E : AuxiliarySection X) : Scheme.{u} :=
  CyclicSectionGlobalCoverGluing.rawCover E.line E.degree E.sectionHom

/-- The actual original cyclic projection, retaining the original line and section. -/
def factorProjection (E : AuxiliarySection X) : factorCover E ⟶ X :=
  CyclicSectionGlobalCoverGluing.rawProjection E.line E.degree E.sectionHom

/-- The literal finite product in schemes over the SAME original X.
No connected or generic component is selected at any stage. -/
def rawObject : List (AuxiliarySection X) → Over X
  | [] => Over.mk (𝟙 X)
  | E :: D => Over.mk
      (Limits.pullback.fst (rawObject D).hom (factorProjection E) ≫ (rawObject D).hom)

/-- The WHOLE actual finite auxiliary raw-covering scheme. -/
abbrev rawScheme (D : List (AuxiliarySection X)) : Scheme.{u} := (rawObject D).left

/-- The actual whole raw projection to the SAME original X. -/
def projection (D : List (AuxiliarySection X)) : rawScheme D ⟶ X := (rawObject D).hom

/-- The actual first pullback projection to the whole remaining multicover. -/
def tailProjection (E : AuxiliarySection X) (D : List (AuxiliarySection X)) :
    rawScheme (E :: D) ⟶ rawScheme D := Limits.pullback.fst _ _

/-- The actual second pullback projection to the SAME original head cyclic cover. -/
def headProjection (E : AuxiliarySection X) (D : List (AuxiliarySection X)) :
    rawScheme (E :: D) ⟶ factorCover E := Limits.pullback.snd _ _

/-- The original whole structure factors through the literal first projection. -/
theorem tailProjection_over (E : AuxiliarySection X) (D : List (AuxiliarySection X)) :
    tailProjection E D ≫ projection D = projection (E :: D) := rfl

/-- The original whole structure also factors through the literal second projection. -/
theorem headProjection_over (E : AuxiliarySection X) (D : List (AuxiliarySection X)) :
    headProjection E D ≫ factorProjection E = projection (E :: D) :=
  Limits.pullback.condition.symm

/-- Every recursive stage is the ACTUAL native scheme pullback square. -/
theorem stage_isPullback (E : AuxiliarySection X) (D : List (AuxiliarySection X)) :
    IsPullback (tailProjection E D) (headProjection E D) (projection D) (factorProjection E) :=
  IsPullback.of_hasPullback _ _

/-- Every ORIGINAL finite list position has its genuine actual cyclic-factor map.
Duplicate original data retain their distinct original list positions. -/
def factorMap : (D : List (AuxiliarySection X)) → (i : Fin D.length) →
    rawScheme D ⟶ factorCover (D.get i)
  | [], i => Fin.elim0 i
  | E :: D, i => Fin.cases (headProjection E D)
      (fun j => tailProjection E D ≫ factorMap D j) i

/-- The whole original factor triangle commutes for EVERY original list position. -/
theorem factorMap_over (D : List (AuxiliarySection X)) (i : Fin D.length) :
    factorMap D i ≫ factorProjection (D.get i) = projection D := by
  induction D with
  | nil => exact Fin.elim0 i
  | cons E D ih =>
      refine Fin.cases (headProjection_over E D) (fun j => ?_) i
      change (tailProjection E D ≫ factorMap D j) ≫ factorProjection (D.get j) = _
      rw [Category.assoc, ih, tailProjection_over]

/-- The whole finite product projection is finite, from the actual
original line-section cover maps and native scheme base change. -/
theorem projection_finite (D : List (AuxiliarySection X))
    (hL : ∀ E ∈ D, IsInvertible E.line) (hN : ∀ E ∈ D, 0 < E.degree) :
    IsFinite (projection D) := by
  induction D with
  | nil => change IsFinite (𝟙 X); infer_instance
  | cons E D ih =>
      let : IsFinite (factorProjection E) :=
        CyclicSectionGlobalCoverGluing.isFinite_rawProjection E.line E.degree E.sectionHom
          (hL E (List.mem_cons_self)) (hN E (List.mem_cons_self))
      let : IsFinite (projection D) := ih
        (fun e he => hL e (List.mem_cons_of_mem E he))
        (fun e he => hN e (List.mem_cons_of_mem E he))
      change IsFinite (Limits.pullback.fst (projection D) (factorProjection E) ≫ projection D)
      infer_instance

/-- The whole finite product projection is flat, from the actual
original line-section cover maps and native scheme base change. -/
theorem projection_flat (D : List (AuxiliarySection X))
    (hL : ∀ E ∈ D, IsInvertible E.line) (hN : ∀ E ∈ D, 0 < E.degree) :
    Flat (projection D) := by
  induction D with
  | nil => change Flat (𝟙 X); infer_instance
  | cons E D ih =>
      let : Flat (factorProjection E) :=
        CyclicSectionGlobalCoverGluing.flat_rawProjection E.line E.degree E.sectionHom
          (hL E (List.mem_cons_self)) (hN E (List.mem_cons_self))
      let : Flat (projection D) := ih
        (fun e he => hL e (List.mem_cons_of_mem E he))
        (fun e he => hN e (List.mem_cons_of_mem E he))
      change Flat (Limits.pullback.fst (projection D) (factorProjection E) ≫ projection D)
      infer_instance

/-- The WHOLE original finite product reaches every original base point;
no integral, connected or chosen generic component is required. -/
theorem projection_surjective (D : List (AuxiliarySection X))
    (hL : ∀ E ∈ D, IsInvertible E.line) (hN : ∀ E ∈ D, 0 < E.degree) :
    Surjective (projection D) := by
  induction D with
  | nil => change Surjective (𝟙 X); infer_instance
  | cons E D ih =>
      let : Surjective (factorProjection E) :=
        CyclicSectionGlobalCoverGluing.surjective_rawProjection E.line E.degree E.sectionHom
          (hL E (List.mem_cons_self)) (hN E (List.mem_cons_self))
      let : Surjective (projection D) := ih
        (fun e he => hL e (List.mem_cons_of_mem E he))
        (fun e he => hN e (List.mem_cons_of_mem E he))
      change Surjective (Limits.pullback.fst (projection D) (factorProjection E) ≫ projection D)
      infer_instance

/-- Genuine whole finiteness also supplies affineness of the same actual projection. -/
theorem projection_affine (D : List (AuxiliarySection X))
    (hL : ∀ E ∈ D, IsInvertible E.line) (hN : ∀ E ∈ D, 0 < E.degree) :
    IsAffineHom (projection D) := by
  let := projection_finite D hL hN
  infer_instance

/-- Every original base point has a point of this SAME whole multicover above it. -/
theorem exists_point_above (D : List (AuxiliarySection X))
    (hL : ∀ E ∈ D, IsInvertible E.line) (hN : ∀ E ∈ D, 0 < E.degree) (x : X) :
    ∃ y : rawScheme D, projection D y = x :=
  (projection_surjective D hL hN).surj x

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticover
