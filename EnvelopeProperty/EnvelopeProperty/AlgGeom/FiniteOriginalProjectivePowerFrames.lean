import EnvelopeProperty.AlgGeom.SchemePullbackSubopenFrames
import EnvelopeProperty.AlgGeom.SchemeTensorSectionHoms

/-! # Actual finite whole original tensor lines, frames and section scalars -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FiniteOriginalProjectivePowerFrames
open SchemeLineSectionEvaluation SchemeTensorSectionHoms
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f
variable {X : Scheme.{u}}

/-- The actual original finite tensor line, retaining every original factor. -/
def tensorLine : {r : ℕ} → (Fin (r+1) → X.Modules) → X.Modules
  | 0,M => M 0
  | r+1,M => M 0 ⊗ tensorLine (fun j : Fin (r+1) => M j.succ)

/-- The actual whole original pure tensor section of all original factors. -/
def tensorSection : {r : ℕ} → (M : Fin (r+1) → X.Modules) →
    (∀ j,unitObj X ⟶ M j) → (unitObj X ⟶ tensorLine M)
  | 0,_,a => a 0
  | r+1,M,a => tensorSectionHom (a 0)
      (tensorSection (fun j : Fin (r+1) => M j.succ) (fun j => a j.succ))

/-- The actual tensor frame on any original open, through genuine monoidal pullback. -/
def tensorFrame (U : X.Opens) : {r : ℕ} → (M : Fin (r+1) → X.Modules) →
    (∀ j,(pullback U.ι).obj (M j) ≅ unitObj U.toScheme) →
      ((pullback U.ι).obj (tensorLine M) ≅ unitObj U.toScheme)
  | 0,_,e => e 0
  | r+1,M,e =>
      (Functor.Monoidal.μIso (pullback U.ι) (M 0) (tensorLine (fun j : Fin (r+1) => M j.succ))).symm ≪≫
        (e 0 ⊗ᵢ tensorFrame U (fun j : Fin (r+1) => M j.succ) (fun j => e j.succ)) ≪≫
          ModularCurves.unitObjTensorIso U.toScheme

/-- EVERY original scalar multiplies in the actual same whole tensor frame. -/
theorem tensorFrame_scalar (U : X.Opens) {r : ℕ} (M : Fin (r+1) → X.Modules)
    (e : ∀ j,(pullback U.ι).obj (M j) ≅ unitObj U.toScheme)
    (a : ∀ j,unitObj X ⟶ M j) (c : Fin (r+1) → Γ(U.toScheme,⊤))
    (hc : ∀ j,pullbackSectionHom U.ι (a j) ≫ (e j).hom =
      ModularCurves.unitEndomorphismOfTopSection (c j)) :
    pullbackSectionHom U.ι (tensorSection M a) ≫ (tensorFrame U M e).hom =
      ModularCurves.unitEndomorphismOfTopSection (∏ j,c j) := by
  induction r with
  | zero =>
    rw [Fin.prod_univ_one]
    exact hc 0
  | succ r ih =>
    change pullbackSectionHom U.ι (tensorSectionHom (a 0)
      (tensorSection (fun j : Fin (r+1) => M j.succ) (fun j => a j.succ))) ≫
        (Functor.Monoidal.μIso (pullback U.ι) (M 0) (tensorLine (fun j : Fin (r+1) => M j.succ))).inv ≫
          ((e 0).hom ⊗ₘ (tensorFrame U (fun j : Fin (r+1) => M j.succ) (fun j => e j.succ)).hom) ≫
            (ModularCurves.unitObjTensorIso U.toScheme).hom = _
    rw [← Category.assoc,pullback_tensorSectionHom,← Category.assoc,tensorSectionHom_comp,
      hc 0,ih (fun j : Fin (r+1) => M j.succ) (fun j => e j.succ)
        (fun j => a j.succ) (fun j => c j.succ) (fun j => hc j.succ)]
    simp only [tensorSectionHom,Category.assoc,ModularCurves.unitObjTensorIso_hom_comp_scalars,
      Iso.inv_hom_id_assoc,Fin.prod_univ_succ]

/-- Actual invertibility of every entire original tensor factor gives actual invertibility of their whole tensor line. -/
theorem tensorLine_isInvertible {r : ℕ} (M : Fin (r+1) → X.Modules)
    (hM : ∀ j,IsInvertible (M j)) : IsInvertible (tensorLine M) := by
  induction r with
  | zero => exact hM 0
  | succ r ih =>
    exact ((hM 0).tensorObj
      (ih (fun j : Fin (r+1) => M j.succ) (fun j => hM j.succ))).of_iso
        (ModularCurves.monoidalTensorObjIso (M 0) (tensorLine (fun j : Fin (r+1) => M j.succ)))

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {r : ℕ} (d : Fin (r+1) → ℕ)
    (q : ∀ j,X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d j+1)) k))
    (t : ∀ j,Fin (d j+1)) (n : Fin (r+1) → ℕ)

/-- The entire ACTUAL original tensor of every original pulled projective power, on the SAME original scheme. -/
def projectiveLine : X.Modules :=
  tensorLine (fun j => (pullback (q j)).obj (coordinateHyperplanePoleSheafPower (R := k) (t j) (n j)))

/-- Every actual original finite projective power tensor line is genuinely invertible. -/
theorem projectiveLine_isInvertible : IsInvertible (projectiveLine d q t n) :=
  tensorLine_isInvertible _ (fun j =>
    (coordinateHyperplanePoleSheafPower_isInvertible (R := k) (t j) (n j)).pullback (q j))

/-- The entire ACTUAL original tensor section of every original homogeneous form. -/
def projectiveHomogeneousSection
    (F : ∀ j,MvPolynomial (Fin (d j+1)) k) (hF : ∀ j,(F j).IsHomogeneous (n j)) :
    unitObj X ⟶ projectiveLine d q t n :=
  tensorSection _ (fun j => pullbackSectionHom (q j)
    (SchemePullbackSubopenFrames.projectiveSectionHom (t j) (n j) (F j) (hF j)))

/-- The ACTUAL original finite power tensor frame on ANY simultaneous original subopen. -/
def projectiveFrame (a : ∀ j,Fin (d j+1)) (U : X.Opens)
    (hU : ∀ j,U ≤ q j ⁻¹ᵁ coordinateOpen (R := k) (a j)) :
    (pullback U.ι).obj (projectiveLine d q t n) ≅ unitObj U.toScheme :=
  tensorFrame U _ (fun j =>
    SchemePullbackSubopenFrames.projectiveFrame (q j) (t j) (n j) (a j) U (hU j))

/-- EVERY entire original finite homogeneous tensor section retains the product of its SAME actual dehomogenized scalars. -/
theorem projectiveFrame_forms_scalar (a : ∀ j,Fin (d j+1)) (U : X.Opens)
    (hU : ∀ j,U ≤ q j ⁻¹ᵁ coordinateOpen (R := k) (a j))
    (F : ∀ j,MvPolynomial (Fin (d j+1)) k) (hF : ∀ j,(F j).IsHomogeneous (n j)) :
    pullbackSectionHom U.ι (projectiveHomogeneousSection d q t n F hF) ≫
      (projectiveFrame d q t n a U hU).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (∏ j,((q j).resLE (coordinateOpen (R := k) (a j)) U (hU j)).appTop.hom
          (ModularCurves.affineOpenTopSection
            ⟨coordinateOpen (R := k) (a j),coordinateOpen_isAffineOpen (a j)⟩
            (ProjectiveHomogeneousSections.coefficient (a j) (n j) (F j) (hF j)))) := by
  exact tensorFrame_scalar U _ _ _ _ (fun j =>
    SchemePullbackSubopenFrames.projectiveForm_scalar (q j) (t j) (n j) (a j) U (hU j) (F j) (hF j))

end EnvelopeProperty.FiniteOriginalProjectivePowerFrames
