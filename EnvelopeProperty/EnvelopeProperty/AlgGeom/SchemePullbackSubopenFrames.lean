import EnvelopeProperty.AlgGeom.NativePulledProjectiveLineFrames

/-! # Actual original pulled module frames on arbitrary joint source subopens -/
open AlgebraicGeometry CategoryTheory MvPolynomial Opposite
open Scheme.Modules
open DeJongAlterations EnvelopeProperty.SchemeLineSectionEvaluation
noncomputable section
universe u
namespace EnvelopeProperty.SchemePullbackSubopenFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine original pulled frame on ANY actual original subopen, with no affine-morphism premise. -/
def frame {Y Z : Scheme.{u}} (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) {M : Z.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    (pullback V.ι).obj ((pullback g).obj M) ≅ unitObj V.toScheme :=
  (pullbackComp V.ι g).app M ≪≫
    frameViaFactor (g.resLE U V h) U.ι (V.ι ≫ g) (g.resLE_comp_ι h) e

/-- EVERY actual original scalar equation pulls to the SAME original source subopen through its genuine restriction map. -/
theorem frame_scalar {Y Z : Scheme.{u}} (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens)
    (h : V ≤ g ⁻¹ᵁ U) {M : Z.Modules}
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme)
    (α : unitObj Z ⟶ M) (c : Γ(U.toScheme,⊤))
    (hc : pullbackSectionHom U.ι α ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection c) :
    pullbackSectionHom V.ι (pullbackSectionHom g α) ≫ (frame g U V h e).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((g.resLE U V h).appTop.hom c) := by
  rw [frame,Iso.trans_hom,Iso.app_hom,← Category.assoc,pullbackSectionHom_comp]
  exact frameViaFactor_sectionHom_scalar (g.resLE U V h) U.ι (V.ι ≫ g)
    (g.resLE_comp_ι h) e α _ hc

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k] {Y : Scheme.{u}} {m : ℕ}
  (f : Y ⟶ Proj (homogeneousSubmodule (Fin (m+1)) k)) (t : Fin (m+1)) (n : ℕ) (j : Fin (m+1))
  (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ coordinateOpen (R := k) j)

/-- The actual original projective whole-section morphism, with its target module explicit. -/
def projectiveSectionHom (F : MvPolynomial (Fin (m+1)) k) (hF : F.IsHomogeneous n) :
    unitObj (Proj (homogeneousSubmodule (Fin (m+1)) k)) ⟶
      coordinateHyperplanePoleSheafPower (R := k) t n :=
  SchemeModuleGlobalSections.sectionHom _ (ProjectiveHomogeneousSections.homogeneousSection t n F hF)

/-- The actual original projective coordinate frame. -/
def projectiveSourceFrame :
    (pullback (coordinateOpen (R := k) j).ι).obj
      (coordinateHyperplanePoleSheafPower (R := k) t n) ≅
        unitObj (coordinateOpen (R := k) j).toScheme :=
  pullbackIsoOfRestrictIso (coordinateHyperplanePoleSheafPower (R := k) t n)
    (coordinateOpen (R := k) j)
    (coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t n)

/-- The ACTUAL original projective power-line frame on ANY original joint subopen, even for a nonclosed factor map. -/
def projectiveFrame :
    (pullback V.ι).obj ((pullback f).obj (coordinateHyperplanePoleSheafPower (R := k) t n)) ≅ unitObj V.toScheme :=
  frame f (coordinateOpen (R := k) j) V h (projectiveSourceFrame t n j)

private theorem projective_source_scalar (F : MvPolynomial (Fin (m+1)) k) (hF : F.IsHomogeneous n) :
    let U : (Proj (homogeneousSubmodule (Fin (m+1)) k)).affineOpens :=
      ⟨coordinateOpen (R := k) j,coordinateOpen_isAffineOpen j⟩
    pullbackSectionHom U.1.ι (projectiveSectionHom t n F hF) ≫
      (projectiveSourceFrame t n j).hom =
      ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.affineOpenTopSection U (ProjectiveHomogeneousSections.coefficient j n F hF)) := by
  let M := coordinateHyperplanePoleSheafPower (R := k) t n
  let U : (Proj (homogeneousSubmodule (Fin (m+1)) k)).affineOpens :=
    ⟨coordinateOpen (R := k) j,coordinateOpen_isAffineOpen j⟩
  let e := coordinateHyperplanePoleSheafPowerTrivialization (R := k) j t n
  have hc : ModularCurves.localTrivializationCoefficient M U e
      (ProjectiveHomogeneousSections.homogeneousSection t n F hF) =
      ProjectiveHomogeneousSections.coefficient j n F hF :=
    (ModularCurves.overTrivializationCoefficient_overTrivializationOfRestrictIso M U e _).symm.trans
      (ProjectiveHomogeneousSections.section_coefficient j t n F hF)
  exact (SchemeLineSectionEvaluation.sectionHom_localScalar M U e
    (ProjectiveHomogeneousSections.homogeneousSection t n F hF)).trans
      (congrArg (fun c => ModularCurves.unitEndomorphismOfTopSection
        (ModularCurves.affineOpenTopSection U c)) hc)

/-- EVERY actual original homogeneous section has its exact original dehomogenized scalar in the SAME derived subopen frame. -/
theorem projectiveForm_scalar (F : MvPolynomial (Fin (m+1)) k) (hF : F.IsHomogeneous n) :
    let U : (Proj (homogeneousSubmodule (Fin (m+1)) k)).affineOpens :=
      ⟨coordinateOpen (R := k) j,coordinateOpen_isAffineOpen j⟩
    pullbackSectionHom V.ι (pullbackSectionHom f (projectiveSectionHom t n F hF)) ≫
      (projectiveFrame f t n j V h).hom =
      ModularCurves.unitEndomorphismOfTopSection
        ((f.resLE U.1 V h).appTop.hom
          (ModularCurves.affineOpenTopSection U (ProjectiveHomogeneousSections.coefficient j n F hF))) := by
  exact frame_scalar f (coordinateOpen (R := k) j) V h (projectiveSourceFrame t n j)
    (projectiveSectionHom t n F hF) _ (projective_source_scalar t n j F hF)

end EnvelopeProperty.SchemePullbackSubopenFrames
