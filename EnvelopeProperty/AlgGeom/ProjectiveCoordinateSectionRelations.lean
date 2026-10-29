import EnvelopeProperty.AlgGeom.GeneratedTupleTwistSections

/-! # SAME original global coordinate sections and their actual whole projective-chart relations -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCoordinateSectionRelations
open SchemeLineSectionEvaluation GeneratedTupleTwistSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {m : ℕ}

private theorem coefficient_self (i : Fin (m + 1)) :
    (coordinateOpen (R := R) i).topIso.inv.hom
      (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i)) = 1 := by
  rw [ProjectiveHomogeneousSections.coefficient_X, coordinateHyperplaneLocalEquation_self, map_one]

private theorem isIso_of_scalar_one {B : Scheme.{u}} {M : B.Modules}
    (α : unitObj B ⟶ M) (e : M ≅ unitObj B) (r : Γ(B, ⊤))
    (h : α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r) (hr : r = 1) : IsIso α := by
  have hh : IsIso (α ≫ e.hom) := by
    rw [h, hr, ModularCurves.unitEndomorphismOfTopSection_one]
    infer_instance
  exact IsIso.of_isIso_comp_right α e.hom

private theorem relation_of_scalars {B : Scheme.{u}} {M : B.Modules}
    (α β : unitObj B ⟶ M) (e : M ≅ unitObj B) (r s : Γ(B, ⊤))
    (hα : α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r)
    (hβ : β ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection s) (hs : s = 1) :
    α = ModularCurves.unitEndomorphismOfTopSection r ≫ β := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, hα, hβ, hs, ModularCurves.unitEndomorphismOfTopSection_one, Category.comp_id]

/-- The SAME original global coordinate section is an ACTUAL whole line isomorphism on its own chart. -/
theorem sectionHom_isIso_on_own_chart (i k : Fin (m + 1)) :
    IsIso (pullbackSectionHom (coordinateOpen (R := R) i).ι
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i))) := by
  exact isIso_of_scalar_one
    (M := (Scheme.Modules.pullback (coordinateOpen (R := R) i).ι).obj
      (coordinateHyperplaneTwist (R := R) k 1))
    (pullbackSectionHom (coordinateOpen (R := R) i).ι
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i)))
    (pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) k 1)
      (coordinateOpen (R := R) i) (coordinateHyperplaneTwistTrivialization (R := R) i k 1))
    _ (coordinateSection_localScalar i k i) (coefficient_self i)

/-- On the WHOLE original chart EVERY SAME original coordinate section has
its actual original ratio to the SAME original pivot section. -/
theorem sectionHom_ratio_on_chart (i k j : Fin (m + 1)) :
    pullbackSectionHom (coordinateOpen (R := R) i).ι
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)) =
      ModularCurves.unitEndomorphismOfTopSection
        ((coordinateOpen (R := R) i).topIso.inv.hom
          (ProjectiveHomogeneousSections.coefficient i 1 (MvPolynomial.X j)
            (MvPolynomial.isHomogeneous_X R j))) ≫
        pullbackSectionHom (coordinateOpen (R := R) i).ι
          (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X R i)) := by
  exact relation_of_scalars
    (M := (Scheme.Modules.pullback (coordinateOpen (R := R) i).ι).obj
      (coordinateHyperplaneTwist (R := R) k 1))
    (pullbackSectionHom (coordinateOpen (R := R) i).ι
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)))
    (pullbackSectionHom (coordinateOpen (R := R) i).ι
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i)))
    (pullbackIsoOfRestrictIso (coordinateHyperplaneTwist (R := R) k 1)
      (coordinateOpen (R := R) i) (coordinateHyperplaneTwistTrivialization (R := R) i k 1))
    _ _ (coordinateSection_localScalar i k j) (coordinateSection_localScalar i k i) (coefficient_self i)

end EnvelopeProperty.ProjectiveCoordinateSectionRelations
