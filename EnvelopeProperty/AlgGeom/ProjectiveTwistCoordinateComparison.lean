import EnvelopeProperty.AlgGeom.SchemeModuleFrameGluing
import ModularCurves.EllipticCurve.ProjectiveSpaceTwist

/-! # Actual original projective twists are independent of the coordinate hyperplane -/
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveTwistCoordinateComparison
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem coordinateCover :
    ∀ x : Proj (homogeneousSubmodule σ R), ∃ i : σ, x ∈ coordinateOpen (R := R) i := by
  intro x
  have hx : x ∈ ⨆ i : σ, coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

private theorem commonTransitions_congr {X : Scheme.{u}} (M N : X.Modules)
    {U V W W' : X.Opens} (hW : W = W')
    (hU : W ≤ U) (hV : W ≤ V) (hU' : W' ≤ U) (hV' : W' ≤ V)
    (eU : M.restrict U.ι ≅ unitObj U.toScheme)
    (eV : M.restrict V.ι ≅ unitObj V.toScheme)
    (gU : N.restrict U.ι ≅ unitObj U.toScheme)
    (gV : N.restrict V.ι ≅ unitObj V.toScheme)
    (htrans : ∃ c : unitObj W.toScheme ⟶ unitObj W.toScheme,
      (restrictOpenTrivialization hU eU).hom = (restrictOpenTrivialization hV eV).hom ≫ c ∧
      (restrictOpenTrivialization hU gU).hom = (restrictOpenTrivialization hV gV).hom ≫ c) :
    ∃ c : unitObj W'.toScheme ⟶ unitObj W'.toScheme,
      (restrictOpenTrivialization hU' eU).hom = (restrictOpenTrivialization hV' eV).hom ≫ c ∧
      (restrictOpenTrivialization hU' gU).hom = (restrictOpenTrivialization hV' gV).hom ≫ c := by
  subst W'
  exact htrans

private theorem sameFrameTransitions (j k : σ) (d : ℤ) (a b : σ) :
    ∃ c : unitObj (coordinateOpen (R := R) a ⊓ coordinateOpen (R := R) b).toScheme ⟶
        unitObj (coordinateOpen (R := R) a ⊓ coordinateOpen (R := R) b).toScheme,
      (restrictOpenTrivialization (inf_le_left : coordinateOpen (R := R) a ⊓
          coordinateOpen (R := R) b ≤ coordinateOpen (R := R) a)
        (coordinateHyperplaneTwistTrivialization (R := R) a j d)).hom =
      (restrictOpenTrivialization (inf_le_right : coordinateOpen (R := R) a ⊓
          coordinateOpen (R := R) b ≤ coordinateOpen (R := R) b)
        (coordinateHyperplaneTwistTrivialization (R := R) b j d)).hom ≫ c ∧
      (restrictOpenTrivialization (inf_le_left : coordinateOpen (R := R) a ⊓
          coordinateOpen (R := R) b ≤ coordinateOpen (R := R) a)
        (coordinateHyperplaneTwistTrivialization (R := R) a k d)).hom =
      (restrictOpenTrivialization (inf_le_right : coordinateOpen (R := R) a ⊓
          coordinateOpen (R := R) b ≤ coordinateOpen (R := R) b)
        (coordinateHyperplaneTwistTrivialization (R := R) b k d)).hom ≫ c := by
  exact commonTransitions_congr
    (coordinateHyperplaneTwist (R := R) j d) (coordinateHyperplaneTwist (R := R) k d)
    (coordinateOpenOverlap_eq (R := R) a b)
    (coordinateOpenOverlap_le_left (R := R) a b) (coordinateOpenOverlap_le_right (R := R) a b)
    inf_le_left inf_le_right
    (coordinateHyperplaneTwistTrivialization (R := R) a j d)
    (coordinateHyperplaneTwistTrivialization (R := R) b j d)
    (coordinateHyperplaneTwistTrivialization (R := R) a k d)
    (coordinateHyperplaneTwistTrivialization (R := R) b k d)
    ⟨ModularCurves.unitEndomorphismOfTopSection
      ((coordinateOpenTransitionTopUnit (R := R) a b ^ d :
          Γ((coordinateOpenOverlap (R := R) a b).toScheme,
            (⊤ : (coordinateOpenOverlap (R := R) a b).toScheme.Opens))ˣ) :
        Γ((coordinateOpenOverlap (R := R) a b).toScheme,
          (⊤ : (coordinateOpenOverlap (R := R) a b).toScheme.Opens))),
      coordinateHyperplaneTwistTrivialization_restrict_transition (R := R) a b j d,
      coordinateHyperplaneTwistTrivialization_restrict_transition (R := R) a b k d⟩

/-- Actual original same-degree coordinate-hyperplane twists are isomorphic
on the SAME original polynomial projective space; overlap compatibility is
DERIVED from their genuine original standard-coordinate frame transitions. -/
def coordinateIso (j k : σ) (d : ℤ) :
    coordinateHyperplaneTwist (R := R) j d ≅ coordinateHyperplaneTwist (R := R) k d :=
  SchemeModuleFrameGluing.glueOfFrames _ _ (fun i : σ => coordinateOpen (R := R) i)
    coordinateCover (fun i => coordinateHyperplaneTwistTrivialization (R := R) i j d)
    (fun i => coordinateHyperplaneTwistTrivialization (R := R) i k d)
    (sameFrameTransitions j k d)

/-- Every actual standard-open restriction is the SAME original
coefficient-preserving comparison of the two original coordinate twist frames. -/
theorem coordinateIso_restrict (j k : σ) (d : ℤ) (i : σ) :
    (SheafOfModules.overFunctor (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (coordinateOpen (R := R) i)).mapIso (coordinateIso j k d) =
      SchemeModuleFrameGluing.frameComparison _ _ (coordinateOpen (R := R) i)
        (coordinateHyperplaneTwistTrivialization (R := R) i j d)
        (coordinateHyperplaneTwistTrivialization (R := R) i k d) := by
  unfold coordinateIso
  apply SchemeModuleFrameGluing.glueOfFrames_restrict

end EnvelopeProperty.ProjectiveTwistCoordinateComparison
