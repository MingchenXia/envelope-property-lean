import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalFrame

/-! # Actual whole affine canonical frame from the SAME original basis alone -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace EnvelopeProperty.CanonicalGeometry
universe u
set_option backward.isDefEq.respectTransparency false
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of k)) (n : ℕ)

/-- The SAME original global differential basis DERIVES a whole original canonical
sheaf frame, without any finite-type/smoothness assumption on the affine scheme. -/
def affineCanonicalBasisFrame
    (b : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤))) :
    canonicalLineSheaf f n ≅ Scheme.Modules.unitObj X := by
  letI := affineChartAlgebra f ⊤
  let j := (Scheme.isoSpec X).inv
  have hj : j ≫ f = affineStructuralMap k Γ(X, ⊤) := by
    dsimp only [j]
    rw [← IsAffineOpen.fromSpec_top]
    exact affineChartStructuralMap_eq_affineStructuralMap f (isAffineOpen_top X)
  let e : (Scheme.Modules.pullback j).obj (canonicalLineSheaf f n) ≅
      Scheme.Modules.unitObj (Spec Γ(X, ⊤)) :=
    (Scheme.Modules.restrictFunctorIsoPullback j).symm.app (canonicalLineSheaf f n) ≪≫
      exteriorCotangentSheafOpenImmersionIso f j n ≪≫
      eqToIso (congrArg (fun q => exteriorCotangentSheaf q n) hj) ≪≫
      affineTopExteriorSheafFrame k Γ(X, ⊤) b
  exact (Scheme.Modules.pullbackId X).symm.app (canonicalLineSheaf f n) ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.isoSpec X).hom_inv_id).symm.app
      (canonicalLineSheaf f n) ≪≫
    (Scheme.Modules.pullbackComp (Scheme.isoSpec X).hom j).symm.app
      (canonicalLineSheaf f n) ≪≫
    (Scheme.Modules.pullback (Scheme.isoSpec X).hom).mapIso e ≪≫
      Scheme.Modules.pullbackUnitIso (Scheme.isoSpec X).hom

/-- Genuine original differential freeness derives actual canonical invertibility even
on affine localizations which need not be of finite presentation over the base field. -/
theorem affineCanonical_isInvertible_of_basis
    (b : letI := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤))) :
    Scheme.Modules.IsInvertible (canonicalLineSheaf f n) :=
  Scheme.Modules.isInvertible_unit.of_iso (affineCanonicalBasisFrame f n b)

end EnvelopeProperty.CanonicalGeometry
