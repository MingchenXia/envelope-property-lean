import EnvelopeProperty.AlgGeom.OriginalAmpleSerreVanishing
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # Actual first-cohomology vanishing for the original geometrically ample powers -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralSerrePowers
open CanonicalGeometry
attribute [local instance] MvPolynomial.gradedAlgebra Scheme.Modules.monoidalCategory

private theorem finiteType_of_invertible {X : Scheme.{u}} (M : X.Modules)
    (hM : IsInvertible M) : M.IsFiniteType := by
  let : M.IsFinitePresentation := hM.isFinitePresentation
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
  constructor
  intro i
  exact (hq.isFinite_presentation i).isFiniteType_generators

/-- Original geometric ampleness internally supplies a bound for vanishing
of actual first sheaf cohomology of every sufficiently large original power.
The source need not be integral, reduced, normal or smooth. -/
theorem exists_sheafH1_bound_of_ample {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (L : X.Modules)
    (hL : SchemeLineAmpleness.IsAmple p L) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      Subsingleton (CategoryTheory.Sheaf.H (bundleTensorPower L s).sheaf 1) := by
  obtain ⟨hInv, r, hr, n, i, hi, _hp, ⟨E⟩⟩ := hL
  let : IsClosedImmersion i := hi
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFiniteType := finiteType_of_invertible (unitObj X) isInvertible_unit
  obtain ⟨N, hN⟩ := @OriginalAmpleSerreVanishing.exists_sheafCohomology_bound
    R _ _ (Fin (n + 1)) _ X i hi (unitObj X) L _ _ hInv r hr
      (0 : Fin (n + 1)) E.symm
  refine ⟨N, fun s hs => ?_⟩
  let γ : unitObj X ⊗ bundleTensorPower L s ≅ bundleTensorPower L s :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl _) ≪≫ λ_ _
  let eH := (CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology X) 1).mapIso
      ((Scheme.Modules.toSheaf X).mapIso γ)
  exact AddCommGrpCat.subsingleton_of_isZero
    (CategoryTheory.Limits.IsZero.of_iso
      (@AddCommGrpCat.isZero_of_subsingleton _ (hN s hs 0)) eH.symm)

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralSerrePowers
