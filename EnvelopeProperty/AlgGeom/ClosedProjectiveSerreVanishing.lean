import EnvelopeProperty.AlgGeom.CoherentProjectiveSerreVanishing
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import EnvelopeProperty.Global.ProjectiveAffineCover
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward

/-! # True original Serre vanishing on actual original closed projective schemes -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules MvPolynomial TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveSerreVanishing
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {X : Scheme.{u}}

omit [IsNoetherianRing R] in
private theorem sheaf_H_subsingleton_of_ordered_isZero [X.IsSeparated]
    (p : X ⟶ Spec (.of R)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) (q : ℕ)
    (hM : IsZero ((orderedBaseCechComplex p M U).homology (q + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  have hbase : IsZero ((baseCechComplex p M U).homology (q + 1)) :=
    IsZero.of_iso hM (baseCechOrderedHomologyIso p M U (q + 1))
  have hcech := (baseCechComplex_exactAt_iff p M U (q + 1)).mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hbase)
  exact (TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    U M.sheaf hU
    (fun a j b => cechIntersection_subsingleton_H M U hUa a j b) q).mp hcech

/-- Actual closed pushforward, whole original projection formula and genuine
projective Serre vanishing DERIVE ALL positive original sheaf cohomology
vanishing on the SAME original closed scheme, for ALL larger twists. -/
theorem exists_sheafCohomology_bound
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion i]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (n + 1)) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (M ⊗ (Scheme.Modules.pullback i).obj
          (coordinateHyperplaneTwist (R := R) j (d : ℤ)) : X.Modules).sheaf (q + 1)) := by
  let p := homogeneousProjπ (R := R) (σ := Fin (n + 1))
  let U := coordinateOpenCover (R := R) (σ := Fin (n + 1))
  let Q := (pushforward i).obj M
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom i
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion i
  let : X.IsSeparated := ProjectiveAffineCover.separated (i ≫ p) ⟨n, i, inferInstance, rfl⟩
  obtain ⟨N, hN⟩ := CoherentProjectiveSerreVanishing.exists_orderedCech_bound Q j
  refine ⟨N, fun d hd q => ?_⟩
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  let hL : IsInvertible L := coordinateHyperplaneTwist_isInvertible j (d : ℤ)
  let B := (Scheme.Modules.pullback i).obj L
  let : (M ⊗ B).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M B (hL.pullback i)
  let e : orderedBaseCechComplex (i ≫ p) (M ⊗ B) (fun a => i ⁻¹ᵁ U a) ≅
      orderedBaseCechComplex p (Q ⊗ L) U :=
    orderedBaseCechComplexPushforwardIso i p (M ⊗ B) U ≪≫
      (orderedBaseCechComplexFunctor p U).mapIso
        (SchemeLineProjectionFormula.lineProjectionFormulaObj i L hL M).symm
  have hv : IsZero ((orderedBaseCechComplex (i ≫ p) (M ⊗ B)
      (fun a => i ⁻¹ᵁ U a)).homology (q + 1)) :=
    IsZero.of_iso (hN d hd q) (HomologicalComplex.homologyMapIso e (q + 1))
  exact sheaf_H_subsingleton_of_ordered_isZero (i ≫ p) (M ⊗ B)
    (fun a => i ⁻¹ᵁ U a) (i.iSup_preimage_eq_top (iSup_coordinateOpenCover_eq_top (R := R)))
    (fun a => (coordinateOpenCover_isAffineOpen (R := R) a).preimage i) q hv

end EnvelopeProperty.ClosedProjectiveSerreVanishing
