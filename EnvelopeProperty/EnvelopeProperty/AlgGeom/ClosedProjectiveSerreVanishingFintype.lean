import EnvelopeProperty.AlgGeom.CoherentProjectiveSerreVanishing
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Serre vanishing for actual closed projective schemes -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.ClosedProjectiveSerreVanishingFintype

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory

/-- A genuine closed embedding gives one bound for every larger original
pulled-back projective twist and every positive original sheaf-cohomology degree. -/
theorem exists_sheafCohomology_bound {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}}
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (M ⊗ (Scheme.Modules.pullback i).obj
          (coordinateHyperplaneTwist (R := R) j (d : ℤ))).sheaf (q+1)) := by
  classical
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let P := Proj (homogeneousSubmodule σ R)
  let π := homogeneousProjπ (R := R) (σ := σ)
  let Q := (pushforward i).obj M
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom i
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion i
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from i]
    infer_instance⟩
  let U := coordinateOpenCover (R := R) (σ := σ)
  let V : ULift.{u} σ → X.Opens := fun a => i ⁻¹ᵁ U a
  have hV : (⨆ a, V a) = ⊤ :=
    i.iSup_preimage_eq_top (iSup_coordinateOpenCover_eq_top (R := R))
  have hVa (a : ULift.{u} σ) : IsAffineOpen (V a) :=
    (coordinateOpenCover_isAffineOpen (R := R) a).preimage i
  obtain ⟨N, hN⟩ := CoherentProjectiveSerreVanishing.exists_orderedCech_bound Q j
  refine ⟨N, ?_⟩
  intro d hd q
  let L := coordinateHyperplaneTwist (R := R) j (d : ℤ)
  have hL : IsInvertible L := coordinateHyperplaneTwist_isInvertible j (d : ℤ)
  let Md := M ⊗ (Scheme.Modules.pullback i).obj L
  let : Md.IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M
      ((Scheme.Modules.pullback i).obj L) (hL.pullback i)
  let e : orderedBaseCechComplex (i ≫ π) Md V ≅
      orderedBaseCechComplex π (Q ⊗ L) U :=
    orderedBaseCechComplexPushforwardIso i π Md U ≪≫
      (orderedBaseCechComplexFunctor π U).mapIso
        (SchemeLineProjectionFormula.lineProjectionFormulaObj i L hL M).symm
  have hordered : IsZero ((orderedBaseCechComplex (i ≫ π) Md V).homology (q+1)) :=
    IsZero.of_iso (hN d hd q) (HomologicalComplex.homologyMapIso e (q+1))
  have hbase : IsZero ((baseCechComplex (i ≫ π) Md V).homology (q+1)) :=
    IsZero.of_iso hordered (baseCechOrderedHomologyIso (i ≫ π) Md V (q+1))
  have hcech := (baseCechComplex_exactAt_iff (i ≫ π) Md V (q+1)).mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hbase)
  exact (TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    V Md.sheaf hV (fun p a r => cechIntersection_subsingleton_H Md V hVa p a r) q).mp hcech

end EnvelopeProperty.ClosedProjectiveSerreVanishingFintype
