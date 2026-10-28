import EnvelopeProperty.AlgGeom.CoherentProjectiveSerreVanishing
import EnvelopeProperty.Global.ProjectiveAffineCover

/-! # Actual quasicoherent cohomology above the length of an affine cover -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.ProjectiveCohomologicalDimension

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- A finite ordered affine cover bounds the positive actual sheaf cohomology
of every quasicoherent module on a separated scheme. -/
theorem subsingleton_H_of_card_le {X : Scheme.{u}} [X.IsSeparated]
    (p : X ⟶ Spec (.of R)) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (hq : Fintype.card ι ≤ q + 1) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  let C := orderedBaseCechComplex p M U
  have hX : IsZero (C.X (q + 1)) :=
    orderedBaseCechObject_isZero_of_card_le p M U (q + 1) hq
  have hord : IsZero (C.homology (q + 1)) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (C.sc (q + 1)) hX
  have hbase : IsZero ((baseCechComplex p M U).homology (q + 1)) :=
    IsZero.of_iso hord (baseCechOrderedHomologyIso p M U (q + 1))
  have hcech := (baseCechComplex_exactAt_iff p M U (q + 1)).mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hbase)
  exact (TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    U M.sheaf hU
    (fun a j b => cechIntersection_subsingleton_H M U hUa a j b) q).mp hcech

/-- On actual polynomial projective space with finitely many coordinates,
every quasicoherent module has zero positive actual sheaf cohomology in
degrees at least the number of coordinates. For n+1 coordinates this is
the usual bound q > n. No Noetherian, finite-type or flatness hypothesis
is needed. -/
theorem subsingleton_H_projective_of_card_le {σ : Type} [Fintype σ]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] (q : ℕ) (hq0 : 0 < q) (hq : Fintype.card σ ≤ q) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  classical
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  cases q with
  | zero => omega
  | succ q =>
    let p := homogeneousProjπ (R := R) (σ := σ)
    exact subsingleton_H_of_card_le p M (coordinateOpenCover (R := R))
      (iSup_coordinateOpenCover_eq_top (R := R))
      (coordinateOpenCover_isAffineOpen (R := R)) q
      (by simpa only [Fintype.card_ulift] using hq)

end EnvelopeProperty.ProjectiveCohomologicalDimension
