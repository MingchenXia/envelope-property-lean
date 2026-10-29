import EnvelopeProperty.AlgGeom.ProjectiveRegularityGlobalGeneration
import EnvelopeProperty.AlgGeom.ClosedProjectiveGlobalGeneration
import EnvelopeProperty.AlgGeom.ClosedProjectiveSerreVanishing

/-! # Finite regularity generation on the original closed projective scheme -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules MvPolynomial TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedProjectiveRegularityGeneration
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra

private theorem subsingleton_H_iff_ordered_zero {X S : Scheme.{u}} [X.IsSeparated]
    (p : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) ↔
      IsZero ((orderedBaseCechComplex p M U).homology (q + 1)) := by
  have hcech := TopCat.Sheaf.cechComplex_exactAt_succ_iff_subsingleton_H_of_subsingleton_restrict_H
    U M.sheaf hU (fun a j b => cechIntersection_subsingleton_H M U hUa a j b) q
  constructor
  · intro h
    have hb := (baseCechComplex_exactAt_iff p M U (q + 1)).mpr (hcech.mpr h)
    have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hb
    exact IsZero.of_iso hz (baseCechOrderedHomologyIso p M U (q + 1)).symm
  · intro h
    have hb : IsZero ((baseCechComplex p M U).homology (q + 1)) :=
      IsZero.of_iso h (baseCechOrderedHomologyIso p M U (q + 1))
    exact hcech.mp ((baseCechComplex_exactAt_iff p M U (q + 1)).mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr hb))

variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}

/-- Original positive twisted cohomology vanishes precisely when that of the
actual closed pushforward does, via original affine Cech complexes and projection formula. -/
theorem subsingleton_H_twist_iff_pushforward
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion i]
    (M : X.Modules) [M.IsQuasicoherent] (j : Fin (n + 1)) (t : ℤ) (q : ℕ) (hq : 0 < q) :
    Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j t)).sheaf q) ↔
    Subsingleton (CategoryTheory.Sheaf.H
      ((pushforward i).obj M ⊗ coordinateHyperplaneTwist (R := R) j t).sheaf q) := by
  cases q with
  | zero => omega
  | succ q =>
    let p := homogeneousProjπ (R := R) (σ := Fin (n + 1))
    let U := coordinateOpenCover (R := R) (σ := Fin (n + 1))
    let Q := (pushforward i).obj M
    let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom i
    let : X.IsSeparated := ProjectiveAffineCover.separated (i ≫ p) ⟨n, i, inferInstance, rfl⟩
    let L := coordinateHyperplaneTwist (R := R) j t
    have hL : IsInvertible L := coordinateHyperplaneTwist_isInvertible j t
    let B := (Scheme.Modules.pullback i).obj L
    let : (M ⊗ B).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M B (hL.pullback i)
    let : (Q ⊗ L).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight Q L hL
    let e : orderedBaseCechComplex (i ≫ p) (M ⊗ B) (fun a => i ⁻¹ᵁ U a) ≅
        orderedBaseCechComplex p (Q ⊗ L) U :=
      orderedBaseCechComplexPushforwardIso i p (M ⊗ B) U ≪≫
        (orderedBaseCechComplexFunctor p U).mapIso
          (SchemeLineProjectionFormula.lineProjectionFormulaObj i L hL M).symm
    have hs := subsingleton_H_iff_ordered_zero (i ≫ p) (M ⊗ B)
      (fun a => i ⁻¹ᵁ U a) (i.iSup_preimage_eq_top (iSup_coordinateOpenCover_eq_top (R := R)))
      (fun a => (coordinateOpenCover_isAffineOpen (R := R) a).preimage i) q
    have ht := subsingleton_H_iff_ordered_zero p (Q ⊗ L) U
      (iSup_coordinateOpenCover_eq_top (R := R)) (coordinateOpenCover_isAffineOpen (R := R)) q
    constructor
    · intro h
      exact ht.mpr (IsZero.of_iso (hs.mp h) (HomologicalComplex.homologyMapIso e (q + 1)).symm)
    · intro h
      exact hs.mpr (IsZero.of_iso (ht.mp h) (HomologicalComplex.homologyMapIso e (q + 1)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finitely many original regularity groups produce finite generators on
an actual closed projective model, over every commutative base including dimension zero. -/
theorem exists_generatingSections_of_regularity
    (i : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion i]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (j : Fin (n + 1))
    (hM : ∀ q : ℕ, 0 < q → q < n + 1 → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) j (-(q : ℤ)))).sheaf q)) :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  let Q := (pushforward i).obj M
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom i
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion i
  have hQ (q : ℕ) (hq : 0 < q) (hqn : q < Fintype.card (Fin (n + 1))) :
      Subsingleton (CategoryTheory.Sheaf.H
        (Q ⊗ coordinateHyperplaneTwist (R := R) j (-(q : ℤ))).sheaf q) :=
    (subsingleton_H_twist_iff_pushforward i M j (-(q : ℤ)) q hq).mp
      (hM q hq (by simpa only [Fintype.card_fin] using hqn))
  obtain ⟨G, hG⟩ := ProjectiveRegularityGlobalGeneration.exists_generatingSections_of_regularity Q j hQ
  let : G.IsFiniteType := hG
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections i G
  let : H.IsFiniteType := ClosedProjectiveGlobalGeneration.pullback_generatingSections_isFiniteType i G
  let e := (pullbackPushforwardAdjunction i).counit.app M
  let : Epi e := ClosedProjectiveGlobalGeneration.counit_epi_of_isInducing i i.isClosedEmbedding.isInducing M
  exact ⟨H.ofEpi e, inferInstance⟩

end EnvelopeProperty.ClosedProjectiveRegularityGeneration
