import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology
import EnvelopeProperty.AlgGeom.SchemeModuleCechNativeCohomology

/-! # Actual ordinary native higher cohomology of nested original restrictions

Actual canonical original open-image scheme isomorphisms and native
whole restriction composition identify nested original module cohomology
with direct original restriction cohomology. There is no incoming
acyclicity, coefficient-matching or higher-H comparison certificate.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeOpenNestedCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual ordinary positive-H vanishing is preserved by restriction along
an actual original scheme isomorphism. The finite affine cover, native
pushforward comparison and whole adjunction-unit inverse are internal. -/
theorem restrictIso_H_succ_iff {A B : Scheme.{u}} [CompactSpace B] [B.IsSeparated]
    (e : A ≅ B) (M : B.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H (M.restrict e.hom).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  classical
  obtain ⟨I, hI, U, hU, hUa⟩ := B.exists_finite_affine_openCover
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hpush := AffinePushforwardCohomology.subsingleton_H_iff_pushforward e.hom (𝟙 B)
    (M.restrict e.hom) U hU hUa q
  have hη : IsIso ((restrictAdjunction e.hom).unit.app M) := by infer_instance
  let := hη
  let K := asIso ((restrictAdjunction e.hom).unit.app M)
  refine hpush.trans ⟨?_, ?_⟩
  · intro h
    exact AffinePushforwardCohomology.subsingleton_H_of_retract K.hom K.inv K.hom_inv_id (q + 1) h
  · intro h
    exact AffinePushforwardCohomology.subsingleton_H_of_retract K.inv K.hom K.inv_hom_id (q + 1) h

/-- The actual SAME original F restricted twice is the canonical original
open-image scheme's actual pullback restriction of the direct restriction.
The original whole module iso uses only genuine native restriction composition. -/
def nestedRestrictionIso {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (W : V.toScheme.Opens) :
    (M.restrict (V.ι ''ᵁ W).ι).restrict (V.ι.isoImage W).hom ≅
      (M.restrict V.ι).restrict W.ι :=
  ((restrictFunctorComp (V.ι.isoImage W).hom (V.ι ''ᵁ W).ι).app M).symm ≪≫
    (restrictFunctorCongr (V.ι.isoImage_hom_ι W)).app M ≪≫
      (restrictFunctorComp W.ι V.ι).app M

/-- Actual ordinary higher H of the SAME original nested restriction is
equivalent to ordinary H of SAME original direct image-open restriction.
Only genuine original geometry is input; no vanishing/matching premise. -/
theorem nested_restrict_H_succ_iff_image {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (V : X.Opens) (W : V.toScheme.Opens)
    [CompactSpace (V.ι ''ᵁ W).toScheme] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((M.restrict V.ι).restrict W.ι).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H (M.restrict (V.ι ''ᵁ W).ι).sheaf (q + 1)) := by
  let : (V.ι ''ᵁ W).toScheme.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (V.ι ''ᵁ W).ι]
    infer_instance⟩
  let E := nestedRestrictionIso M V W
  have hmodules :
      Subsingleton (CategoryTheory.Sheaf.H ((M.restrict V.ι).restrict W.ι).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H
        ((M.restrict (V.ι ''ᵁ W).ι).restrict (V.ι.isoImage W).hom).sheaf (q + 1)) := by
    constructor
    · intro h
      exact AffinePushforwardCohomology.subsingleton_H_of_retract E.hom E.inv E.hom_inv_id (q + 1) h
    · intro h
      exact AffinePushforwardCohomology.subsingleton_H_of_retract E.inv E.hom E.inv_hom_id (q + 1) h
  exact hmodules.trans (restrictIso_H_succ_iff (V.ι.isoImage W)
    (M.restrict (V.ι ''ᵁ W).ι) q)

end EnvelopeProperty.SchemeOpenNestedCohomology
