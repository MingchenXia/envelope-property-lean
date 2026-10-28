import EnvelopeProperty.AlgGeom.SchemeProjectiveAffineInverseCohomology
import EnvelopeProperty.Vanishing.NadelLerayCech

/-! # Actual projective global twists supply the native pushforward comparison

The original global family supplies all actual inverse-image intersection
acyclicity internally. The existing native Leray-Cech comparison then gives
positive vanishing equivalence for the SAME original module and pushforward.
Quasicoherence of the actual pushforward is an explicit ordinary sheaf property;
no local cohomology, matching, cover or affine-morphism certificate is an input.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open MvPolynomial TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

namespace EnvelopeProperty.SchemeProjectiveAcyclicPushforwardCohomology
open CanonicalGeometry SchemeProjectiveSectionPositiveBasis
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual eventual original GLOBAL twists internally prove the local groups
needed by the existing native Leray comparison, so positive cohomology vanishes
for the SAME original F iff it vanishes for its SAME original pushforward.
Only original geometry, standard source/pushforward quasicoherence and the
explicit original GLOBAL family are assumed; f is not assumed affine. -/
theorem subsingleton_H_succ_iff_pushforward
    {R : Type u} [CommRing R] {n : ℕ} {X Y : Scheme.{u}}
    (j : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion j]
    (f : Y ⟶ X) [IsProper f] (F : Y.Modules) [F.IsQuasicoherent]
    [((pushforward f).obj F).IsQuasicoherent]
    (hGlobal : ∀ r : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H
        (F ⊗ bundleTensorPower ((pullback f).obj (embeddingLine j)) m).sheaf (r + 1)))
    (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F.sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H ((pushforward f).obj F).sheaf (q + 1)) := by
  classical
  let p := DeJongAlterations.projectiveSpaceStructure R n
  let : X.IsSeparated := ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (j ≫ p)]
    infer_instance⟩
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (j ≫ p)
  obtain ⟨I, hI, U, hU, hUa⟩ := X.exists_finite_affine_openCover
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hInter (a : ℕ) (i : Fin (a + 1) → I) (r : ℕ) :
      Subsingleton (CategoryTheory.Sheaf.H
        ((TopCat.Sheaf.restrict AddCommGrpCat
          (∏ᶜ fun k : Fin (a + 1) => f ⁻¹ᵁ U (i k)).isOpenEmbedding).obj F.sheaf) (r + 1)) := by
    let C : X.Opens := ∏ᶜ fun k : Fin (a + 1) => U (i k)
    have hC : IsAffineOpen C := IsAffineOpen.cechIntersection U hUa a i
    have hActual := SchemeProjectiveAffineInverseCohomology.projective_affine_inverseImage_H_succ_subsingleton
      j f F hGlobal ⟨C, hC⟩ r
    have hOpen : f ⁻¹ᵁ C = ∏ᶜ fun k : Fin (a + 1) => f ⁻¹ᵁ U (i k) :=
      f.preimage_cechIntersection U a i
    change Subsingleton (CategoryTheory.Sheaf.H
      (F.restrict (∏ᶜ fun k : Fin (a + 1) => f ⁻¹ᵁ U (i k)).ι).sheaf (r + 1))
    exact hOpen ▸ hActual
  exact Vanishing.NadelLerayCech.subsingleton_H_iff_pushforward f F U hU hUa hInter q

end EnvelopeProperty.SchemeProjectiveAcyclicPushforwardCohomology
