import EnvelopeProperty.AlgGeom.ProjectiveCoordinateGeneratorDescent
import EnvelopeProperty.AlgGeom.CoherentProjectiveGlobalGeneration

/-! # The actual Castelnuovo–Mumford finite global-generation criterion -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjectiveRegularityGlobalGeneration
attribute [local instance] Scheme.Modules.monoidalCategory MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Vanishing of the actual finitely many regularity cohomology groups gives
finite global generators of the original module, over every commutative base. -/
theorem exists_generatingSections_of_regularity
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ)
    (hM : ∀ q : ℕ, 0 < q → q < Fintype.card σ → Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (-(q : ℤ))).sheaf q)) :
    ∃ G : M.GeneratingSections, G.IsFiniteType := by
  have hall (q : ℕ) (hq : 0 < q) : Subsingleton (CategoryTheory.Sheaf.H
      (M ⊗ coordinateHyperplaneTwist (R := R) j (-(q : ℤ))).sheaf q) := by
    by_cases hlt : q < Fintype.card σ
    · exact hM q hq hlt
    · let : (M ⊗ coordinateHyperplaneTwist (R := R) j (-(q : ℤ))).IsQuasicoherent :=
        SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M _
          (coordinateHyperplaneTwist_isInvertible j _)
      exact ProjectiveCohomologicalDimension.subsingleton_H_projective_of_card_le _ q hq (by omega)
  obtain ⟨N, hN⟩ := CoherentProjectiveGlobalGeneration.exists_eventual_generatingSections M j
  have down : ∀ n : ℕ,
      (∃ G : (M ⊗ coordinateHyperplaneTwist (R := R) j (n : ℤ)).GeneratingSections, G.IsFiniteType) →
      ∃ G : (M ⊗ coordinateHyperplaneTwist (R := R) j (0 : ℤ)).GeneratingSections, G.IsFiniteType := by
    intro n
    induction n with
    | zero => exact id
    | succ n ih =>
      rintro ⟨G, hG⟩
      let : G.IsFiniteType := hG
      exact ih (ProjectiveCoordinateGeneratorDescent.exists_generatingSections_predecessor M j hall n G)
  obtain ⟨G, hG⟩ := down N (hN N le_rfl)
  let : G.IsFiniteType := hG
  let e : M ⊗ coordinateHyperplaneTwist (R := R) j (0 : ℤ) ≅ M := ρ_ M
  exact ⟨G.ofEpi e.hom, inferInstance⟩

end EnvelopeProperty.ProjectiveRegularityGlobalGeneration
