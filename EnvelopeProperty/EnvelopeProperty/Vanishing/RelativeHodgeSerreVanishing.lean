import EnvelopeProperty.Vanishing.HodgeSerreVanishing

/-! # Absolute Hodge Serre endpoints with ampleness over the original affine base

The differential sheaves are still relative to the original field. Actual
relative ampleness over any Noetherian affine base supplies the Serre endpoint.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
universe u
namespace EnvelopeProperty.Vanishing.RelativeHodgeSerreVanishing
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- One threshold kills every positive cohomology group of all exterior
degrees up to the smooth relative dimension, for all larger ample powers. -/
theorem exists_bound {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g₀ : X ⟶ Spec (.of R)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple g₀ L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i : Fin (n + 1), ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
          (q + 1)) := by
  let M : Fin (n + 1) → X.Modules := fun i => exteriorCotangentSheaf f i.val
  let (i : Fin (n + 1)) : (M i).IsQuasicoherent :=
    SmoothExteriorFiniteType.isQuasicoherent f n i.val
  let (i : Fin (n + 1)) : (M i).IsFiniteType :=
    SmoothExteriorFiniteType.isFiniteType f n i.val
  exact SchemeAmpleCoherentSerreVanishing.exists_uniform_sheafCohomology_bound g₀ L hL M

/-- Actual smooth differential sheaves have eventually zero Hodge diagonals
in every total degree strictly above the relative dimension.  The bound is
independent of both the total degree and the exterior degree. -/
theorem exists_upper_diagonal_bound {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g₀ : X ⟶ Spec (.of R)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple g₀ L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ t : ℕ, n < t → ∀ i : Fin (n + 1),
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
          (t - i.val)) := by
  obtain ⟨N, hN⟩ := exists_bound f g₀ n L hL
  refine ⟨N, fun m hm t ht i => ?_⟩
  have hi := i.isLt
  have he : t - i.val = (t - i.val - 1) + 1 := by omega
  rw [he]
  exact hN m hm i (t - i.val - 1)

end EnvelopeProperty.Vanishing.RelativeHodgeSerreVanishing
