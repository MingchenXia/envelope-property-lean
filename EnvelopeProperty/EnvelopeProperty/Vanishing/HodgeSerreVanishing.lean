import EnvelopeProperty.AlgGeom.SchemeAmpleCoherentSerreVanishing
import EnvelopeProperty.Vanishing.SmoothExteriorFiniteType
import EnvelopeProperty.Vanishing.FrobeniusIteration

/-! # Eventual vanishing above the actual positive Hodge diagonal

The eventual endpoints are unconditional. The final criterion explicitly
leaves the geometric one-step comparison as a separate premise; it does not
identify that comparison with the Deligne--Illusie decomposition itself.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.HodgeSerreVanishing

open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

/-- One threshold kills every positive cohomology group of all exterior
degrees up to the smooth relative dimension, for all larger ample powers. -/
theorem exists_bound {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i : Fin (n + 1), ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
          (q + 1)) := by
  let M : Fin (n + 1) → X.Modules := fun i => exteriorCotangentSheaf f i.val
  let (i : Fin (n + 1)) : (M i).IsQuasicoherent :=
    SmoothExteriorFiniteType.isQuasicoherent f n i.val
  let (i : Fin (n + 1)) : (M i).IsFiniteType :=
    SmoothExteriorFiniteType.isFiniteType f n i.val
  exact SchemeAmpleCoherentSerreVanishing.exists_uniform_sheafCohomology_bound f L hL M

/-- Actual smooth differential sheaves have eventually zero Hodge diagonals
in every total degree strictly above the relative dimension.  The bound is
independent of both the total degree and the exterior degree. -/
theorem exists_upper_diagonal_bound {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ t : ℕ, n < t → ∀ i : Fin (n + 1),
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
          (t - i.val)) := by
  obtain ⟨N, hN⟩ := exists_bound f n L hL
  refine ⟨N, fun m hm t ht i => ?_⟩
  have hi := i.isLt
  have he : t - i.val = (t - i.val - 1) + 1 := by omega
  rw [he]
  exact hN m hm i (t - i.val - 1)

/-- The geometric descent step and the independently proved Serre endpoint
imply vanishing at every positive power on an actual Hodge diagonal.

This is a conditional criterion, not a proof of Kodaira vanishing from DI:
the projection/connection, hypercohomology and field-Frobenius comparisons
must still produce `hdescent`. In particular `hdescent` is not an instance
or an axiom asserting the desired vanishing. -/
theorem upper_diagonal_of_descent {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L)
    {p : ℕ} (hp : 2 ≤ p) (t : ℕ) (ht : n < t)
    (hdescent : ∀ m : ℕ, 0 < m →
      (∀ i : Fin (n + 1), Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L (p * m) ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
          (t - i.val))) →
      ∀ i : Fin (n + 1), Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
          (t - i.val)))
    {m : ℕ} (hm : 0 < m) (i : Fin (n + 1)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
        (t - i.val)) := by
  apply FrobeniusIteration.of_eventually
    (fun m => ∀ i : Fin (n + 1), Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
        (t - i.val))) hp hdescent ?_ hm i
  obtain ⟨N, hN⟩ := exists_upper_diagonal_bound f n L hL
  exact ⟨N, fun m hm => hN m hm t ht⟩

end EnvelopeProperty.Vanishing.HodgeSerreVanishing
