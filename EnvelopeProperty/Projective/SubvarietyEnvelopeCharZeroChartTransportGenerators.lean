/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.SubvarietyEnvelopeCharZeroCoefficients
import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsCone
import EnvelopeProperty.Alterations.Geometry.ProperSteinProjectiveCechGradedPresentation

/-!
# Actual homogeneous generators of the same whole canonical cone ideal

Noetherianity supplies genuine homogeneous members of the canonical
representative. The original parameter exchange produces entire original
ambient polynomials generating the same actual cone ideal exactly.
Their degrees are unrestricted; the uniform degree estimate is separate.
-/

open scoped Polynomial

noncomputable section

namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals

open AlgebraicGeometry ProjBerk

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- Noetherianity selects actual homogeneous members spanning the same
whole original homogeneous ideal, with their membership retained. -/
theorem exists_finset_homogeneous_generators {R : Type u} [CommRing R] [IsNoetherianRing R]
    {n : ℕ} (H : HomogeneousIdeal (ProjectiveGrading R n)) :
    ∃ G : Finset (MvPolynomial (Fin (n + 1)) R),
      (∀ P ∈ G, P ∈ H ∧ ∃ e : ℕ, P.IsHomogeneous e) ∧
      Ideal.span (G : Set (MvPolynomial (Fin (n + 1)) R)) = H.toIdeal := by
  exact Alterations.Geometry.ProperSteinProjectiveCech.homogeneousModule_finiteGenerators
    (ProjectiveGrading R n) H.toIdeal H.isHomogeneous

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The whole actual canonical cone ideal has true finite polynomial
generators homogeneous in `x`, with actual canonical representative
membership. No uniform degree bound or approximation is an input. -/
theorem exists_finset_coneIdeal_homogeneous_generators
    (K : (familyScheme X).IdealSheafData) :
    ∃ G : Finset (MvPolynomial (Fin (M + 1)) k)[X],
      (∀ F ∈ G, ∃ e : ℕ, ∀ ℓ : ℕ, (F.coeff ℓ).IsHomogeneous e) ∧
      (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk = coneIdeal X K ∧
      ∀ F ∈ G, parameterEquiv F ∈ homogeneousConeRepresentative X K ∧
        ∃ e : ℕ, (parameterEquiv F).IsHomogeneous e := by
  classical
  obtain ⟨P, hP, hspan⟩ :=
    exists_finset_homogeneous_generators (homogeneousConeRepresentative X K)
  let G : Finset (MvPolynomial (Fin (M + 1)) k)[X] :=
    P.image (parameterEquiv (k := k) (M := M)).symm
  have hswapspan : Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X]) =
      (Ideal.span (P : Set (MvPolynomial (Fin (M + 1)) k[X]))).map
        (parameterEquiv (k := k) (M := M)).symm.toRingHom := by
    rw [Ideal.map_span]
    congr 1
    ext F
    simp [G]
  refine ⟨G, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨e, he⟩ := (hP p hp).2
    exact ⟨e, fun ℓ => parameterEquiv_symm_coeff_isHomogeneous he ℓ⟩
  · change (Ideal.span (G : Set (MvPolynomial (Fin (M + 1)) k)[X])).map X.coneMk.toRingHom = _
    rw [hswapspan, Ideal.map_map, hspan]
    rfl
  · intro F hF
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hF
    simpa only [AlgEquiv.apply_symm_apply] using hP p hp

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
