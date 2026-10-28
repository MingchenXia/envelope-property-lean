/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Projective.BiProj

/-!
# Actual bihomogeneous representatives at two unit coordinates

Every polynomial admits one bihomogeneous representative preserving both
of two given algebra maps that send the selected x and y coordinates to
one. The representative is constructed by monomial induction; addition
is homogenized by multiplying by powers of those actual unit coordinates.
-/

open MvPolynomial
noncomputable section
namespace EnvelopeProperty
universe u
variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] {M M' : ℕ}

/-- Two actual coordinate-unit evaluations share a genuinely constructed
bihomogeneous representative of every polynomial. -/
theorem exists_bihomogeneous_pair_of_map_coordinates_eq_one
    (φ : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] R)
    (ψ : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k →ₐ[k] S)
    (i : Fin (M + 1)) (l : Fin (M' + 1))
    (hφx : φ (X (Sum.inl i)) = 1) (hφy : φ (X (Sum.inr l)) = 1)
    (hψx : ψ (X (Sum.inl i)) = 1) (hψy : ψ (X (Sum.inr l)) = 1)
    (P : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k) :
    ∃ (p : ℕ × ℕ) (F : MvPolynomial (Fin (M + 1) ⊕ Fin (M' + 1)) k),
      F.IsWeightedHomogeneous (biWeight M M') p ∧ φ F = φ P ∧ ψ F = ψ P := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    exact ⟨Finsupp.weight (biWeight M M') α, monomial α c,
      isWeightedHomogeneous_monomial _ _ _ rfl, rfl, rfl⟩
  | add P Q ihP ihQ =>
    obtain ⟨p, F, hF, eφF, eψF⟩ := ihP
    obtain ⟨q, G, hG, eφG, eψG⟩ := ihQ
    have hF' : (F * X (Sum.inl i) ^ q.1 * X (Sum.inr l) ^ q.2).IsWeightedHomogeneous
        (biWeight M M') (p + q) := by
      convert (hF.mul ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inl i)).pow q.1)).mul
        ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inr l)).pow q.2) using 1
      cases p
      cases q
      simp [biWeight, Prod.add_def]
    have hG' : (G * X (Sum.inl i) ^ p.1 * X (Sum.inr l) ^ p.2).IsWeightedHomogeneous
        (biWeight M M') (p + q) := by
      convert (hG.mul ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inl i)).pow p.1)).mul
        ((isWeightedHomogeneous_X k (biWeight M M') (Sum.inr l)).pow p.2) using 1
      cases p
      cases q
      simp [biWeight, Prod.add_def, add_comm]
    refine ⟨p + q,
      F * X (Sum.inl i) ^ q.1 * X (Sum.inr l) ^ q.2 +
        G * X (Sum.inl i) ^ p.1 * X (Sum.inr l) ^ p.2,
      hF'.add hG', ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, hφx, hφy, one_pow, mul_one, eφF, eφG]
    · simp only [map_add, map_mul, map_pow, hψx, hψy, one_pow, mul_one, eψF, eψG]

end EnvelopeProperty
