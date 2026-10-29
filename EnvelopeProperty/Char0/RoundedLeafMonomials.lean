import EnvelopeProperty.Char0.FamilyLeafMonomials
import EnvelopeProperty.Char0.RoundedSncIdealSheaf

/-! # The SAME intrinsic rounded SNC ideal on actual original resolution leaves -/

noncomputable section
namespace EnvelopeProperty.Char0
open AlgebraicGeometry CategoryTheory Module Ideal
open scoped Classical
universe u

variable {k A : Type u} [Field k] [CommRing A] {Y : Scheme.{u}}

/-- Actual adapted ORIGINAL boundary ideals transport the SAME whole
intrinsic rounded SNC ideal to the SAME actual leaf coordinates, for EVERY q. -/
theorem idealOfSpecSheaf_comap_rounded_monomial
    (f : Y ⟶ Spec (.of k)) [Smooth f]
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor)
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (d : F.ι → ℕ)
    (hJF : J = ∏ i, F.component i ^ d i) (q : ℚ)
    (x : Y) (U : Y.affineOpens) {n : ℕ} (v : Fin n → Γ(Y, U.1))
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hc : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤)
    (α : Spec (.of A) ⟶ Y) (hαU : Set.range α ⊆ (U.1 : Set Y))
    (vA : Fin n → A) (cA : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hFA : ∀ i, idealOfSpecSheaf ((F.component i.1).comap α) = span {vA (cA i)}) :
    idealOfSpecSheaf ((RoundedSncIdealSheaf.rounded J hJ q).comap α) =
      span {∏ i, vA (cA i) ^ ⌊q * (d i.1 : ℚ)⌋₊} := by
  exact idealOfSpecSheaf_comap_monomial_factor
    (RoundedSncIdealSheaf.rounded J hJ q) (fun i => F.component i.1) U
    (fun i => v (c i)) (fun i => ⌊q * (d i.1 : ℚ)⌋₊) hc
    (RoundedSncIdealSheaf.rounded_ideal f J hJ hF d hJF q x U v c hc habsent)
    α hαU (fun i => vA (cA i)) hFA

variable {R : Type u} [CommRing R] [Algebra k R]
variable [Algebra k A] [Algebra R A] [IsScalarTower k R A]

/-- Actual original SNC Jacobian neighborhoods derive actual leaf etale
coordinates, FULL original Jacobian monomials, and SAME intrinsic rounded
ideal monomials for ALL q from ONE original global SNC presentation. -/
theorem exists_leaf_coordinates_rounded_jacobian_monomials [IsDomain A]
    (π : Y ⟶ Spec (.of R)) (α : Spec (.of A) ⟶ Y) [IsOpenImmersion α]
    (hπ : α ≫ π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (J : (Spec (.of R)).IdealSheafData) (hJ : (J.comap π).IsIdealOfSncDivisor)
    (F : Scheme.DivisorFamily Y) (hF : F.IsSnc) (d : F.ι → ℕ)
    (hJF : J.comap π = ∏ i, F.component i ^ d i) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)))]
    (x : Y) (W : Y.affineOpens)
    (hW : SNCJacobianNeighbourhood (k := k) π F n J x W)
    (hαW : Set.range α ⊆ (W.1 : Set Y))
    (z : Fin n → R) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    ∃ (vA : Fin n → A) (hvA : (MvPolynomial.aeval (R := k) vA).toRingHom.Etale)
      (cA : {i : F.ι // x ∈ (F.component i).support} → Fin n),
      Function.Injective cA ∧
      (∀ i, idealOfSpecSheaf ((F.component i.1).comap α) = span {vA (cA i)}) ∧
      ∃ a : {i : F.ι // x ∈ (F.component i).support} → ℕ,
        affineRelativeJacobianIdeal (R := R) (etaleDifferentialBasis vA hvA) =
          span {∏ i, vA (cA i) ^ a i} ∧
        ∀ q : ℚ, idealOfSpecSheaf
            ((RoundedSncIdealSheaf.rounded (J.comap π) hJ q).comap α) =
          span {∏ i, vA (cA i) ^ ⌊q * (d i.1 : ℚ)⌋₊} := by
  obtain ⟨vA, hvA, cA, hcinjA, hFA, _, aA, uA, _, hJacA⟩ :=
    exists_leaf_coordinates_jacobian_monomial π α hπ J F n x W hW hαW z hz
  obtain ⟨U, v, _, _, c, _, hc, habsent, _, _, s, hWs, _⟩ := hW
  have hαU : Set.range α ⊆ (U.1 : Set Y) := by
    intro y hy
    have hyW := hαW hy
    rw [hWs] at hyW
    exact Y.basicOpen_le s hyW
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine ⟨vA, hvA, cA, hcinjA, hFA, aA, ?_, fun q => ?_⟩
  · rw [affineRelativeJacobianIdeal_eq_span z hz,
      relativeDifferentialDet_eq_etaleJacobian z hz vA hvA, hJacA,
      Ideal.span_singleton_mul_left_unit uA.isUnit]
  · exact idealOfSpecSheaf_comap_rounded_monomial f (J.comap π) hJ F hF d hJF q
      x U v c hc habsent α hαU vA cA hFA

end EnvelopeProperty.Char0
