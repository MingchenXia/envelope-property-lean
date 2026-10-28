import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.CharP.Basic

/-! Pure normalization of actual multilinear maps. Geometric ordered-product
closure and evaluation identities must be proved by their actual consumers. -/

noncomputable section
universe u v w x y
namespace EnvelopeProperty.Cartier.DeligneIllusieAlternatingNormalization

variable {k : Type u} [Field k] {R : Type v} [CommRing R] (β : k →+* R)

/-- Inversion takes place in the original field; its actual image acts even over zero R. -/
def normalizationScalar (q : ℕ) : R := β ((q.factorial : k)⁻¹)

section Characteristic
variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem factorial_cast_ne_zero (q : ℕ) (hq : q < p) : (q.factorial : k) ≠ 0 := by
  intro h
  have hpq : p ≤ q := (Fact.out : p.Prime).dvd_factorial.mp
    ((CharP.cast_eq_zero_iff k p q.factorial).mp h)
  exact (Nat.not_le_of_lt hq) hpq

theorem normalizationScalar_mul_factorial (q : ℕ) (hq : q < p) :
    normalizationScalar β q * (q.factorial : R) = 1 := by
  rw [normalizationScalar, ← map_natCast β q.factorial, ← map_mul,
    inv_mul_cancel₀ (factorial_cast_ne_zero (k := k) p q hq), map_one]
end Characteristic

variable {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type x} [AddCommGroup N] [Module R N] (q : ℕ)

/-- Genuine alternation comes from the existing finite involution proof, including in char two. -/
def normalizedAlternatization (μ : MultilinearMap R (fun _ : Fin q => M) N) :
    M [⋀^Fin q]→ₗ[R] N :=
  normalizationScalar β q • MultilinearMap.alternatization μ

theorem normalizedAlternatization_apply (μ : MultilinearMap R (fun _ : Fin q => M) N)
    (v : Fin q → M) :
    normalizedAlternatization β q μ v = normalizationScalar β q •
      ∑ σ : Equiv.Perm (Fin q), Equiv.Perm.sign σ • μ.domDomCongr σ v := by
  rw [normalizedAlternatization, AlternatingMap.smul_apply,
    MultilinearMap.alternatization_apply]

theorem comp_normalizedAlternatization {P : Type y} [AddCommGroup P] [Module R P]
    (L : N →ₗ[R] P) (μ : MultilinearMap R (fun _ : Fin q => M) N) :
    L.compAlternatingMap (normalizedAlternatization β q μ) =
      normalizedAlternatization β q (L.compMultilinearMap μ) := by
  rw [normalizedAlternatization, LinearMap.compAlternatingMap_smul]
  exact (congrArg (fun a => normalizationScalar β q • a)
    (LinearMap.compMultilinearMap_alternatization L μ)).symm

theorem normalizedAlternatization_closed {P : Type y} [AddCommGroup P] [Module R P]
    (L : N →ₗ[R] P) (μ : MultilinearMap R (fun _ : Fin q => M) N)
    (hμ : L.compMultilinearMap μ = 0) :
    L.compAlternatingMap (normalizedAlternatization β q μ) = 0 := by
  rw [comp_normalizedAlternatization, hμ]
  simp only [normalizedAlternatization, map_zero, smul_zero]

/-- This is generic linear evaluation; it does not assert an actual Cech/AW evaluation premise. -/
theorem normalizedAlternatization_recovery (p : ℕ) [Fact p.Prime] [CharP k p]
    (hq : q < p) {P : Type y} [AddCommGroup P] [Module R P]
    (L : N →ₗ[R] P) (μ : MultilinearMap R (fun _ : Fin q => M) N)
    (a : M [⋀^Fin q]→ₗ[R] P) (hμ : L.compMultilinearMap μ = a.toMultilinearMap) :
    L.compAlternatingMap (normalizedAlternatization β q μ) = a := by
  rw [normalizedAlternatization, LinearMap.compAlternatingMap_smul,
    ← LinearMap.compMultilinearMap_alternatization, hμ,
    AlternatingMap.coe_alternatization, Fintype.card_fin]
  ext v
  change normalizationScalar β q • (q.factorial • a v) = a v
  rw [← Nat.cast_smul_eq_nsmul R, ← mul_smul,
    normalizationScalar_mul_factorial β p q hq, one_smul]

end EnvelopeProperty.Cartier.DeligneIllusieAlternatingNormalization

universe u₁ v₁
namespace EnvelopeProperty.Cartier.DeligneIllusieAlternatingNormalization

variable {k : Type u} [Field k] {R : Type v} [CommRing R] {S : Type y} [CommRing S]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type x} [AddCommGroup N] [Module R N]
  {M' : Type u₁} [AddCommGroup M'] [Module S M']
  {N' : Type v₁} [AddCommGroup N'] [Module S N']

/-- Generic raw-map compatibility implies normalized restriction, without geometric claims. -/
theorem normalizedAlternatization_naturality
    (ρ : R →+* S) (βR : k →+* R) (βS : k →+* S) (hβ : ρ.comp βR = βS)
    (q : ℕ) (f : M →ₛₗ[ρ] M') (g : N →ₛₗ[ρ] N')
    (μR : MultilinearMap R (fun _ : Fin q => M) N)
    (μS : MultilinearMap S (fun _ : Fin q => M') N')
    (hμ : ∀ v, g (μR v) = μS (fun i => f (v i))) (v : Fin q → M) :
    g (normalizedAlternatization βR q μR v) =
      normalizedAlternatization βS q μS (fun i => f (v i)) := by
  rw [normalizedAlternatization_apply, normalizedAlternatization_apply, g.map_smulₛₗ]
  have hc : ρ (normalizationScalar βR q) = normalizationScalar βS q :=
    RingHom.congr_fun hβ ((q.factorial : k)⁻¹)
  rw [hc]
  apply congrArg (fun z : N' => normalizationScalar βS q • z)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun z : N' => (Equiv.Perm.sign σ : ℤ) • z)
    (hμ (fun i => v (σ i)))

end EnvelopeProperty.Cartier.DeligneIllusieAlternatingNormalization
