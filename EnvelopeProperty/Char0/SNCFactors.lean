/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCMonomials
import Hironaka.Scheme.Snc.ParameterAlgebra
import Hironaka.Algebra.Local.Regular
import Hironaka.Scheme.Snc.Family
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.BlowUp.ProductCenter
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Resolution.Algebraic.Snc.SncInvertible

/-!
# Monomial stalks of factors of a principalized product

The actual total-transform ideal of principalization is a product of powers of SNC component
ideals. Factors of this product are invertible; their stalk generators divide the boundary
monomial and hence are themselves monomials. This supplies the stalk step of the simultaneous
ideal monomialization adapter.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory IsLocalRing Ideal
open scoped Classical

universe u

variable {X : Scheme.{u}}

/-- Powers of the components missing the point are units; the remaining stalk product is the
actual boundary monomial in its assigned regular parameters. -/
theorem prod_pow_stalkIdeal_eq_span {ι : Type*} [Fintype ι] (E : ι → X.IdealSheafData)
    {x : X} {n : ℕ} {z : Fin n → X.presheaf.stalk x} (e : ι → ℕ)
    (c : {i : ι // x ∈ (E i).support} → Fin n)
    (hc : ∀ i, (E i.1).stalkIdeal x = span {z (c i)}) :
    ∏ i, (E i).stalkIdeal x ^ e i = span {∏ i, z (c i) ^ e i.1} := by
  classical
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : ι => x ∈ (E i).support)
    (fun i => (E i).stalkIdeal x ^ e i)]
  have hmissing : ∏ i : {i : ι // x ∉ (E i).support}, (E i.1).stalkIdeal x ^ e i.1 = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ i.2,
      Ideal.top_pow, Ideal.one_eq_top]
  rw [hmissing, mul_one]
  calc (∏ i : {i : ι // x ∈ (E i).support}, (E i.1).stalkIdeal x ^ e i.1) =
      ∏ i, span {z (c i) ^ e i.1} := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hc i, Ideal.span_singleton_pow]
    _ = span {∏ i, z (c i) ^ e i.1} := Ideal.prod_span_singleton _ _

/-- Every factor of an actual SNC total-transform product is a boundary monomial at every
stalk. The exponents are bounded by those of the total product in the same boundary family. -/
theorem exists_stalk_monomial_factor {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {A B : X.IdealSheafData}
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc) (e : F.ι → ℕ)
    (hprod : A * B = ∏ i, F.component i ^ e i) (x : X) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), IsRegularSystemOfParameters z ∧
      ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).stalkIdeal x = span {z (c i)}) ∧
        ∃ a : {i : F.ι // x ∈ (F.component i).support} → ℕ,
          (∀ i, a i ≤ e i.1) ∧ A.stalkIdeal x = span {∏ i, z (c i) ^ a i} := by
  have := isRegularLocalRing_stalk f x
  obtain ⟨n, z, hz, c, hcinj, hc⟩ := hF.2 x
  have hAB : (A * B).IsIdealOfSncDivisor := ⟨F, e, hF, hprod⟩
  have hA : A.IsInvertible :=
    (Scheme.IdealSheafData.IsInvertible.of_mul (hAB.isInvertible f)).1
  obtain ⟨g, _, hAg⟩ := hA.exists_ne_zero_stalkIdeal_eq_span x
  have htotal : (A * B).stalkIdeal x = span {∏ i, z (c i) ^ e i.1} := by
    rw [hprod, Scheme.IdealSheafData.stalkIdeal_finset_prod]
    simp_rw [Scheme.IdealSheafData.stalkIdeal_pow]
    exact prod_pow_stalkIdeal_eq_span F.component e c hc
  have hmem : (∏ i, z (c i) ^ e i.1) ∈ A.stalkIdeal x := by
    have hle : A.stalkIdeal x * B.stalkIdeal x ≤ A.stalkIdeal x := Ideal.mul_le_left
    apply hle
    rw [← Scheme.IdealSheafData.stalkIdeal_mul, htotal]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hdiv : g ∣ ∏ i, z (c i) ^ e i.1 := by
    apply Ideal.mem_span_singleton.mp
    rw [← hAg]
    exact hmem
  obtain ⟨a, ha, hassoc⟩ := exists_exponents_associated_of_dvd_monomial
    (fun i => z (c i)) (fun i => prime_of_parameters hz.1.symm hz.2 (c i))
    (fun i => e i.1) hdiv
  refine ⟨n, z, hz, c, hcinj, hc, a, ha, ?_⟩
  exact hAg.trans (Ideal.span_singleton_eq_span_singleton.mpr hassoc)

end EnvelopeProperty.Char0
