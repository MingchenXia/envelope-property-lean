import EnvelopeProperty.Cartier.RelativeFrobenius
import EnvelopeProperty.Cartier.PolynomialDifferentialKernel

/-!
# Relative Frobenius coefficients and polynomial degree-zero Cartier

The genuine native pushout retains every original base coefficient. Over an arbitrary
characteristic-p field, the kernel of the original polynomial universal differential is
the range of this relative Frobenius, without a perfection hypothesis or coefficient roots.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeFrobeniusCoefficient
open CategoryTheory Limits MvPolynomial
open scoped Classical
universe u

section General
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (p : ℕ) [Fact p.Prime] [CharP R p] [CharP B p]

/-- Every image under the actual relative Frobenius is killed by the SAME original
universal relative differential, over any characteristic-p coefficient ring. -/
theorem D_map_eq_zero (x : RelativeFrobenius.twist (algebraMap R B) p) :
    KaehlerDifferential.D R B ((RelativeFrobenius.map (algebraMap R B) p).hom x) = 0 := by
  have hx : x ∈ Subring.closure
      (Set.range (RelativeFrobenius.coefficientMap (algebraMap R B) p) ∪
        Set.range (RelativeFrobenius.sourceMap (algebraMap R B) p)) := by
    have ht : Subring.closure
        (Set.range (RelativeFrobenius.coefficientMap (algebraMap R B) p) ∪
          Set.range (RelativeFrobenius.sourceMap (algebraMap R B) p)) = ⊤ :=
      CommRingCat.closure_range_union_range_eq_top_of_isPushout
        (IsPushout.of_hasPushout (CommRingCat.ofHom (frobenius R p))
          (CommRingCat.ofHom (algebraMap R B)))
    rw [ht]
    trivial
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have h := congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of B => h.hom a)
        (RelativeFrobenius.coefficientMap_map (algebraMap R B) p)
      change (RelativeFrobenius.map (algebraMap R B) p).hom
        ((RelativeFrobenius.coefficientMap (algebraMap R B) p).hom a) = algebraMap R B a at h
      rw [h, Derivation.map_algebraMap]
    · have h := congrArg (fun h : CommRingCat.of B ⟶ CommRingCat.of B => h.hom b)
        (RelativeFrobenius.sourceMap_map (algebraMap R B) p)
      change (RelativeFrobenius.map (algebraMap R B) p).hom
        ((RelativeFrobenius.sourceMap (algebraMap R B) p).hom b) = b^p at h
      rw [h, Derivation.leibniz_pow, ← smul_assoc, nsmul_eq_mul, CharP.cast_eq_zero B p,
        zero_mul, zero_smul]
  | zero => rw [map_zero, map_zero]
  | one => rw [map_one, Derivation.map_one_eq_zero]
  | add a b ha hb hda hdb => rw [map_add, map_add, hda, hdb, add_zero]
  | neg a ha hda => rw [map_neg, map_neg, hda, neg_zero]
  | mul a b ha hb hda hdb =>
    rw [map_mul, Derivation.leibniz, hda, hdb, smul_zero, smul_zero, add_zero]

end General

section Polynomial
variable {k σ : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The actual relative Frobenius image contains every original divisible-exponent
monomial with its arbitrary SAME original coefficient, without taking a root of it. -/
theorem monomial_mem_range_of_dvd (d : σ →₀ ℕ) (c : k) (hd : ∀ i, p ∣ d i) :
    monomial d c ∈ (RelativeFrobenius.map (algebraMap k (MvPolynomial σ k)) p).hom.range := by
  rw [monomial_eq]
  apply Subring.mul_mem
  · refine ⟨(RelativeFrobenius.coefficientMap (algebraMap k (MvPolynomial σ k)) p).hom c, ?_⟩
    exact congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of (MvPolynomial σ k) => h.hom c)
      (RelativeFrobenius.coefficientMap_map (algebraMap k (MvPolynomial σ k)) p)
  · apply Subring.prod_mem
    intro i hi
    change (X i : MvPolynomial σ k) ^ d i ∈ _
    obtain ⟨m, hm⟩ := hd i
    rw [hm, mul_comm p m, pow_mul]
    exact RelativeFrobenius.pow_mem_range (algebraMap k (MvPolynomial σ k)) p (X i ^ m)

/-- Vanishing of ALL original polynomial partials produces membership in the genuine
relative Frobenius range, over arbitrary imperfect characteristic-p fields. -/
theorem mem_range_of_partials_eq_zero (f : MvPolynomial σ k)
    (hf : ∀ i, pderiv i f = 0) :
    f ∈ (RelativeFrobenius.map (algebraMap k (MvPolynomial σ k)) p).hom.range := by
  rw [f.as_sum]
  apply Subring.sum_mem
  intro d hd
  apply monomial_mem_range_of_dvd p
  intro i
  by_contra hi
  exact (mem_support_iff.mp hd)
    (PolynomialDifferentialKernel.coeff_eq_zero_of_not_dvd p f hf d i hi)

/-- The ENTIRE original universal polynomial differential kernel is the actual relative
Frobenius range. The original coefficient field need not be perfect. -/
theorem D_eq_zero_iff_mem_range (f : MvPolynomial σ k) :
    KaehlerDifferential.D k (MvPolynomial σ k) f = 0 ↔
      f ∈ (RelativeFrobenius.map (algebraMap k (MvPolynomial σ k)) p).hom.range := by
  constructor
  · intro hf
    exact mem_range_of_partials_eq_zero p f
      ((PolynomialDifferentialKernel.D_eq_zero_iff_partials_eq_zero f).mp hf)
  · rintro ⟨x, rfl⟩
    exact D_map_eq_zero p x

/-- The simultaneous kernel of EVERY actual standard partial is exactly the genuine
relative Frobenius image, with all original coefficients retained. -/
theorem partials_eq_zero_iff_mem_range (f : MvPolynomial σ k) :
    (∀ i, pderiv i f = 0) ↔
      f ∈ (RelativeFrobenius.map (algebraMap k (MvPolynomial σ k)) p).hom.range :=
  (PolynomialDifferentialKernel.D_eq_zero_iff_partials_eq_zero f).symm.trans
    (D_eq_zero_iff_mem_range p f)

end Polynomial
end EnvelopeProperty.Cartier.RelativeFrobeniusCoefficient
