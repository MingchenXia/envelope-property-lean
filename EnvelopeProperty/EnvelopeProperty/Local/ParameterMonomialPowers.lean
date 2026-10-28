import EnvelopeProperty.Local.PLIdealParameterScaling

/-! # True finite parameter-monomial generators survive original ideal powers -/
open scoped Classical Polynomial Pointwise
noncomputable section
universe u
namespace EnvelopeProperty
variable {R : Type u} [CommRing R] {σ : Type*}

/-- Multiplication retains the SAME original coefficient forms and adds the
actual parameter exponents. -/
theorem parameterMonomial_mul (F G : MvPolynomial σ R) (e f : ℕ) :
    parameterMonomial F e * parameterMonomial G f = parameterMonomial (F * G) (e + f) := by
  simp only [parameterMonomial, map_mul, pow_add]
  ring

/-- Every original ideal power of a finite homogeneous parameter-monomial
span again has finite homogeneous parameter-monomial generators. All ideal
equalities are whole original ideals, without radical or integral closure. -/
theorem exists_parameterMonomial_span_pow
    (S : Finset (MvPolynomial σ R × ℕ))
    (hS : ∀ p ∈ S, ∃ d : ℕ, p.1.IsHomogeneous d) (m : ℕ) :
    ∃ T : Finset (MvPolynomial σ R × ℕ),
      (∀ p ∈ T, ∃ d : ℕ, p.1.IsHomogeneous d) ∧
      (Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
        (S : Set (MvPolynomial σ R × ℕ)))) ^ m =
        Ideal.span ((fun p => parameterMonomial p.1 p.2) ''
          (T : Set (MvPolynomial σ R × ℕ))) := by
  induction m with
  | zero =>
    refine ⟨{(1, 0)}, ?_, ?_⟩
    · intro p hp
      obtain rfl := Finset.mem_singleton.mp hp
      exact ⟨0, MvPolynomial.isHomogeneous_one _ _⟩
    · simp [parameterMonomial]
  | succ m ih =>
    obtain ⟨T, hT, hpow⟩ := ih
    let U := (T.product S).image fun pq => (pq.1.1 * pq.2.1, pq.1.2 + pq.2.2)
    refine ⟨U, ?_, ?_⟩
    · intro p hp
      obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
      obtain ⟨d,hd⟩ := hT a ha
      obtain ⟨e,he⟩ := hS b hb
      exact ⟨d+e, hd.mul he⟩
    · rw [pow_succ, hpow, Ideal.span_mul_span']
      congr 1
      ext z
      constructor
      · rintro ⟨a, ⟨p,hp,rfl⟩, b, ⟨q,hq,rfl⟩, rfl⟩
        refine ⟨(p.1*q.1,p.2+q.2), ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨(p,q), Finset.mem_product.mpr ⟨hp,hq⟩, rfl⟩
        · exact (parameterMonomial_mul _ _ _ _).symm
      · rintro ⟨p,hp,rfl⟩
        obtain ⟨⟨a,b⟩, hab,rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
        exact ⟨_, ⟨a,ha,rfl⟩, _, ⟨b,hb,rfl⟩, parameterMonomial_mul _ _ _ _⟩
end EnvelopeProperty
