import EnvelopeProperty.Local.ProjectionExistenceProof

/-!
# Constructing a global separating Noether normalization

The existing Noether-coordinate twists and differential perturbations construct
a finite injective generically etale map from an actual polynomial algebra to
every finite-type domain over a perfect field. No generic separability or chosen
normalization is an input. This is the global normalization needed for curve
chains, without the point-adapted localization in the projection theorem.
-/

open scoped Polynomial
noncomputable section

namespace EnvelopeProperty.FcSeparatingNormalization

open MvPolynomial KaehlerDifferential

/-- Every finite-type domain over a perfect field has a constructed GLOBAL finite
injective generically etale Noether normalization, in every characteristic. -/
theorem exists_finite_separating_normalization_with_fractionMap
    (F A : Type*) [Field F] [PerfectField F] [CommRing A] [IsDomain A]
    [Algebra F A] [Algebra.FiniteType F A] :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) F →ₐ[F] A),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsGenericallyEtale φ.toRingHom ∧
      ∃ ψ : FractionRing (MvPolynomial (Fin n) F) →+* FractionRing A,
        (∀ p, ψ (algebraMap _ (FractionRing (MvPolynomial (Fin n) F)) p) =
          algebraMap A (FractionRing A) (φ p)) ∧
        (letI : Algebra (FractionRing (MvPolynomial (Fin n) F)) (FractionRing A) := ψ.toAlgebra
         Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin n) F)) (FractionRing A)) := by
  classical
  obtain ⟨n, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg F A
  have hdim : ringKrullDim A = n :=
    ringKrullDim_eq_of_isIntegral_of_injective g.toRingHom hgint hginj
  let τ : Fin n → A := fun i => g (X i)
  have hgτ : ∀ G, g G = aeval τ G := fun G => by
    rw [MvPolynomial.aeval_unique g]
    rfl
  have hτ : ∀ x : A, IsIntegral (Algebra.adjoin F (Set.range τ)) x :=
    isIntegral_of_ringHom_isIntegral g.toRingHom hgint _ (fun G => by
      change g G ∈ _
      rw [hgτ, ← MvPolynomial.aeval_range]
      exact ⟨G, rfl⟩)
  let L := FractionRing A
  obtain ⟨a, _ha, hspanOrIndep⟩ := exists_forall_mem_spanOrIndep
    (k := F) (L := L) (⊤ : Ideal A) top_ne_bot (0 : Fin n → A)
  have hspanOrIndep' : SpanOrIndep (K := L)
      (fun i => D F L (algebraMap A L (a i))) := by
    simpa only [Pi.zero_apply, zero_add] using hspanOrIndep
  let Pred : ℕ → Prop := fun m => 2 ≤ m ∧ ringExpChar F ∣ m
  have hPred : ∀ N, ∃ m, N ≤ m ∧ Pred m := by
    intro N
    have he : 1 ≤ ringExpChar F := by
      rcases expChar_is_prime_or_one F (ringExpChar F) with he | he
      · exact he.one_lt.le
      · omega
    exact ⟨(N + 2) * ringExpChar F, by nlinarith, by nlinarith, dvd_mul_left _ _⟩
  obtain ⟨f, hfPred, hf⟩ := exists_forall_isIntegral_adjoin_twist Pred hPred τ a Finset.univ hτ
  let y : Fin n → A := fun i => τ i ^ f i - a i
  have hyint : ∀ x : A, IsIntegral (Algebra.adjoin F (Set.range y)) x := by
    have hyeq : (fun i : Fin n => if i ∈ Finset.univ then τ i ^ f i - a i else τ i) = y := by
      funext i
      simp only [Finset.mem_univ, ite_true, y]
    rw [hyeq] at hf
    exact hf
  let B := MvPolynomial (Fin n) F
  let φ : B →ₐ[F] A := aeval y
  have hφint : φ.toRingHom.IsIntegral := fun x =>
    isIntegralElem_aeval_of_isIntegral_adjoin y (hyint x)
  have hφinj : Function.Injective φ :=
    injective_of_isIntegral_of_ringKrullDim_eq φ.toRingHom hφint hdim
  have hφfin : φ.toRingHom.Finite := by
    algebraize [φ.toRingHom]
    have : Algebra.IsIntegral B A := ⟨hφint⟩
    have : IsScalarTower F B A := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    have : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType F B A
    exact Algebra.IsIntegral.finite
  have hsepD : CharZero F ∨ Submodule.span L
      ((fun p => D F L (algebraMap A L (φ p))) '' Set.range X) = ⊤ := by
    obtain ⟨p, hp⟩ := CharP.exists F
    rcases CharP.char_is_prime_or_zero F p with hpp | hp0
    · right
      have : Fact p.Prime := ⟨hpp⟩
      have hq : ringExpChar F = p := ringExpChar.eq F p
      have : CharP L p := charP_of_injective_algebraMap (algebraMap F L).injective p
      have hD (i : Fin n) : D F L (algebraMap A L (y i)) =
          -D F L (algebraMap A L (a i)) := by
        change D F L (algebraMap A L (τ i ^ f i - a i)) = _
        rw [map_sub, map_sub, map_pow, Derivation.leibniz_pow,
          show (f i : ℕ) • ((algebraMap A L (τ i)) ^ (f i - 1) •
              D F L (algebraMap A L (τ i))) = 0 by
            rw [← Nat.cast_smul_eq_nsmul L,
              (CharP.cast_eq_zero_iff L p (f i)).mpr (hq ▸ (hfPred i).2), zero_smul],
          zero_sub]
      have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
      have : Algebra.EssFiniteType F L := .comp F A L
      have := isAlgebraic_adjoin_range_fractionRing (k := F) (L := L) τ hτ
      obtain ⟨hfd, hrk⟩ := finiteDimensional_and_finrank_le F L
        (fun i => algebraMap A L (τ i))
      have hwspan := span_eq_top_of_spanOrIndep _ hspanOrIndep' hrk
      rw [eq_top_iff, ← hwspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hh : -D F L (algebraMap A L (a i)) ∈ Submodule.span L
          ((fun p => D F L (algebraMap A L (φ p))) '' Set.range X) := by
        rw [← hD i]
        exact Submodule.subset_span ⟨X i, ⟨i, rfl⟩, by
          change D F L (algebraMap A L (φ (X i))) = _
          rw [show φ (X i) = y i from MvPolynomial.aeval_X y i]⟩
      simpa only [neg_neg, SetLike.mem_coe] using Submodule.neg_mem _ hh
    · left
      subst hp0
      exact (CharP.charP_zero_iff_charZero F).mp hp
  let K := FractionRing B
  have hle : nonZeroDivisors B ≤ (nonZeroDivisors A).comap φ.toRingHom :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφinj
  let ψKL : K →+* L := IsLocalization.map L φ.toRingHom hle
  let : Algebra K L := ψKL.toAlgebra
  have hKL : ∀ p, algebraMap K L (algebraMap B K p) = algebraMap A L (φ p) := fun p =>
    IsLocalization.map_eq hle p
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply F B K, hKL, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have : Algebra.FormallyEtale K L :=
    formallyEtale_of_span_D F φ.toRingHom hφfin hKL (Set.range X) hsepD
  obtain ⟨h, hh, het⟩ := exists_ne_zero_etale_awayMap φ.toRingHom hφfin K L hKL
  exact ⟨n, φ, hφinj, hφfin, ⟨h, hh, het⟩, ψKL, hKL, inferInstance⟩

/-- The actual global finite separating normalization, retaining the simpler
generically etale interface when no explicit fraction-field map is needed. -/
theorem exists_finite_injective_genericallyEtale_normalization
    (F A : Type*) [Field F] [PerfectField F] [CommRing A] [IsDomain A]
    [Algebra F A] [Algebra.FiniteType F A] :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) F →ₐ[F] A),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsGenericallyEtale φ.toRingHom := by
  obtain ⟨n, φ, hinj, hfin, het, _⟩ :=
    exists_finite_separating_normalization_with_fractionMap F A
  exact ⟨n, φ, hinj, hfin, het⟩

end EnvelopeProperty.FcSeparatingNormalization
