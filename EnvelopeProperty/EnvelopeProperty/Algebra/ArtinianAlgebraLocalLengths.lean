import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import EnvelopeProperty.Algebra.FiniteAlgebraPrincipalDegrees

/-! # Actual Artinian algebra lengths and NONflat residue-weighted principal degrees -/
open Module Submodule LinearMap IsLocalRing
noncomputable section
universe u
namespace EnvelopeProperty.ArtinianAlgebraLocalLengths
variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

private theorem covBy_length_restrictScalars {p q : Submodule S M} (h : p ⋖ q) :
    Module.length R q = Module.length R p + Module.length R (ResidueField S) := by
  let f : p →ₗ[S] q := inclusion h.le
  have hsimple : IsSimpleModule S (q ⧸ f.range) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  rw [eq_maximalIdeal hm] at e
  let g : q →ₗ[S] ResidueField S := e.comp f.range.mkQ
  have hf : Function.Injective f := inclusion_injective _
  have hg : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
  have hex : Function.Exact f g := exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
  exact Module.length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R)
    hf hg hex

/-- Length along ANY original coefficient ring is the actual local length
times the original coefficient length of the SAME target residue field.
The coefficient ring need not be local or a field. -/
theorem length_restrictScalars_of_finiteLength (hM : IsFiniteLength S M) :
    Module.length R M = Module.length S M * Module.length R (ResidueField S) := by
  obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
  rw [← length_compositionSeries s hs_bot hs_top]
  suffices ∀ j, Module.length R (s j) = j * Module.length R (ResidueField S) by
    rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
    exact Module.length_top.symm
  intro j
  induction j using Fin.induction with
  | zero => rw [← RelSeries.head, hs_bot]; simp
  | succ j hj =>
    simpa [hj, add_one_mul] using covBy_length_restrictScalars (R := R) (s.step j)

omit [IsLocalRing S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] in
/-- The ENTIRE original Artinian algebra has actual length equal to the sum
of the true residue-weighted lengths at ALL of its ORIGINAL primes. -/
theorem length_eq_sum_local_length_mul_residue_length [IsArtinianRing S] :
    Module.length R S = ∑ᶠ p : PrimeSpectrum S,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) *
        Module.length R (ResidueField (Localization.AtPrime p.asIdeal)) := by
  let : Fintype (PrimeSpectrum S) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype,
    ((PrimeSpectrum.toPiLocalizationEquiv S).restrictScalars R).toLinearEquiv.length_eq,
    Module.length_pi_of_fintype]
  apply Finset.sum_congr rfl
  intro p _
  let : IsLocalRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p.asIdeal) p.asIdeal
  exact length_restrictScalars_of_finiteLength (R := R)
    (M := Localization.AtPrime p.asIdeal)
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end EnvelopeProperty.ArtinianAlgebraLocalLengths

namespace EnvelopeProperty.ArtinianAlgebraLocalLengths
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [IsDomain B] [Module.Finite R B]

omit [IsDomain B] in
/-- The SAME original principal quotient is genuinely Artinian, internally
derived from its nonzero original annihilator, without flatness or normality. -/
theorem principalQuotient_isArtinian (a : R) (ha : a ≠ 0) :
    IsArtinianRing (B ⧸ Ideal.span {algebraMap R B a}) := by
  let I : Ideal B := Ideal.span {algebraMap R B a}
  have hfinite : IsFiniteLength R (B ⧸ I) :=
    OneDimensionalFiniteLattices.finiteLength_of_nonzero_annihilator a ha (by
      intro q
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
      have hz : Ideal.Quotient.mk I (algebraMap R B a * b) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (I.mul_mem_right b (Ideal.subset_span (Set.mem_singleton _)))
      simpa only [map_mul, Algebra.smul_def,
        IsScalarTower.algebraMap_apply R B (B ⧸ I), Ideal.Quotient.algebraMap_eq] using hz)
  exact isArtinian_of_tower R
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2

/-- TRUE residue-weighted local principal degrees of the SAME original
finite algebra sum to the actual generic rank times original principal order.
No flatness, normality, local-basis or residue-degree certificate is supplied. -/
theorem sum_principal_local_degrees_eq_rank_mul_ord
    (hinj : Function.Injective (algebraMap R B)) (a : R) (ha : a ≠ 0) :
    (∑ᶠ p : PrimeSpectrum (B ⧸ Ideal.span {algebraMap R B a}),
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) *
        Module.length R (ResidueField (Localization.AtPrime p.asIdeal))) =
      (Module.finrank R B : ℕ∞) * Ring.ord R a := by
  let := principalQuotient_isArtinian (B := B) a ha
  rw [← length_eq_sum_local_length_mul_residue_length]
  exact FiniteAlgebraPrincipalDegrees.length_principalQuotient_eq_rank_mul_ord hinj a ha

end EnvelopeProperty.ArtinianAlgebraLocalLengths
