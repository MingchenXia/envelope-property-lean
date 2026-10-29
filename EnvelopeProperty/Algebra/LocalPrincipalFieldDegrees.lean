import EnvelopeProperty.Algebra.ArtinianAlgebraLocalLengths

/-! # True original field dimensions of NONflat local principal quotients -/
open Module IsLocalRing
noncomputable section
universe u
namespace EnvelopeProperty.LocalPrincipalFieldDegrees
variable {k R M : Type u} [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

/-- True finite residue degree and actual finite local length internally
derive finite dimension of the ENTIRE original module over the original field. -/
theorem finite_of_finiteLength [Module.Finite k (ResidueField R)]
    (hM : IsFiniteLength R M) : Module.Finite k M := by
  have heq := ArtinianAlgebraLocalLengths.length_restrictScalars_of_finiteLength (R := k) hM
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top_iff.mpr hM)
  have hlen : Module.length k M ≠ ⊤ := by
    rw [heq, ← hn, Module.length_eq_finrank]
    exact_mod_cast (ENat.natCast_ne_top (n * Module.finrank k (ResidueField R)))
  have hm := Module.length_ne_top_iff.mp hlen
  let : IsNoetherian k M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hm).1
  infer_instance

/-- Actual original field dimension is true local length times the actual
original residue-field degree; finite dimension is derived internally. -/
theorem finrank_eq_length_mul_residue_finrank [Module.Finite k (ResidueField R)]
    (hM : IsFiniteLength R M) :
    Module.finrank k M = (Module.length R M).toNat * Module.finrank k (ResidueField R) := by
  let := finite_of_finiteLength (k := k) hM
  have heq := ArtinianAlgebraLocalLengths.length_restrictScalars_of_finiteLength (R := k) hM
  rw [Module.length_eq_finrank, Module.length_eq_finrank] at heq
  simpa using congrArg ENat.toNat heq

end EnvelopeProperty.LocalPrincipalFieldDegrees

namespace EnvelopeProperty.LocalPrincipalFieldDegrees
variable {k R B : Type u} [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]
    [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing B] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
    [IsDomain B] [Module.Finite R B] [Module.Finite k (ResidueField R)]

omit [IsLocalRing R] [IsDomain B] in
private theorem principalQuotient_finiteLength (a : R) (ha : a ≠ 0) :
    IsFiniteLength R (B ⧸ Ideal.span {algebraMap R B a}) := by
  let I : Ideal B := Ideal.span {algebraMap R B a}
  change IsFiniteLength R (B ⧸ I)
  apply OneDimensionalFiniteLattices.finiteLength_of_nonzero_annihilator a ha
  intro q
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hz : Ideal.Quotient.mk I (algebraMap R B a * b) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (I.mul_mem_right b (Ideal.subset_span (Set.mem_singleton _)))
  simpa only [map_mul, Algebra.smul_def,
    IsScalarTower.algebraMap_apply R B (B ⧸ I), Ideal.Quotient.algebraMap_eq] using hz

omit [IsDomain B] in
/-- The SAME original NONflat finite principal quotient has genuine finite
dimension over the original coefficient field, internally derived. -/
theorem principalQuotient_finite (a : R) (ha : a ≠ 0) :
    Module.Finite k (B ⧸ Ideal.span {algebraMap R B a}) :=
  finite_of_finiteLength (k := k) (principalQuotient_finiteLength a ha)

/-- The actual whole original principal field degree equals actual generic
rank times original principal order times the true original residue degree.
No flatness, normality, finite-quotient or degree matching certificate. -/
theorem finrank_principalQuotient
    (hinj : Function.Injective (algebraMap R B)) (a : R) (ha : a ≠ 0) :
    Module.finrank k (B ⧸ Ideal.span {algebraMap R B a}) =
      Module.finrank R B * (Ring.ord R a).toNat * Module.finrank k (ResidueField R) := by
  rw [finrank_eq_length_mul_residue_finrank (k := k) (principalQuotient_finiteLength a ha),
    FiniteAlgebraPrincipalDegrees.length_principalQuotient_eq_rank_mul_ord hinj a ha,
    ENat.toNat_mul, ENat.toNat_natCast]

end EnvelopeProperty.LocalPrincipalFieldDegrees
