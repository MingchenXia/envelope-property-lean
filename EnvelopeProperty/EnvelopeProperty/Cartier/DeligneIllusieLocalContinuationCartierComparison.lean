import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationClosedness

/-! # Genuine lift arithmetic produces the original Cartier representative and boundary -/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCartierComparison

open FrobeniusLiftDifference
open scoped Classical

universe u

/-- An actual ring power-difference equation DERIVES an actual divisor in the native cotangent module. -/
theorem power_difference_divisor {C S : Type u} [CommRing C] [CommRing S] [Algebra C S]
    {p : ℕ} (x u y : S) (hu : (p : S)*u = y-x^p) :
    (p : S) • (x^(p-1) • KaehlerDifferential.D C S x + KaehlerDifferential.D C S u) =
      KaehlerDifferential.D C S y := by
  have hd : (p : S) • KaehlerDifferential.D C S u =
      KaehlerDifferential.D C S y - (p : S) • (x^(p-1) • KaehlerDifferential.D C S x) := by
    simpa only [Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, map_sub,
      Derivation.leibniz_pow, Nat.cast_smul_eq_nsmul, smul_assoc] using
      congrArg (KaehlerDifferential.D C S) hu
  rw [smul_add, hd]
  abel

variable {p : ℕ} {K B R S : Type u} [CommRing K] [CommRing B] [CommRing R] [CommRing S]
  [Algebra K B] [Fact p.Prime] [CharP K p] [CharP B p]

private theorem relativeFrobenius_source_apply (t : B) :
    (RelativeFrobenius.map (algebraMap K B) p).hom
        ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t) = t^p := by
  have h := congrArg (fun h : CommRingCat.of B ⟶ CommRingCat.of B => h.hom t)
    (RelativeFrobenius.sourceMap_map (algebraMap K B) p)
  exact h

/-- Quotient geometry and the ACTUAL source triangle internally produce actual power-difference lifts. -/
theorem exists_source_power_difference
    (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p)) (b : Reduction p S B)
    (f : R →+* S) (hf : ∀ r, b.map (f r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))
    (t : B) : ∃ r : R, ∃ x u : S,
      a.map r = (RelativeFrobenius.sourceMap (algebraMap K B) p).hom t ∧
      b.map x = t ∧ (p : S)*u = f r-x^p := by
  obtain ⟨r, hr⟩ := a.surjective ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t)
  obtain ⟨x, hx⟩ := b.surjective t
  have hzero : b.map (f r-x^p) = 0 := by
    rw [map_sub, hf, hr, relativeFrobenius_source_apply, map_pow, hx, sub_self]
  obtain ⟨u, hu⟩ := (b.kernel_iff (f r-x^p)).mp hzero
  exact ⟨r, x, u, hr, hx, hu⟩

variable {m : ℕ} (w : Fin m → B) (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale)

/-- The SAME native relative degree-zero map gives the ORIGINAL exact first exterior representative. -/
theorem native_differential_zero (z : B) :
    (RelativeEtaleDeRham.differential w hw p 0).hom
        (show RelativeEtaleDeRham.formModule (R := K) (B := B) p 0 from
          (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm z) =
      (show RelativeEtaleDeRham.formModule (R := K) (B := B) p 1 from
        (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (KaehlerDifferential.D K B z)) := by
  apply (exteriorPower.oneEquiv B (KaehlerDifferential K B)).injective
  exact (EtaleDeRham.differential_zero w hw z).trans
    ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).apply_symm_apply _).symm

variable {C : Type u} [CommRing C]
  [Algebra C K] [Algebra C S] [Algebra S B] [Algebra C B]
  [IsScalarTower C S B] [IsScalarTower C K B] [SMulCommClass K S B]
  [Algebra.FormallySmooth C S]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (hc : algebraMap C K = c.map) (hb : algebraMap S B = b.map)
  (f : R →+* S) (hf : ∀ r, b.map (f r) = (RelativeFrobenius.map (algebraMap K B) p).hom (a.map r))

attribute [local instance] DeligneIllusieLocalContinuationDividedFrobenius.coefficientAlgebra

/-- Every ACTUAL ring power-division witness gives the SAME original representative-independent divided value. -/
theorem divided_source_eq_of_power_difference (t : B) (r : R) (x u : S)
    (hr : a.map r = (RelativeFrobenius.sourceMap (algebraMap K B) p).hom t)
    (hx : b.map x = t) (hu : (p : S)*u = f r-x^p) :
    DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb f hf
        ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t) =
      t^(p-1) • KaehlerDifferential.D K B t + KaehlerDifferential.D K B (b.map u) := by
  have hη := power_difference_divisor (C := C) x u (f r) hu
  have hξ := DeligneIllusieLocalContinuationDividedFrobenius.divided_eq_of_lift
    c a b hc hb f hf r (x^(p-1) • KaehlerDifferential.D C S x + KaehlerDifferential.D C S u) hη
  rw [hr] at hξ
  calc
    DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb f hf
        ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t) =
        DeligneIllusieLocalContinuationDifferential.reduction (S := S) (B := B) C K
          (x^(p-1) • KaehlerDifferential.D C S x + KaehlerDifferential.D C S u) := hξ
    _ = t^(p-1) • KaehlerDifferential.D K B t + KaehlerDifferential.D K B (b.map u) := by
      change DeligneIllusieLocalContinuationClosedness.reductionSemilinear
        (C := C) (K := K) (S := S) (B := B)
        (x^(p-1) • KaehlerDifferential.D C S x + KaehlerDifferential.D C S u) = _
      rw [map_add, map_smulₛₗ, DeligneIllusieLocalContinuationClosedness.reductionSemilinear_D,
        DeligneIllusieLocalContinuationClosedness.reductionSemilinear_D, map_pow, hb, hx]

/-- The primitive in the actual Cartier comparison is DERIVED, never supplied as an input. -/
theorem exists_divided_source_primitive (t : B) : ∃ z : B,
    DeligneIllusieLocalContinuationDividedFrobenius.divided c a b hc hb f hf
        ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t) =
      t^(p-1) • KaehlerDifferential.D K B t + KaehlerDifferential.D K B z := by
  obtain ⟨r, x, u, hr, hx, hu⟩ := exists_source_power_difference a b.toReduction f hf t
  exact ⟨b.map u, divided_source_eq_of_power_difference c a b hc hb f hf t r x u hr hx hu⟩

variable (ι : C →+* R)
  (hι : ∀ r, a.map (ι r) = algebraMap K (RelativeFrobenius.twist (algebraMap K B) p) (c.map r))
  (hbase : ∀ r, f (ι r) = algebraMap C S r)

/-- The SAME actual native cotangent generator has the derived Cartier representative plus exact form. -/
theorem exists_cotangent_source_primitive (t : B) :
    letI : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
      Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
    ∃ z : B,
      DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap c a b hc hb f hf ι hι hbase
          (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
            ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t)) =
        t^(p-1) • KaehlerDifferential.D K B t + KaehlerDifferential.D K B z := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  obtain ⟨z, hz⟩ := exists_divided_source_primitive c a b hc hb f hf t
  refine ⟨z, ?_⟩
  rw [DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D]
  exact hz

/-- The original native one-form representative equals Cartier's original representative plus an ACTUAL d0 boundary. -/
theorem exists_oneForm_source_boundary (t : B) : ∃ z : B,
    DeligneIllusieLocalContinuationClosedness.oneFormMap c a b hc hb f hf ι hι hbase
        (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
          ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t)) =
      (show RelativeEtaleDeRham.formModule (R := K) (B := B) p 1 from
        t^(p-1) • (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (KaehlerDifferential.D K B t)) +
      (RelativeEtaleDeRham.differential w hw p 0).hom
        (show RelativeEtaleDeRham.formModule (R := K) (B := B) p 0 from
          (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm z) := by
  let : Module (RelativeFrobenius.twist (algebraMap K B) p) (KaehlerDifferential K B) :=
    Module.compHom _ (RelativeFrobenius.map (algebraMap K B) p).hom
  obtain ⟨z, hz⟩ := exists_divided_source_primitive c a b hc hb f hf t
  refine ⟨z, ?_⟩
  apply (exteriorPower.oneEquiv B (KaehlerDifferential K B)).injective
  rw [DeligneIllusieLocalContinuationClosedness.oneFormMap_apply,
    DeligneIllusieLocalContinuationDividedFrobenius.cotangentMap_D,
    native_differential_zero (p := p) w hw z]
  change _ = (exteriorPower.oneEquiv B (KaehlerDifferential K B))
    ((t^(p-1) • (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B t) +
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm (KaehlerDifferential.D K B z)) :
      ⋀[B]^1 (KaehlerDifferential K B))
  simpa only [map_add, map_smul, LinearEquiv.apply_symm_apply] using hz

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCartierComparison
