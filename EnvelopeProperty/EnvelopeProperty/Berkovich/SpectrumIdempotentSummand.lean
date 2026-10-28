import EnvelopeProperty.Berkovich.IdempotentSummand
import EnvelopeProperty.Berkovich.SpectrumLocalization
import EnvelopeProperty.Berkovich.SpectrumFibreHomIso
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Whole analytic fibre pieces of genuine idempotent summands

The actual quotient by `1-e` has exactly the original seminorm points with
value one on `e`. The comparison preserves every original function and every
coefficient. Localizing the canonical completed tensor map identifies the
actual local rings, so all local-length times residue-degree multiplicities
are retained, including nonreduced factors.
-/

open scoped TensorProduct Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E]

/-- A seminorm takes only the values zero and one on a genuine idempotent. -/
theorem val_idempotent_ne_zero_iff {e : E} (he : IsIdempotentElem e) (y : Spectrum E) :
    y.val e ≠ 0 ↔ y.val e = 1 := by
  have h := IsIdempotentElem.iff_eq_zero_or_one.mp (he.map y.val)
  constructor
  · exact fun hn => h.resolve_left hn
  · exact fun hy => hy ▸ one_ne_zero

/-- The original idempotent piece is both open and closed in the entire original spectrum. -/
theorem isClopen_setOf_val_idempotent_eq_one {e : E} (he : IsIdempotentElem e) :
    IsClopen {y : Spectrum E | y.val e = 1} := by
  refine ⟨isClosed_eq (continuous_abs e) continuous_const, ?_⟩
  convert isOpen_setOf_val_ne_zero e using 1
  ext y
  exact (val_idempotent_ne_zero_iff he y).symm

/-- The entire quotient spectrum is the actual clopen piece where the idempotent is one. -/
def idempotentSummandHomeomorph {e : E} (he : IsIdempotentElem e) :
    Spectrum (IdempotentSummand.Summand e) ≃ₜ {y : Spectrum E // y.val e = 1} := by
  letI := IdempotentSummand.isLocalization he
  exact (Away.homeomorph (IdempotentSummand.Summand e) e).trans
    (Homeomorph.setCongr (by ext y; exact val_idempotent_ne_zero_iff he y))

/-- Every original function has its exact quotient value under the whole comparison. -/
theorem idempotentSummandHomeomorph_apply_val {e : E} (he : IsIdempotentElem e)
    (y : Spectrum (IdempotentSummand.Summand e)) (a : E) :
    (idempotentSummandHomeomorph he y).1.val a =
      y.val (IdempotentSummand.quotient (R := R) e a) := rfl

/-- Every actual coefficient is preserved by the same whole point comparison. -/
theorem idempotentSummandHomeomorph_base {e : E} (he : IsIdempotentElem e)
    (y : Spectrum (IdempotentSummand.Summand e)) :
    comap (algebraMap R E) (idempotentSummandHomeomorph he y).1 =
      comap (algebraMap R (IdempotentSummand.Summand e)) y :=
  comap_algHom_base (IdempotentSummand.quotient (R := R) e) y

/-- Restricting the genuine whole comparison gives exactly the entire original fibre piece. -/
def idempotentSummandFibreEquiv {e : E} (he : IsIdempotentElem e) (x : Spectrum R) :
    Fibre (B := IdempotentSummand.Summand e) x ≃
      {y : Fibre (B := E) x // y.1.val e = 1} where
  toFun y := ⟨⟨(idempotentSummandHomeomorph he y.1).1,
    (idempotentSummandHomeomorph_base he y.1).trans y.2⟩,
      (idempotentSummandHomeomorph he y.1).2⟩
  invFun y := ⟨(idempotentSummandHomeomorph he).symm ⟨y.1.1, y.2⟩, by
    have h := idempotentSummandHomeomorph_base (R := R) he
      ((idempotentSummandHomeomorph he).symm ⟨y.1.1, y.2⟩)
    rw [Homeomorph.apply_symm_apply] at h
    exact h.symm.trans y.1.2⟩
  left_inv y := Subtype.ext ((idempotentSummandHomeomorph he).symm_apply_apply y.1)
  right_inv y := by
    refine Subtype.ext (Subtype.ext ?_)
    change ((idempotentSummandHomeomorph he)
      ((idempotentSummandHomeomorph he).symm ⟨y.1.1, y.2⟩)).1 = y.1.1
    exact congrArg Subtype.val
      ((idempotentSummandHomeomorph he).apply_symm_apply ⟨y.1.1, y.2⟩)

private def localizationAtPrimeEquiv {K C D : Type*} [Field K]
    [CommRing C] [CommRing D] [Algebra K C] [Algebra K D]
    [Algebra C D] [IsScalarTower K C D] (M : Submonoid C)
    [IsLocalization M D] (p : Ideal D) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap C D)) ≃ₐ[K] Localization.AtPrime p := by
  letI : IsLocalization.AtPrime (Localization.AtPrime p)
      (p.comap (algebraMap C D)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime p) p
  exact (IsLocalization.algEquiv
    (p.comap (algebraMap C D)).primeCompl
    (Localization.AtPrime (p.comap (algebraMap C D)))
    (Localization.AtPrime p)).restrictScalars K

private local instance summand_ker_isPrime {C D : Type*} [CommRing C] [CommRing D]
    [Algebra C D] {x : Spectrum C} {y : Spectrum D}
    (hy : comap (algebraMap C D) y = x) :
    (RingHom.ker (fibreHom hy)).IsPrime := RingHom.ker_isPrime _

/-- The actual quotient map retains every full nonreduced fibre weight. -/
theorem fibreNormMult_idempotentSummand [Module.Finite R E]
    {e : E} (he : IsIdempotentElem e)
    (y : Spectrum (IdempotentSummand.Summand e)) :
    fibreNormMult R (idempotentSummandHomeomorph he y).1 = fibreNormMult R y := by
  let Q := IdempotentSummand.Summand e
  let := IdempotentSummand.finite (R := R) e
  let := IdempotentSummand.isLocalization he
  let f : E →ₐ[R] Q := IdempotentSummand.quotient (R := R) e
  let x := comap (algebraMap R Q) y
  let C := H x ⊗[R] E
  let D := H x ⊗[R] Q
  let g : C →ₐ[H x] D := Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f
  let : Algebra C D := g.toRingHom.toAlgebra
  let : IsScalarTower (H x) C D :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      change g ((algebraMap (H x) C) c) = algebraMap (H x) D c
      exact g.commutes c)
  let : IsLocalization (Submonoid.powers ((1 : H x) ⊗ₜ[R] e)) D := by
    have h := IsLocalization.tensorProduct_tensorProduct_right R (H x)
      (Submonoid.powers e) Q (by
        ext a
        rfl)
    simpa only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] using h
  let p : Ideal D := RingHom.ker (fibreHom (rfl : comap (algebraMap R Q) y = x))
  have hp : p.IsPrime := RingHom.ker_isPrime _
  let := hp
  have hy : comap (algebraMap R E) (comap f.toRingHom y) = x :=
    comap_algHom_base f y
  have hker : p.comap (algebraMap C D) = RingHom.ker (fibreHom hy) := by
    ext q
    change fibreHom (rfl : comap (algebraMap R Q) y = x) (g q) = 0 ↔
      fibreHom hy q = 0
    rw [fibreHom_algHom_of_comap f (rfl : comap (algebraMap R Q) y = x)]
    exact (map_eq_zero_iff _ (H.map_injective f.toRingHom rfl))
  change fibreNormMult R (comap f.toRingHom y) = fibreNormMult R y
  rw [fibreNormMult_eq_localFinrank_of_comap hy,
    fibreNormMult_eq_localFinrank_of_comap (rfl : comap (algebraMap R Q) y = x)]
  exact (localFinrank_congr (K := H x) hker.symm).trans
    (localizationAtPrimeEquiv (K := H x)
      (Submonoid.powers ((1 : H x) ⊗ₜ[R] e)) p).toLinearEquiv.finrank_eq

end EnvelopeProperty.Berkovich.Spectrum
