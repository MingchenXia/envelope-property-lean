/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

noncomputable section
namespace EnvelopeProperty
universe u v

/-- An actual injection into a normal domain uniquely extends across the
original integral closure in the original fraction field. -/
theorem existsUnique_integralClosure_extension
    {A : Type u} [CommRing A] [IsDomain A]
    {B : Type v} [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    (φ : A →+* B) (hφ : Function.Injective φ) :
    ∃! ψ : integralClosure A (FractionRing A) →+* B,
      ψ.comp (algebraMap A (integralClosure A (FractionRing A))) = φ := by
  classical
  let C := integralClosure A (FractionRing A)
  let β : B →+* FractionRing B := algebraMap B (FractionRing B)
  have hβ : Function.Injective β := IsFractionRing.injective B (FractionRing B)
  let Φ : FractionRing A →+* FractionRing B := IsFractionRing.lift (A := A) (K := FractionRing A) (g := β.comp φ) (hβ.comp hφ)
  have hΦ : Φ.comp (algebraMap A (FractionRing A)) = β.comp φ :=
    RingHom.ext (fun a => IsFractionRing.lift_algebraMap (A := A) (K := FractionRing A) (g := β.comp φ) (hβ.comp hφ) a)
  let θ : C →+* FractionRing B := Φ.comp (algebraMap C (FractionRing A))
  have hmem (c : C) : θ c ∈ β.range := by
    have hint : IsIntegral B (Φ (c : FractionRing A)) :=
      IsIntegral.map_of_comp_eq φ Φ hΦ.symm c.2
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
  let e : B ≃+* β.range := RingEquiv.ofBijective β.rangeRestrict
    ⟨fun _ _ h => hβ (congrArg Subtype.val h), β.rangeRestrict_surjective⟩
  let ψ : C →+* B := e.symm.toRingHom.comp (θ.codRestrict β.range hmem)
  have hψ (c : C) : β (ψ c) = θ c :=
    congrArg Subtype.val (e.apply_symm_apply (θ.codRestrict β.range hmem c))
  have hψcoeff : ψ.comp (algebraMap A C) = φ := by
    ext a
    apply hβ
    rw [RingHom.comp_apply, hψ]
    change Φ (algebraMap A (FractionRing A) a) = β (φ a)
    exact RingHom.congr_fun hΦ a
  refine ⟨ψ, hψcoeff, ?_⟩
  intro χ hχ
  ext c
  obtain ⟨a, s, hs, hfrac⟩ := IsFractionRing.div_surjective A (c : FractionRing A)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap A (FractionRing A) s ≠ 0 :=
    fun h => hs0 (IsFractionRing.injective A (FractionRing A) (h.trans (map_zero _).symm))
  have hc : algebraMap A C s * c = algebraMap A C a := by
    apply Subtype.ext
    change algebraMap A (FractionRing A) s * (c : FractionRing A) =
      algebraMap A (FractionRing A) a
    rw [← hfrac]
    field_simp
  have hχeq := congrArg χ hc
  have hψeq := congrArg ψ hc
  have hχcoeff (x : A) : χ (algebraMap A C x) = φ x := RingHom.congr_fun hχ x
  have hψcoeff' (x : A) : ψ (algebraMap A C x) = φ x := RingHom.congr_fun hψcoeff x
  simp only [map_mul, hχcoeff] at hχeq
  simp only [map_mul, hψcoeff'] at hψeq
  exact mul_left_cancel₀ (fun h => hs0 (hφ (h.trans (map_zero _).symm))) (hχeq.trans hψeq.symm)

end EnvelopeProperty
