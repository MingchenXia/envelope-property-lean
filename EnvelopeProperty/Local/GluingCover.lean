/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.Gluing
import EnvelopeProperty.Local.StrictExhaustion

/-!
# Regularizability is local

FHX Proposition 5.20(2) (`prop:gluing`): a function of logarithmic growth, upper semicontinuous,
that is regularizable on principal opens covering `Y`, is regularizable on `Y`. Apply the gluing
hull inequality (Proposition 5.20(1)) with `Z = ∅` on `Ỹ = Y × 𝔸¹` to `u ∘ p + log|w|` and conclude
with the hull criterion (Lemma 5.19).
-/

open scoped NNReal ENNReal Topology

noncomputable section

namespace EnvelopeProperty

open Berk Polynomial

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] [Countable k] [WuRegularization.{u, v} k]
  {A : Type v} [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
  [IsIntegrallyClosed A]

/-- **Regularizability is local** (FHX Proposition 5.20(2)). -/
theorem IsRegularizable.of_cover_principal {u : Berk k A → EReal}
    (husc : UpperSemicontinuous u) (hlog : HasLogGrowth u)
    (hcover : ∀ x : Berk k A, ∃ g : A, g ≠ 0 ∧ x.val g ≠ 0 ∧
      IsRegularizable fun y => u (awayComap g y)) : IsRegularizable u := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_isStrictExhaustion (k := k) (A := A[X])
  -- `u` is not identically `-∞`
  have hne : ∃ x, u x ≠ ⊥ := by
    obtain ⟨g, -, -, ⟨⟨w, hw⟩, -⟩⟩ := hcover triv
    exact ⟨_, hw⟩
  -- the function `ũ = u ∘ p + log|w|`
  obtain ⟨g0, C0, hg0⟩ := hlog
  have hutop : ∀ x, u x ≠ ⊤ := fun x => ne_top_of_le_ne_top
    (EReal.add_ne_top (g0.eval_ne_top x) (EReal.coe_ne_top C0)) (hg0 x)
  have hlog' : HasLogGrowth u := ⟨g0, C0, hg0⟩
  set ũ : Berk k A[X] → EReal := fun z => u (proj z) + logAbs (X : A[X]) z with hũ
  have hũusc : UpperSemicontinuous ũ :=
    upperSemicontinuous_add_of_ne_top (husc.comp continuous_proj)
      (continuous_logAbs _).upperSemicontinuous (fun z => hutop _) (fun z => logAbs_ne_top _ _)
  have hũlog : HasLogGrowth ũ :=
    (hlog'.comp_comap (Polynomial.CAlgHom (R := k) (A := A))).add (hasLogGrowth_logAbs _)
  -- the cover of `Ỹ` by the principal opens `Ỹ_g`
  have hcover' : ∀ z : Berk k A[X], (∃ f ∈ ({1} : Finset A[X]), z.val f ≠ 0) →
      ∃ g : A[X], g ≠ 0 ∧ z.val g ≠ 0 ∧ IsRegularizable fun w => ũ (awayComap g w) := by
    intro z _
    obtain ⟨g, hg0, hzg, hug⟩ := hcover (proj z)
    refine ⟨Polynomial.CAlgHom (R := k) (A := A) g, ?_, ?_, ?_⟩
    · simpa [Polynomial.CAlgHom] using hg0
    · simpa [proj_val_apply] using hzg
    · have hCg : (Polynomial.CAlgHom (R := k) (A := A) g) ≠ 0 := by
        simpa [Polynomial.CAlgHom] using hg0
      have := isDomain_localizationAway hCg
      -- first summand
      have h1 : IsRegularizable fun w : Berk k (Localization.Away
          (Polynomial.CAlgHom (R := k) (A := A) g)) =>
          u (awayComap g (comap (awayPolyMap g) w)) := by
        refine hug.comp_comap (awayPolyMap g) ?_
        obtain ⟨⟨y₀, hy₀⟩, -⟩ := hug
        set y := awayComap g y₀
        have hyC : (gauss y 1).val (Polynomial.CAlgHom (R := k) (A := A) g) ≠ 0 := by
          change (gauss y 1).val (C g) ≠ 0
          rw [gauss_val_C]
          exact awayComap_val_ne_zero g y₀
        refine ⟨awayLift _ (gauss y 1) hyC, ?_⟩
        rw [← proj_awayComap_C, awayComap_awayLift, proj_gauss]
        exact hy₀
      -- second summand
      have h2 : IsRegularizable fun w : Berk k (Localization.Away
          (Polynomial.CAlgHom (R := k) (A := A) g)) =>
          logAbs (X : A[X]) (awayComap (Polynomial.CAlgHom (R := k) (A := A) g) w) := by
        have hs := isRegularizable_finsetSup_fsTerm
          (k := k) (A := Localization.Away (Polynomial.CAlgHom (R := k) (A := A) g))
          (s := {(algebraMap A[X] _ X, (1 : ℚ), (0 : ℚ))}) (by simp)
          ⟨triv, by
            rw [Finset.sup_singleton]
            simp only [fsTerm, Rat.cast_one, EReal.coe_one, one_mul, Rat.cast_zero,
              EReal.coe_zero, add_zero]
            rw [Ne, logAbs_eq_bot_iff, triv_val_of_ne_zero]
            · exact one_ne_zero
            · intro h
              rw [IsLocalization.to_map_eq_zero_iff
                (M := Submonoid.powers (Polynomial.CAlgHom (R := k) (A := A) g))
                (Localization.Away (Polynomial.CAlgHom (R := k) (A := A) g))
                (powers_le_nonZeroDivisors_of_noZeroDivisors hCg)] at h
              exact Polynomial.X_ne_zero h⟩
        refine hs.congr fun w => ?_
        rw [Finset.sup_singleton]
        simp [fsTerm]
      refine (h1.add h2).congr fun w => ?_
      simp only [hũ, proj_awayComap_C]
  -- the hull criterion
  refine IsRegularizable.of_hullIneq_add_smul u husc hlog' hne ρ hρ.2.1 hρ.1.ne_top
    (fun c hc => (hρ.1.smul hc).upperSemicontinuous) ?_
  intro c hc K hK z hz
  exact gluing_hullIneq hũusc hũlog {1} hcover' hρ hc hK hz ⟨1, by simp, by simp⟩

end EnvelopeProperty
