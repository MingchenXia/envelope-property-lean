import EnvelopeProperty.Vanishing.ArithmeticOriginalSmoothWitt

/-! # A dimension-preserving Witt stage containing the already descended line coefficients

An actual finite coefficient enlargement is localized to a produced smooth
arithmetic base before choosing the closed point. All its coefficients remain
in the resulting actual Witt stage. This permits the original-line descent
to precede the closed-point choice.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth

open ProjBerk ArithmeticProjectiveOriginalFamily ArithmeticSmoothProjectiveOriginalFamily
open ArithmeticSmoothCoefficientBase ArithmeticProjectiveWittFamily

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [CharZero k] {N : ℕ} {X : Scheme.{u}}
  (j : X ⟶ NativeProjectiveScheme k N) [IsClosedImmersion j] (extra : Finset k)

/-- Any actual finite coefficient stage of the original n-smooth family
produces a genuine Witt stage containing all its coefficients. Smoothness
of the integer base and the large-characteristic point are constructed. -/
theorem exists_relativeDimension_witt_stage_over (S : Subalgebra ℤ k)
    (hRS : coefficientBase j extra ≤ S) (hFT : Algebra.FiniteType ℤ S)
    (n : ℕ) (hn : SmoothOfRelativeDimension n (scalarProjection j extra S hRS))
    (bound : ℕ) (hnb : n ≤ bound) :
    ∃ D : ProducedStage j extra bound, S ≤ D.base ∧
      SmoothOfRelativeDimension n D.baseProjection ∧
      SmoothOfRelativeDimension n D.wittProjection ∧
      SmoothOfRelativeDimension n D.residueProjection ∧ n < D.prime := by
  let : Algebra.FiniteType ℤ S := hFT
  obtain ⟨s, hs, _, hBase, hFT₀, _, _, _, hSS₀⟩ :=
    exists_smooth_localizedCoefficientRing S
  let S₀ := localizedCoefficientRing S s hs
  have hRS₀ : coefficientBase j extra ≤ S₀ := hRS.trans hSS₀
  have hn₀ : SmoothOfRelativeDimension n (scalarProjection j extra S₀ hRS₀) :=
    relativeDimension_scalarProjection j extra S S₀ hRS hSS₀ n hn
  let : Algebra.FiniteType ℤ S₀ := hFT₀
  have hSmooth : Smooth (scalarProjection j extra S₀ hRS₀) := by
    let : SmoothOfRelativeDimension n (scalarProjection j extra S₀ hRS₀) := hn₀
    exact SmoothOfRelativeDimension.smooth n _
  obtain ⟨r, hr, m, ell, hp, hBound, hc, hf, lifted, hred, -⟩ :=
    exists_produced_witt_point S₀ bound
  let D : ProducedStage j extra bound :=
    ⟨S₀, hRS₀, hBase, hFT₀, hSmooth, r, hr, m, ell, hp, hBound, hc, hf, lifted, hred⟩
  have hS₀D : S₀ ≤ D.base := le_localizedCoefficientRing S₀ r hr
  have hbase : SmoothOfRelativeDimension n D.baseProjection :=
    relativeDimension_scalarProjection j extra S₀ D.base hRS₀ hS₀D n hn₀
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have hwitt : SmoothOfRelativeDimension n D.wittProjection :=
    MorphismProperty.pullback_snd D.baseProjection
      (Spec.map (CommRingCat.ofHom D.coefficientLift)) hbase
  have hresidue : SmoothOfRelativeDimension n D.residueProjection :=
    MorphismProperty.pullback_snd D.baseProjection
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.point.asIdeal))) hbase
  exact ⟨D, hSS₀.trans hS₀D, hbase, hwitt, hresidue, hnb.trans_lt hBound⟩

end EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth
