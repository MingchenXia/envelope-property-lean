import EnvelopeProperty.Char0.NativeSNCMultiplierCriterion
import TranscendentalNakamaye.Pending.LocalHolomorphicMultiplierGermCovariance

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.NativeSNCIntegralTransport

open CategoryTheory AlgebraicGeometry BingWangEntropy Filter MeasureTheory
open TranscendentalNakamaye TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open SGPT.Okounkov NativeEtaleCoordinates NativeSNCMultiplierCriterion
open HironakaHolomorphicJetChartInvariance HironakaHolomorphicJetMonomialSpan
open scoped Topology ENNReal

variable {R : Type} [CommRing R]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (p : SchemeComplexPoint f) (t : Fin n → R)
  (ht : letI := affinePointFieldAlgebra f
    (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)

/-- The actual original test after the inverse of the internally derived native etale coordinates. -/
def adaptedTest (F : ComplexModel n → ℂ) : ComplexModel n → ℂ :=
  F ∘ (localCoordinates f n p t ht).invFun

/-- Every actual holomorphic test remains holomorphic in these actual original coordinates. -/
theorem adaptedTest_holomorphic (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (adaptedTest f n p t ht F) z :=
  holomorphic_comp _
    (local_invFun_holomorphic (localCoordinates f n p t ht) (localCoordinates_zero f n p t ht))
    (local_invFun_zero (localCoordinates f n p t ht) (localCoordinates_zero f n p t ht)) hF

/-- The ENTIRE inverse native coordinate germ map is the actual inverse-coordinate composite. -/
theorem adaptedTest_germ (F : ComplexModel n → ℂ)
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z) :
    (coordinateGermEquiv f n p t ht).symm (HolGerm.mk F hF) =
      HolGerm.mk (adaptedTest f n p t ht F) (adaptedTest_holomorphic f n p t ht F hF) := rfl

/-- The actual coordinate inverse preserves literal multiplier integrability, with actual
volume measure and internally derived holomorphic Jacobian units. -/
theorem multiplierIntegrableAt_adapted_iff
    {w : ComplexModel n → EReal} {F : ComplexModel n → ℂ} {c : ℝ}
    (hw : QuasiPlurisubharmonicAt w 0) :
    MultiplierIntegrableAt (fun z => w ((localCoordinates f n p t ht).invFun z)) c
      (adaptedTest f n p t ht F) 0 volume ↔ MultiplierIntegrableAt w c F 0 volume := by
  change MultiplierIntegrableAt (fun z => w ((localCoordinates f n p t ht).invFun z)) c
    (fun z => F ((localCoordinates f n p t ht).invFun z)) 0 volume ↔
      MultiplierIntegrableAt w c F 0 volume
  simpa only [localCoordinates_zero] using
    LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff
      (localCoordinates f n p t ht) hw

include ht in
/-- Whole ORIGINAL centered-coordinate weight and Jacobian ideals give rounded ORIGINAL
ideal membership for EVERY native analytic test, after actual inverse-coordinate measure
transport. No adapted-test matching, integral-equivalence, unit or monomial certificate is
an input. The two whole original monomial ideal identities are the natural SNC inputs. -/
theorem multiplierIntegrableAt_iff_original_rounded_ideal {s : ℕ}
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    (a d : Fin n → ℕ)
    (hspanG : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      Ideal.span {coefficientGerm f n p (∏ i, centeredOriginal f n p t i ^ a i)})
    {J : ComplexModel n → ℂ}
    (hJ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ J z)
    (hspanJ : Ideal.span {HolGerm.mk J hJ} =
      Ideal.span {coefficientGerm f n p (∏ i, centeredOriginal f n p t i ^ d i)})
    {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hw : QuasiPlurisubharmonicAt (generatorLog G) 0) {c : ℝ} (hc : 0 < c) :
    MultiplierIntegrableAt (generatorLog G) c (fun z => F z * J z) 0 volume ↔
      HolGerm.mk F hF ∈ Ideal.span {coefficientGerm f n p
        (∏ i, centeredOriginal f n p t i ^ roundedOrder (fun j => (a j : ℝ)) d c i)} := by
  let E := coordinateGermEquiv f n p t ht
  let GA : Fin s → ComplexModel n → ℂ := fun i => adaptedTest f n p t ht (G i)
  let JA := adaptedTest f n p t ht J
  let FA := adaptedTest f n p t ht F
  let hGA := fun i => adaptedTest_holomorphic f n p t ht (G i) (hG i)
  let hJA := adaptedTest_holomorphic f n p t ht J hJ
  let hFA := adaptedTest_holomorphic f n p t ht F hF
  have hmono (q : Fin n → ℕ) : E (∏ i, coordinateGerm i ^ q i) =
      coefficientGerm f n p (∏ i, centeredOriginal f n p t i ^ q i) :=
    coordinateGermEquiv_monomial f n p t ht q
  have hGAspan : Ideal.span (Set.range fun i => HolGerm.mk (GA i) (hGA i)) =
      Ideal.span {∏ i, coordinateGerm i ^ a i} := by
    calc
      _ = (Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i))).map E.symm.toRingHom := by
        rw [Ideal.map_span, ← Set.range_comp]
        apply congrArg Ideal.span
        apply congrArg Set.range
        funext i
        exact (adaptedTest_germ f n p t ht (G i) (hG i)).symm
      _ = _ := by
        rw [hspanG, Ideal.map_span, Set.image_singleton, ← hmono a]
        exact congrArg (fun x => Ideal.span {x}) (E.symm_apply_apply _)
  have hJAspan : Ideal.span {HolGerm.mk JA hJA} =
      Ideal.span {∏ i, coordinateGerm i ^ d i} := by
    calc
      _ = (Ideal.span {HolGerm.mk J hJ}).map E.symm.toRingHom := by
        rw [Ideal.map_span, Set.image_singleton]
        exact congrArg (fun x => Ideal.span {x}) (adaptedTest_germ f n p t ht J hJ).symm
      _ = _ := by
        rw [hspanJ, Ideal.map_span, Set.image_singleton, ← hmono d]
        exact congrArg (fun x => Ideal.span {x}) (E.symm_apply_apply _)
  have hwcomp : generatorLog GA =
      fun z => generatorLog G ((localCoordinates f n p t ht).invFun z) := by
    funext z
    rfl
  have hcov : MultiplierIntegrableAt (generatorLog GA) c (fun z => FA z * JA z) 0 volume ↔
      MultiplierIntegrableAt (generatorLog G) c (fun z => F z * J z) 0 volume := by
    rw [hwcomp]
    simpa only [FA, JA, adaptedTest, Function.comp_def] using
      multiplierIntegrableAt_adapted_iff f n p t ht (F := fun z => F z * J z) (c := c) hw
  have hcrit := multiplierIntegrableAt_generatorLog_mul_iff GA hGA a d hGAspan hJA hJAspan hFA hc
  have hdiv : (∏ i, coordinateGerm i ^ roundedOrder (fun j => (a j : ℝ)) d c i) ∣
      HolGerm.mk FA hFA ↔
      HolGerm.mk F hF ∈ Ideal.span {coefficientGerm f n p
        (∏ i, centeredOriginal f n p t i ^ roundedOrder (fun j => (a j : ℝ)) d c i)} := by
    rw [← adaptedTest_germ f n p t ht F hF, Ideal.mem_span_singleton,
      ← hmono (roundedOrder (fun j => (a j : ℝ)) d c)]
    change _ ∣ E.symm (HolGerm.mk F hF) ↔ _
    have hmap : E (∏ i, coordinateGerm i ^ roundedOrder (fun j => (a j : ℝ)) d c i) ∣
        E (E.symm (HolGerm.mk F hF)) ↔
        (∏ i, coordinateGerm i ^ roundedOrder (fun j => (a j : ℝ)) d c i) ∣
          E.symm (HolGerm.mk F hF) := map_dvd_iff E
    simpa only [E.apply_symm_apply] using hmap.symm
  exact hcov.symm.trans (hcrit.trans hdiv)


/-- The literal full-coordinate orders of the original finite active SNC component family. -/
def coordinateOrder {m : ℕ} {κ : Type*} [Fintype κ]
    (ι : κ → Fin m) (a : κ → ℕ) (j : Fin m) : ℕ :=
  ∑ i ∈ (Finset.univ.filter fun i => ι i = j), a i

private theorem coordinateOrder_prod {m : ℕ} {κ M : Type*} [Fintype κ] [CommMonoid M]
    (ι : κ → Fin m) (a : κ → ℕ) (x : Fin m → M) :
    (∏ j, x j ^ coordinateOrder ι a j) = ∏ i, x (ι i) ^ a i := by
  classical
  calc
    _ = ∏ j, ∏ i ∈ (Finset.univ.filter fun i => ι i = j), x j ^ a i := by
      simp only [coordinateOrder, Finset.prod_pow_eq_pow_sum]
    _ = ∏ j, ∏ i ∈ (Finset.univ.filter fun i => ι i = j), x (ι i) ^ a i := by
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.prod_fiberwise Finset.univ ι (fun i => x (ι i) ^ a i)

private theorem map_active_ideal_eq_original {κ : Type*} [Fintype κ]
    (ι : κ → Fin n) (a : κ → ℕ) :
    (Ideal.span {∏ i, coordinateGerm (ι i) ^ a i}).map
      (coordinateGermEquiv f n p t ht).toRingHom =
        Ideal.span {coefficientGerm f n p
          (∏ j, centeredOriginal f n p t j ^ coordinateOrder ι a j)} := by
  rw [Ideal.map_span, Set.image_singleton,
    ← coordinateOrder_prod ι a (fun j => coordinateGerm j)]
  exact congrArg (fun x => Ideal.span {x})
    (coordinateGermEquiv_monomial f n p t ht (coordinateOrder ι a))

include ht in
/-- The EXACT whole active-component ideal outputs of the original SNC geometry feed the
actual inverse-coordinate multiplier criterion for arbitrary ORIGINAL analytic tests.
No extra exponent/coordinate matching hypothesis is supplied. -/
theorem multiplierIntegrableAt_iff_active_original_rounded_ideal {s : ℕ}
    {κ : Type*} [Fintype κ] (ι : κ → Fin n) (a d : κ → ℕ)
    (G : Fin s → ComplexModel n → ℂ)
    (hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z)
    (hspanG : Ideal.span (Set.range fun i => HolGerm.mk (G i) (hG i)) =
      (Ideal.span {∏ i, coordinateGerm (ι i) ^ a i}).map
        (coordinateGermEquiv f n p t ht).toRingHom)
    {J : ComplexModel n → ℂ}
    (hJ : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ J z)
    (hspanJ : Ideal.span {HolGerm.mk J hJ} =
      (Ideal.span {∏ i, coordinateGerm (ι i) ^ d i}).map
        (coordinateGermEquiv f n p t ht).toRingHom)
    {F : ComplexModel n → ℂ}
    (hF : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z)
    (hw : QuasiPlurisubharmonicAt (generatorLog G) 0) {c : ℝ} (hc : 0 < c) :
    MultiplierIntegrableAt (generatorLog G) c (fun z => F z * J z) 0 volume ↔
      HolGerm.mk F hF ∈ Ideal.span {coefficientGerm f n p
        (∏ j, centeredOriginal f n p t j ^ roundedOrder
          (fun i => (coordinateOrder ι a i : ℝ)) (coordinateOrder ι d) c j)} := by
  apply multiplierIntegrableAt_iff_original_rounded_ideal f n p t ht
    G hG (coordinateOrder ι a) (coordinateOrder ι d)
    (hspanG.trans (map_active_ideal_eq_original f n p t ht ι a)) hJ
    (hspanJ.trans (map_active_ideal_eq_original f n p t ht ι d)) hF hw hc

end EnvelopeProperty.Char0.NativeSNCIntegralTransport
