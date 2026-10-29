import EnvelopeProperty.Potential.CurveClopenCharacteristicFactors
import EnvelopeProperty.Potential.CurvePieceRanks

/-! # Original global curve clopens give complementary actual polynomial factors -/

open scoped NNReal Polynomial TensorProduct Classical
open Polynomial
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
  [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]
  {m : ℕ} (U : FCStandardAffinoid w m)

omit [Fintype ι] in
private theorem mem_piece_iff_original_evaluation (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (y : RelativeSpectrum w B)
    (hy : comap (IsScalarTower.toAlgHom K K[X] B) y ∈ U.carrier) :
    y ∈ U.curveIdempotentAmbientPiece basis e ↔
      ‖U.curveOriginalEvaluation basis ⟨y, hy⟩ e‖₊ = 1 := by
  rw [U.mem_curveIdempotentAmbientPiece_iff basis e y hy]
  change ‖Spectrum.fibreHom _ (U.curveIdempotentSpecialization basis e
    (U.curveOriginalBasePoint ⟨y, hy⟩))‖₊ = 1 ↔ _
  rw [← U.curveOriginalEvaluation_specialization basis ⟨y, hy⟩ e]

omit [Fintype ι] in
/-- The actual ambient complementary piece is the relative original complement,
derived from whole original completed-field evaluation. -/
theorem curveIdempotentAmbientPiece_one_sub (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) :
    U.curveIdempotentAmbientPiece basis (1-e) =
      comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier \ U.curveIdempotentAmbientPiece basis e := by
  ext y
  by_cases hy : comap (IsScalarTower.toAlgHom K K[X] B) y ∈ U.carrier
  · simp only [Set.mem_sdiff, Set.mem_preimage, hy, true_and]
    rw [U.mem_piece_iff_original_evaluation basis (1-e) y hy,
      U.mem_piece_iff_original_evaluation basis e y hy, map_sub, map_one]
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp
      (he.map (U.curveOriginalEvaluation basis ⟨y, hy⟩)) with hz | ho
    · simp only [hz, sub_zero, nnnorm_one, nnnorm_zero, zero_ne_one, not_false_eq_true]
    · simp only [ho, sub_self, nnnorm_zero, nnnorm_one, zero_ne_one, not_true_eq_false]
  · have hne : y ∉ U.curveIdempotentAmbientPiece basis (1-e) :=
      fun h => hy (U.curveIdempotentAmbientPiece_subset basis (1-e) h)
    simp only [Set.mem_sdiff, Set.mem_preimage, hy, false_and, hne]

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K]
  [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]
  {m : ℕ} (U : FCStandardAffinoid (NormedField.valuation (K := K)) m)

/-- The original complement constructs exactly the whole complementary
idempotent, using actual original-point faithfulness. -/
theorem globalClopenIdempotent_compl (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C) :
    U.globalClopenIdempotent basis Cᶜ hC.compl = 1-U.globalClopenIdempotent basis C hC := by
  apply (U.curveIdempotentAmbientPiece_eq_iff basis
    (U.isIdempotent_globalClopenIdempotent basis Cᶜ hC.compl)
    (U.isIdempotent_globalClopenIdempotent basis C hC).one_sub).mpr
  rw [U.ambientPiece_globalClopenIdempotent,
    U.curveIdempotentAmbientPiece_one_sub basis (U.isIdempotent_globalClopenIdempotent basis C hC),
    U.ambientPiece_globalClopenIdempotent]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_preimage]
  tauto

variable [CompleteSpace K]

omit [IsAlgClosed K] in
/-- Every positive-radius whole disc faithfully contains the original
polynomial ring, read by its actual original-field coefficients. -/
theorem polynomialAnalyticMap_zeroDisc_injective {r : ℝ≥0} (hr : 0 < r) :
    Function.Injective (zeroDisc (K := K) r).polynomialAnalyticMap := by
  intro p q hpq
  apply Polynomial.ext
  intro i
  have h := congrArg (discCoefficient r hr i) hpq
  simpa only [discCoefficient_polynomialMap] using h

/-- A genuine original global clopen constructs complementary actual
polynomial factors of the original multiplication polynomial. -/
theorem exists_globalClopen_polynomial_factorization (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C)
    (b : B) :
    let := Module.Finite.of_basis basis
    let := Module.Free.of_basis basis
    ∃ P Q : K[X][X], P * Q = (Algebra.lmul K[X] B b).charpoly ∧
      ∀ r : ℝ≥0,
        Polynomial.map (zeroDisc (K := K) r).polynomialAnalyticMap P =
          (zeroDisc (K := K) r).curveCharacteristicFactor basis
            ((zeroDisc (K := K) r).isIdempotent_globalClopenIdempotent basis C hC) b ∧
        Polynomial.map (zeroDisc (K := K) r).polynomialAnalyticMap Q =
          (zeroDisc (K := K) r).curveCharacteristicFactor basis
            ((zeroDisc (K := K) r).isIdempotent_globalClopenIdempotent basis C hC).one_sub b := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis basis
  obtain ⟨P, _, hP⟩ := exists_globalClopenFactor_polynomial basis C hC b
  obtain ⟨Q, _, hQ⟩ := exists_globalClopenFactor_polynomial basis Cᶜ hC.compl b
  have hQc (r : ℝ≥0) :
      Polynomial.map (zeroDisc (K := K) r).polynomialAnalyticMap Q =
        (zeroDisc (K := K) r).curveCharacteristicFactor basis
          ((zeroDisc (K := K) r).isIdempotent_globalClopenIdempotent basis C hC).one_sub b := by
    have hh := hQ r
    simp only [(zeroDisc (K := K) r).globalClopenIdempotent_compl basis C hC] at hh
    exact hh
  refine ⟨P, Q, ?_, fun r => ⟨hP r, hQc r⟩⟩
  apply Polynomial.map_injective (zeroDisc (K := K) 1).polynomialAnalyticMap
    (polynomialAnalyticMap_zeroDisc_injective (K := K) zero_lt_one)
  rw [Polynomial.map_mul, hP 1, hQc 1]
  exact (zeroDisc (K := K) 1).curveCharacteristicFactor_mul_one_sub basis
    ((zeroDisc (K := K) 1).isIdempotent_globalClopenIdempotent basis C hC) b

omit [CompleteSpace K] in
/-- An actual original selected point prevents its genuine whole analytic
characteristic factor from being a unit. -/
theorem not_isUnit_curveCharacteristicFactor_of_selected_point
    (basis : Module.Basis ι K[X] B) {e : U.CurveAnalyticAlgebra basis}
    (he : IsIdempotentElem e) (b : B) (y : RelativeSpectrum (NormedField.valuation (K := K)) B)
    (hy : y ∈ U.curveIdempotentAmbientPiece basis e) :
    ¬ IsUnit (U.curveCharacteristicFactor basis he b) := by
  let := Module.Finite.of_basis basis
  have hyU := U.curveIdempotentAmbientPiece_subset basis e hy
  let yp : U.CurvePreimage (B := B) := ⟨y, hyU⟩
  let x := U.curveOriginalBasePoint yp
  let z : Spectrum.Fibre (B := B) x.1.1 := ⟨y.1, rfl⟩
  have hz : (Spectrum.fibrePoint z.2).1.val (U.curveIdempotentSpecialization basis e x) = 1 :=
    (U.mem_curveIdempotentAmbientPiece_iff basis e y hyU).mp hy
  have hw := U.curveIdempotentPieceWeight_pos basis e x z hz
  have hrank : 0 < Module.finrank (Spectrum.H x.1.1)
      (IdempotentSummand.Summand (U.curveIdempotentSpecialization basis e x)) := by
    change 0 < ∑ z ∈ Spectrum.completedIdempotentFibrePiece x.1.1
      (U.curveIdempotentSpecialization basis e x), Spectrum.fibreNormMult K[X] z.1 at hw
    rwa [Spectrum.sum_completedIdempotentFibrePiece_eq_finrank x.1.1
      (U.curveIdempotentSpecialization_isIdempotent basis he x)] at hw
  intro hunit
  have hfield := hunit.map (Polynomial.mapRingHom (U.evaluationToH x))
  change IsUnit (Polynomial.map (U.evaluationToH x) (U.curveCharacteristicFactor basis he b)) at hfield
  rw [U.map_curveCharacteristicFactor basis he b x] at hfield
  have hdeg := (IdempotentSummand.characteristicFactor_eq_charpoly (R := Spectrum.H x.1.1)
    (U.curveIdempotentSpecialization_isIdempotent basis he x)
    ((1 : Spectrum.H x.1.1) ⊗ₜ[K[X]] b)).2.2
  rw [Polynomial.natDegree_eq_zero_of_isUnit hfield] at hdeg
  exact (Nat.ne_of_gt hrank) hdeg.symm

/-- A nontrivial original global clopen constructs two nonunit original
polynomial factors; nontriviality is witnessed by actual original points. -/
theorem exists_globalClopen_nonunit_polynomial_factorization
    (basis : Module.Basis ι K[X] B)
    (C : Set (RelativeSpectrum (NormedField.valuation (K := K)) B)) (hC : IsClopen C)
    (hCne : C.Nonempty) (hCcomp : Cᶜ.Nonempty) (b : B) :
    let := Module.Finite.of_basis basis
    let := Module.Free.of_basis basis
    ∃ P Q : K[X][X], P * Q = (Algebra.lmul K[X] B b).charpoly ∧ ¬ IsUnit P ∧ ¬ IsUnit Q := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis basis
  obtain ⟨P, Q, hPQ, hPQdisc⟩ := exists_globalClopen_polynomial_factorization basis C hC b
  refine ⟨P, Q, hPQ, ?_, ?_⟩
  · intro hunit
    obtain ⟨y, hyC⟩ := hCne
    let x := comap (IsScalarTower.toAlgHom K K[X] B) y
    let r := val x Polynomial.X
    let D := zeroDisc (K := K) r
    have hxD : x ∈ D.carrier := by
      refine ⟨?_, fun j => Fin.elim0 j⟩
      simpa only [D, zeroDisc, ofDisc, Polynomial.C_0, sub_zero] using (le_refl r)
    have hyD : y ∈ D.curveIdempotentAmbientPiece basis (D.globalClopenIdempotent basis C hC) := by
      rw [D.ambientPiece_globalClopenIdempotent]
      exact ⟨hyC, hxD⟩
    apply D.not_isUnit_curveCharacteristicFactor_of_selected_point basis
      (D.isIdempotent_globalClopenIdempotent basis C hC) b y hyD
    have hu := hunit.map (Polynomial.mapRingHom D.polynomialAnalyticMap)
    change IsUnit (Polynomial.map D.polynomialAnalyticMap P) at hu
    rw [(hPQdisc r).1] at hu
    exact hu
  · intro hunit
    obtain ⟨y, hyC⟩ := hCcomp
    let x := comap (IsScalarTower.toAlgHom K K[X] B) y
    let r := val x Polynomial.X
    let D := zeroDisc (K := K) r
    have hxD : x ∈ D.carrier := by
      refine ⟨?_, fun j => Fin.elim0 j⟩
      simpa only [D, zeroDisc, ofDisc, Polynomial.C_0, sub_zero] using (le_refl r)
    have hyD : y ∈ D.curveIdempotentAmbientPiece basis (1-D.globalClopenIdempotent basis C hC) := by
      rw [← D.globalClopenIdempotent_compl basis C hC, D.ambientPiece_globalClopenIdempotent]
      exact ⟨hyC, hxD⟩
    apply D.not_isUnit_curveCharacteristicFactor_of_selected_point basis
      (D.isIdempotent_globalClopenIdempotent basis C hC).one_sub b y hyD
    have hu := hunit.map (Polynomial.mapRingHom D.polynomialAnalyticMap)
    change IsUnit (Polynomial.map D.polynomialAnalyticMap Q) at hu
    rw [(hPQdisc r).2] at hu
    exact hu

/-- An actual irreducible original multiplication polynomial rules out every
nontrivial original analytic clopen, deriving whole analytic preconnectedness. -/
theorem preconnectedSpace_of_irreducible_charpoly (basis : Module.Basis ι K[X] B) (b : B)
    (hirr : let := Module.Finite.of_basis basis
      let := Module.Free.of_basis basis
      Irreducible (Algebra.lmul K[X] B b).charpoly) :
    PreconnectedSpace (RelativeSpectrum (NormedField.valuation (K := K)) B) := by
  let := Module.Finite.of_basis basis
  let := Module.Free.of_basis basis
  apply preconnectedSpace_iff_clopen.mpr
  intro C hC
  by_cases hce : C = ∅
  · exact Or.inl hce
  by_cases hcu : C = Set.univ
  · exact Or.inr hcu
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hce
  have hCcomp : Cᶜ.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hc
    apply hcu
    exact compl_injective (by simpa only [Set.compl_univ] using hc)
  obtain ⟨P, Q, hPQ, hnP, hnQ⟩ :=
    exists_globalClopen_nonunit_polynomial_factorization basis C hC hCne hCcomp b
  rcases hirr.isUnit_or_isUnit hPQ.symm with hP | hQ
  · exact False.elim (hnP hP)
  · exact False.elim (hnQ hQ)

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
