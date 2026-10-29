import EnvelopeProperty.AlgGeom.ArithmeticCoefficientModel
import EnvelopeProperty.AlgGeom.ArithmeticClosedPointLift
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Algebra.CharZero.AddMonoidHom
import Mathlib.Algebra.Algebra.Rat

/-!
# A produced smooth arithmetic base inside the same coefficient field

An actual finite-type characteristic-zero integer domain is smooth on a produced
nonzero principal open. Its fraction field is used only as an essentially
finite-type algebra. For a literal integer subalgebra of the original field,
the localization has an actual image subalgebra of that same field. Extending
the preceding literal arithmetic model to it preserves the entire original
base-change map. The existing Witt point lift then applies to the produced base.
-/

noncomputable section
open scoped TensorProduct Classical

namespace EnvelopeProperty.ArithmeticSmoothCoefficientBase

universe u v w z

/-- The original zero-prime localization is formally smooth over the integers.
Only essentially finite type is used for its rational-field algebra. -/
theorem formallySmooth_atBot (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℤ R] [Algebra.FiniteType ℤ R] :
    Algebra.IsSmoothAt ℤ (⊥ : Ideal R) := by
  let F := Localization.AtPrime (⊥ : Ideal R)
  let : IsFractionRing R F := by
    change IsLocalization (nonZeroDivisors R) F
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let : Field F := IsFractionRing.toField R
  let : CharZero F := CharZero.of_addMonoidHom (algebraMap R F).toAddMonoidHom
    (algebraMap R F).map_one (IsFractionRing.injective R F)
  let : Algebra.EssFiniteType R F := .of_isLocalization _ (⊥ : Ideal R).primeCompl
  let : Algebra.EssFiniteType ℤ F := .comp ℤ R F
  let : @IsScalarTower ℤ ℚ F (inferInstance : Algebra ℤ ℚ).toSMul
      (inferInstance : Algebra ℚ F).toSMul (inferInstance : Algebra ℤ F).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := F) (Subsingleton.elim _ _)
  let : Algebra.EssFiniteType ℚ F := .of_comp ℤ ℚ F
  let : Algebra.FormallySmooth ℤ ℚ := .of_isLocalization (nonZeroDivisors ℤ)
  let : Algebra.FormallySmooth ℚ F := .of_perfectField
  exact Algebra.FormallySmooth.comp ℤ ℚ F

/-- Actual finite-type characteristic-zero integer domains produce a nonzero smooth principal open. -/
theorem exists_nonzero_smooth_away (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℤ R] [Algebra.FiniteType ℤ R] :
    ∃ r : R, r ≠ 0 ∧ Algebra.Smooth ℤ (Localization.Away r) ∧
      Algebra.FiniteType ℤ (Localization.Away r) ∧ IsDomain (Localization.Away r) ∧
        CharZero (Localization.Away r) := by
  let : Algebra.FinitePresentation ℤ R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.IsSmoothAt ℤ (⊥ : Ideal R) := formallySmooth_atBot R
  obtain ⟨r, hr, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℤ (⊥ : Ideal R)
  have hr0 : r ≠ 0 := by simpa using hr
  let : Algebra.Smooth ℤ (Localization.Away r) := hs
  let : IsDomain (Localization.Away r) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)
  let : CharZero (Localization.Away r) :=
    CharZero.of_addMonoidHom (algebraMap R (Localization.Away r)).toAddMonoidHom
      (algebraMap R (Localization.Away r)).map_one
      (IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hr0))
  exact ⟨r, hr0, hs, inferInstance, inferInstance, inferInstance⟩

variable {k : Type u} [Field k]

/-- The native localization lift into the SAME original field. -/
def awayEmbedding (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) :
    Localization.Away r →ₐ[R] k :=
  IsLocalization.Away.liftAlgHom (S := Localization.Away r) r
    (f := Algebra.ofId R k) (isUnit_iff_ne_zero.mpr (fun h => hr (Subtype.ext h)))

/-- The lift agrees with the original inclusion on every original element. -/
theorem awayEmbedding_source (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) (x : R) :
    awayEmbedding R r hr (algebraMap R (Localization.Away r) x) = (x : k) :=
  (awayEmbedding R r hr).commutes x

/-- The actual source inclusion makes the localization lift injective. -/
theorem awayEmbedding_injective (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) :
    Function.Injective (awayEmbedding R r hr) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (.powers r)
    (awayEmbedding R r hr).toRingHom).mpr
  intro x y
  change algebraMap R (Localization.Away r) x = algebraMap R (Localization.Away r) y ↔
    awayEmbedding R r hr (algebraMap R (Localization.Away r) x) =
      awayEmbedding R r hr (algebraMap R (Localization.Away r) y)
  rw [awayEmbedding_source, awayEmbedding_source]
  constructor
  · intro h
    exact congrArg Subtype.val
      (IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hr) h)
  · intro h
    exact congrArg (algebraMap R (Localization.Away r)) (Subtype.ext h)

/-- The localization as an ACTUAL integer subalgebra of the SAME original field. -/
def localizedCoefficientRing (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) : Subalgebra ℤ k :=
  (awayEmbedding R r hr).range.restrictScalars ℤ

private instance localizedAlgebra (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) :
    Algebra R (localizedCoefficientRing R r hr) :=
  inferInstanceAs (Algebra R (awayEmbedding R r hr).range)

private instance localizedTower (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) :
    IsScalarTower R (localizedCoefficientRing R r hr) k :=
  inferInstanceAs (IsScalarTower R (awayEmbedding R r hr).range k)

/-- The range equivalence identifies this actual subalgebra with the original localization. -/
def localizedCoefficientEquiv (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) :
    Localization.Away r ≃ₐ[R] localizedCoefficientRing R r hr :=
  AlgEquiv.ofInjective (awayEmbedding R r hr) (awayEmbedding_injective R r hr)

/-- The entire image equivalence followed by the actual inclusion is the original lift. -/
theorem localizedCoefficientEquiv_whole_embedding (R : Subalgebra ℤ k) (r : R)
    (hr : r ≠ 0) :
    (localizedCoefficientRing R r hr).val.toRingHom.comp
        (localizedCoefficientEquiv R r hr).toRingHom = (awayEmbedding R r hr).toRingHom := by
  ext x
  rfl

/-- All original coefficients remain literally in the same field subalgebra. -/
theorem le_localizedCoefficientRing (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) :
    R ≤ localizedCoefficientRing R r hr := by
  intro x hx
  exact ⟨algebraMap R (Localization.Away r) ⟨x, hx⟩, awayEmbedding_source R r hr ⟨x, hx⟩⟩

/-- This actual image, with its constructed source action, is the original localization. -/
theorem localizedCoefficientRing_isLocalization (R : Subalgebra ℤ k) (r : R) (hr : r ≠ 0) :
    IsLocalization.Away r (localizedCoefficientRing R r hr) :=
  IsLocalization.isLocalization_of_algEquiv (.powers r) (localizedCoefficientEquiv R r hr)

/-- A literal arithmetic subalgebra internally produces an actual smooth arithmetic localization. -/
theorem exists_smooth_localizedCoefficientRing [CharZero k] (R : Subalgebra ℤ k)
    [Algebra.FiniteType ℤ R] :
    ∃ (r : R) (hr : r ≠ 0), Algebra.Smooth ℤ (Localization.Away r) ∧
      Algebra.Smooth ℤ (localizedCoefficientRing R r hr) ∧
      Algebra.FiniteType ℤ (localizedCoefficientRing R r hr) ∧
      IsDomain (localizedCoefficientRing R r hr) ∧ CharZero (localizedCoefficientRing R r hr) ∧
      IsLocalization.Away r (localizedCoefficientRing R r hr) ∧ R ≤ localizedCoefficientRing R r hr := by
  obtain ⟨r, hr, hs, -, -, -⟩ := exists_nonzero_smooth_away R
  let : Algebra.Smooth ℤ (Localization.Away r) := hs
  let : Algebra.Smooth ℤ (localizedCoefficientRing R r hr) :=
    .of_equiv ((localizedCoefficientEquiv R r hr).restrictScalars ℤ)
  exact ⟨r, hr, hs, inferInstance, inferInstance, inferInstance, inferInstance,
    localizedCoefficientRing_isLocalization R r hr, le_localizedCoefficientRing R r hr⟩

open ArithmeticCoefficientModel

variable {σ : Type v} {ι : Type w} {A : Type z} [CommRing A] [Algebra k A]

/-- The SAME prior literal arithmetic model extended to the actual image subalgebra. -/
abbrev localizedPresentationModel (P : Algebra.Presentation k A σ ι) (extra : Finset k)
    (r : coefficientRing P.relation extra) (hr : r ≠ 0) :=
  localizedCoefficientRing (coefficientRing P.relation extra) r hr ⊗[coefficientRing P.relation extra]
    presentationModel P extra

private instance localizedModelCommRing (P : Algebra.Presentation k A σ ι) (extra : Finset k)
    (r : coefficientRing P.relation extra) (hr : r ≠ 0) :
    CommRing (localizedPresentationModel P extra r hr) :=
  Algebra.TensorProduct.instCommRing
    (R := coefficientRing P.relation extra)
    (A := localizedCoefficientRing (coefficientRing P.relation extra) r hr)
    (B := presentationModel P extra)

private instance localizedModelAlgebra (P : Algebra.Presentation k A σ ι) (extra : Finset k)
    (r : coefficientRing P.relation extra) (hr : r ≠ 0) :
    Algebra (localizedCoefficientRing (coefficientRing P.relation extra) r hr)
      (localizedPresentationModel P extra r hr) :=
  Algebra.TensorProduct.leftAlgebra
    (R := coefficientRing P.relation extra)
    (S := localizedCoefficientRing (coefficientRing P.relation extra) r hr)
    (A := localizedCoefficientRing (coefficientRing P.relation extra) r hr)
    (B := presentationModel P extra)

/-- Consecutive actual scalar extension followed by the SAME original model equivalence. -/
def localizedPresentationTensorEquiv (P : Algebra.Presentation k A σ ι) (extra : Finset k)
    (r : coefficientRing P.relation extra) (hr : r ≠ 0) :
    k ⊗[localizedCoefficientRing (coefficientRing P.relation extra) r hr]
      localizedPresentationModel P extra r hr ≃ₐ[k] A :=
  (Algebra.TensorProduct.cancelBaseChange (coefficientRing P.relation extra)
    (localizedCoefficientRing (coefficientRing P.relation extra) r hr) k k
    (presentationModel P extra)).trans (presentationTensorEquiv P extra)

/-- Every scalar and original polynomial retains its value after actual base localization. -/
theorem localizedPresentationTensorEquiv_tmul (P : Algebra.Presentation k A σ ι)
    (extra : Finset k) (r : coefficientRing P.relation extra) (hr : r ≠ 0)
    (c : k) (s : localizedCoefficientRing (coefficientRing P.relation extra) r hr)
    (p : MvPolynomial σ (coefficientRing P.relation extra)) :
    localizedPresentationTensorEquiv P extra r hr (c ⊗ₜ (s ⊗ₜ Ideal.Quotient.mk _ p)) =
      algebraMap k A ((s : k) * c) * MvPolynomial.aeval P.val
        (MvPolynomial.map (algebraMap (coefficientRing P.relation extra) k) p) := by
  simp only [localizedPresentationTensorEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  change presentationTensorEquiv P extra
    (((s : k) * c) ⊗ₜ Ideal.Quotient.mk _ p) = _
  exact presentationTensorEquiv_tmul P extra ((s : k) * c) p

/-- The ENTIRE original model base-change map is unchanged by the constructed localization. -/
theorem localizedPresentationTensorEquiv_whole_baseChange
    (P : Algebra.Presentation k A σ ι) (extra : Finset k)
    (r : coefficientRing P.relation extra) (hr : r ≠ 0) :
    (localizedPresentationTensorEquiv P extra r hr).toAlgHom.comp
      (Algebra.TensorProduct.cancelBaseChange (coefficientRing P.relation extra)
        (localizedCoefficientRing (coefficientRing P.relation extra) r hr) k k
        (presentationModel P extra)).symm.toAlgHom = (presentationTensorEquiv P extra).toAlgHom := by
  apply AlgHom.ext
  intro x
  exact congrArg (presentationTensorEquiv P extra)
    ((Algebra.TensorProduct.cancelBaseChange (coefficientRing P.relation extra)
      (localizedCoefficientRing (coefficientRing P.relation extra) r hr) k k
      (presentationModel P extra)).apply_symm_apply x)

/-- Finite presentation survives this actual scalar extension of the literal model. -/
theorem localizedPresentationModel_finitePresentation [Finite σ] [Finite ι]
    (P : Algebra.Presentation k A σ ι) (extra : Finset k)
    (r : coefficientRing P.relation extra) (hr : r ≠ 0) :
    Algebra.FinitePresentation (localizedCoefficientRing (coefficientRing P.relation extra) r hr)
      (localizedPresentationModel P extra r hr) := by
  let : Algebra.FinitePresentation (coefficientRing P.relation extra) (presentationModel P extra) :=
    presentationModel_finitePresentation P extra
  exact Algebra.FinitePresentation.baseChange
    (R := coefficientRing P.relation extra) (A := presentationModel P extra)
    (localizedCoefficientRing (coefficientRing P.relation extra) r hr)

/-- Original equations and extras internally produce a smooth actual arithmetic base,
retaining the SAME original model equivalence as a whole algebra-map square. -/
theorem exists_smooth_original_presentation_base [CharZero k] [Finite σ] [Finite ι]
    (P : Algebra.Presentation k A σ ι) (extra : Finset k) :
    ∃ (r : coefficientRing P.relation extra) (hr : r ≠ 0),
      Algebra.Smooth ℤ (localizedCoefficientRing (coefficientRing P.relation extra) r hr) ∧
      Algebra.FiniteType ℤ (localizedCoefficientRing (coefficientRing P.relation extra) r hr) ∧
      (∀ c ∈ extra, c ∈ localizedCoefficientRing (coefficientRing P.relation extra) r hr) ∧
      (∀ i m, MvPolynomial.coeff m (P.relation i) ∈
        localizedCoefficientRing (coefficientRing P.relation extra) r hr) ∧
      Algebra.FinitePresentation (localizedCoefficientRing (coefficientRing P.relation extra) r hr)
        (localizedPresentationModel P extra r hr) ∧
      (localizedPresentationTensorEquiv P extra r hr).toAlgHom.comp
        (Algebra.TensorProduct.cancelBaseChange (coefficientRing P.relation extra)
          (localizedCoefficientRing (coefficientRing P.relation extra) r hr) k k
          (presentationModel P extra)).symm.toAlgHom = (presentationTensorEquiv P extra).toAlgHom := by
  let : Algebra.FiniteType ℤ (coefficientRing P.relation extra) :=
    coefficientRing_finiteType P.relation extra
  obtain ⟨r, hr, -, hs, hFT, -, -, -, hle⟩ :=
    exists_smooth_localizedCoefficientRing (coefficientRing P.relation extra)
  exact ⟨r, hr, hs, hFT, fun c hc => hle (extra_mem_coefficientRing P.relation extra hc),
    fun i m => hle (coeff_mem_coefficientRing P.relation extra i m),
    localizedPresentationModel_finitePresentation P extra r hr,
    localizedPresentationTensorEquiv_whole_baseChange P extra r hr⟩

/-- The produced SAME arithmetic base supplies an actual large-characteristic W2 point lift. -/
theorem exists_produced_witt_point [CharZero k] (R : Subalgebra ℤ k)
    [Algebra.FiniteType ℤ R] (N : ℕ) :
    ∃ (r : R) (hr : r ≠ 0)
      (m : MaximalSpectrum (localizedCoefficientRing R r hr)) (p : ℕ) (hp : Fact p.Prime),
      N < p ∧
        ∃ (_hc : CharP ((localizedCoefficientRing R r hr) ⧸ m.asIdeal) p)
          (_hf : Finite ((localizedCoefficientRing R r hr) ⧸ m.asIdeal)),
          letI : Fact p.Prime := hp
          letI : Field ((localizedCoefficientRing R r hr) ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
          ∃ lifted : localizedCoefficientRing R r hr →+*
              DeligneIllusie.WittTwo.Ring p ((localizedCoefficientRing R r hr) ⧸ m.asIdeal),
            (DeligneIllusie.WittTwo.reduction p _).comp lifted = Ideal.Quotient.mk m.asIdeal ∧
              (DeligneIllusie.WittTwo.reduction p _).comp
                (lifted.comp (algebraMap R (localizedCoefficientRing R r hr))) =
                  (Ideal.Quotient.mk m.asIdeal).comp (algebraMap R (localizedCoefficientRing R r hr)) := by
  obtain ⟨r, hr, -, hs, hFT, -, -, -, -⟩ := exists_smooth_localizedCoefficientRing R
  let S := localizedCoefficientRing R r hr
  let : Algebra.Smooth ℤ S := hs
  let : Algebra.FiniteType ℤ S := hFT
  obtain ⟨m, p, hp, hNp, -, hc, hf, lifted, hred, -⟩ :=
    ArithmeticClosedPointLift.exists_large_characteristic_witt_lift (1 : S) one_ne_zero N
  exact ⟨r, hr, m, p, hp, hNp, hc, hf, lifted, hred, by rw [← RingHom.comp_assoc, hred]⟩

end EnvelopeProperty.ArithmeticSmoothCoefficientBase
