import EnvelopeProperty.Global.NativeRankOneProperModel
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The SAME original native model is proper over arbitrary coefficient fields

Original M2 proves integral degree-zero coefficients. The TRUE graded-zero
projection and original finite generation prove finite type of actual degree
zero; integral+finiteType gives a finite actual base map. Compose its genuine
finite/proper Spec map with actual Proj-to-zero properness. No S0=k assertion.
Route: owned `native-arbitrary-field-properness-route.tex`.
-/
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Original M2 alone makes EVERY actual degree-zero coefficient integral
over the SAME original k. No algebraic-closedness or constant-field equality. -/
theorem originalDegreeZeroCoefficient_isIntegral {r : ℕ} (Y : MultiModel k K r)
    {f : K} (hf : f ∈ Y.piece 0) : IsIntegral k f := by
  have hint : IsIntegral Y.coordAlg (monomial 0 f) := Y.isIntegral_coordAlg hf
  let ψ : MvPolynomial (Fin r) K →ₐ[k] K := (aeval fun _ => (0 : K)).restrictScalars k
  have hle : Y.coordAlg ≤ (⊥ : Subalgebra k K).comap ψ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    have h0 : ψ (Y.coordMono i) = 0 := by
      simp [ψ, coordMono, aeval_monomial]
    change ψ (Y.coordMono i) ∈ (⊥ : Subalgebra k K)
    rw [h0]
    exact Subalgebra.zero_mem _
  let φ : Y.coordAlg →ₐ[k] k := (Algebra.botEquiv k K).toAlgHom.comp
    ((ψ.comp Y.coordAlg.val).codRestrict ⊥ fun x => hle x.2)
  have hbot : ∀ b : (⊥ : Subalgebra k K), algebraMap k K (Algebra.botEquiv k K b) = b := by
    intro b
    conv_rhs => rw [← (Algebra.botEquiv k K).symm_apply_apply b]
    rw [Algebra.botEquiv_symm_apply]
    rfl
  have hφ : (algebraMap k K).comp (φ : Y.coordAlg →+* k) =
      (ψ : MvPolynomial (Fin r) K →+* K).comp
        (algebraMap Y.coordAlg (MvPolynomial (Fin r) K)) :=
    RingHom.ext fun _ => hbot _
  have h1 := IsIntegral.map_of_comp_eq (φ : Y.coordAlg →+* k)
    (ψ : MvPolynomial (Fin r) K →+* K) hφ hint
  have hψ : (ψ : MvPolynomial (Fin r) K →+* K) (monomial 0 f) = f := by
    simp [ψ]
  rw [hψ] at h1
  exact h1

variable (X : MultiModel k K 1)

private local instance arbitraryNativeZeroTower : IsScalarTower k (X.nativeTotalGrading 0) X.S where
  smul_assoc a b p := by
    change (a • (b : X.S)) * p = a • ((b : X.S) * p)
    exact smul_mul_assoc a (b : X.S) p

/-- The TRUE actual nonnegative graded-zero projection is an actual k-algebra
map, with original coefficient inclusion; no replacement base action. -/
def nativeRankOneZeroProjection : X.S →ₐ[k] X.nativeTotalGrading 0 where
  toRingHom := GradedRing.projZeroRingHom' X.nativeTotalGrading
  commutes' a := by
    change GradedRing.projZeroRingHom' X.nativeTotalGrading (algebraMap k X.S a) =
      X.nativeRankOneCoefficients a
    exact GradedRing.projZeroRingHom'_apply_coe X.nativeTotalGrading
      (X.nativeRankOneCoefficients a)

/-- The SAME actual graded-zero projection is genuinely onto the whole zero ring. -/
theorem nativeRankOneZeroProjection_surjective :
    Function.Surjective X.nativeRankOneZeroProjection :=
  GradedRing.projZeroRingHom'_surjective X.nativeTotalGrading

/-- Original fg and the actual graded-zero surjection DERIVE finite type
of the SAME actual degree-zero ring over the SAME k, without AlgClosed. -/
theorem nativeRankOneZeroFiniteType : Algebra.FiniteType k (X.nativeTotalGrading 0) := by
  let : Algebra.FiniteType k X.S := (Subalgebra.fg_iff_finiteType X.S).mp X.fg
  exact Algebra.FiniteType.of_surjective X.nativeRankOneZeroProjection
    X.nativeRankOneZeroProjection_surjective

/-- EVERY element of the SAME actual native zero ring is integral over actual
original k, via its literal homogeneous coefficient and injective inclusion. -/
theorem nativeRankOneZeroIsIntegral : Algebra.IsIntegral k (X.nativeTotalGrading 0) := by
  let ι : X.nativeTotalGrading 0 →ₐ[k] MvPolynomial (Fin 1) K :=
    X.S.val.comp (IsScalarTower.toAlgHom k (X.nativeTotalGrading 0) X.S)
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  refine ⟨fun z => ?_⟩
  let f : K := (((z : X.S) : MvPolynomial (Fin 1) K).coeff 0)
  have hp : ((z : X.S) : MvPolynomial (Fin 1) K) = monomial 0 f := by
    simpa only [Finsupp.single_zero] using rankOne_homogeneous_eq_monomial 0
      ((z : X.S) : MvPolynomial (Fin 1) K) ((X.mem_nativeTotalGrading 0 _).mp z.property)
  have hf : f ∈ X.piece 0 := by
    change monomial 0 f ∈ X.S
    rw [← hp]
    exact (z : X.S).property
  apply (isIntegral_algHom_iff ι hι).mp
  change IsIntegral k ((z : X.S) : MvPolynomial (Fin 1) K)
  rw [hp]
  have h : IsIntegral k (algebraMap K (MvPolynomial (Fin 1) K) f) :=
    (X.originalDegreeZeroCoefficient_isIntegral hf).map
      (IsScalarTower.toAlgHom k K (MvPolynomial (Fin 1) K))
  simpa only [MvPolynomial.algebraMap_apply,
    MvPolynomial.C_apply, Algebra.algebraMap_self_apply] using h

/-- Actual original zero integrality plus finite type DERIVES finite k-module
structure, retaining genuine algebraic constant extensions over arbitrary k. -/
theorem nativeRankOneZeroFinite : Module.Finite k (X.nativeTotalGrading 0) := by
  let := X.nativeRankOneZeroIsIntegral
  let := X.nativeRankOneZeroFiniteType
  exact Algebra.IsIntegral.finite (R := k) (A := X.nativeTotalGrading 0)

/-- The ACTUAL original coefficient homomorphism itself is finite. -/
theorem nativeRankOneCoefficients_finite : RingHom.Finite (A := k) (B := X.nativeTotalGrading 0) X.nativeRankOneCoefficients := by
  have he : X.nativeRankOneCoefficients = algebraMap k (X.nativeTotalGrading 0) := by
    ext a
    rfl
  rw [he, RingHom.finite_algebraMap]
  exact X.nativeRankOneZeroFinite

/-- The SAME coefficient Spec map is genuinely finite, without changing fields. -/
theorem nativeRankOneCoefficientSpec_isFinite :
    IsFinite (Spec.map (CommRingCat.ofHom (R := k) (S := X.nativeTotalGrading 0) X.nativeRankOneCoefficients)) :=
  (IsFinite.SpecMap_iff _).mpr X.nativeRankOneCoefficients_finite

/-- The SAME actual original native structure is proper over ARBITRARY k:
true Proj-to-zero properness composed with true finite constant-extension Spec. -/
theorem nativeRankOneStructure_isProper_arbitraryField : IsProper X.nativeRankOneStructure := by
  let := X.nativeRankOne_toSpecZero_isProper
  let := X.nativeRankOneCoefficientSpec_isFinite
  change IsProper (Proj.toSpecZero X.nativeTotalGrading ≫
    Spec.map (CommRingCat.ofHom (R := k) (S := X.nativeTotalGrading 0) X.nativeRankOneCoefficients))
  infer_instance

#check @arbitraryNativeZeroTower
#print axioms arbitraryNativeZeroTower
end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.MultiModel.originalDegreeZeroCoefficient_isIntegral
#print axioms EnvelopeProperty.MultiModel.originalDegreeZeroCoefficient_isIntegral
#check @EnvelopeProperty.MultiModel.nativeRankOneZeroProjection
#print axioms EnvelopeProperty.MultiModel.nativeRankOneZeroProjection
#check @EnvelopeProperty.MultiModel.nativeRankOneZeroProjection_surjective
#print axioms EnvelopeProperty.MultiModel.nativeRankOneZeroProjection_surjective
#check @EnvelopeProperty.MultiModel.nativeRankOneZeroFiniteType
#print axioms EnvelopeProperty.MultiModel.nativeRankOneZeroFiniteType
#check @EnvelopeProperty.MultiModel.nativeRankOneZeroIsIntegral
#print axioms EnvelopeProperty.MultiModel.nativeRankOneZeroIsIntegral
#check @EnvelopeProperty.MultiModel.nativeRankOneZeroFinite
#print axioms EnvelopeProperty.MultiModel.nativeRankOneZeroFinite
#check @EnvelopeProperty.MultiModel.nativeRankOneCoefficients_finite
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoefficients_finite
#check @EnvelopeProperty.MultiModel.nativeRankOneCoefficientSpec_isFinite
#print axioms EnvelopeProperty.MultiModel.nativeRankOneCoefficientSpec_isFinite
#check @EnvelopeProperty.MultiModel.nativeRankOneStructure_isProper_arbitraryField
#print axioms EnvelopeProperty.MultiModel.nativeRankOneStructure_isProper_arbitraryField
