/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SpectrumBaseChangeProper
import EnvelopeProperty.Berkovich.SpectrumLocalPSH
import EnvelopeProperty.Berkovich.SpectrumResidueField
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Local psh pullback and rational points under scalar extension

Compatible coefficient valuations pull finite-coefficient convex PL
presentations and decreasing limits to the actual tensor scalar extension.
Rational points lift along arbitrary compatible valued coefficient maps by
an explicit tensor evaluator. Every affine point lifts through completion
of its normed coefficient field. Together with algebraic extension this
gives surjectivity for completed algebraic extensions of complete fields.
These are affine producers for `lem:fc-base-change` in the fibre-constancy
blueprint.
-/

open scoped NNReal Topology TensorProduct
open Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

section LocalPSHPullback
variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A]
    {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
    (hwv : ∀ r, w (algebraMap R S r) = v r)

/-- Scalar extension pulls every actual finite-coefficient convex PL
presentation back, preserving its coefficients and nonvanishing locus. -/
theorem IsConvexPLOn.fc_comp_baseChangeRestriction
    {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : IsConvexPLOn U u) :
    IsConvexPLOn (baseChangeRestriction hwv ⁻¹' U)
      (fun y => u (baseChangeRestriction hwv y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, n, a, s, hs, ha, hform⟩ :=
    hu (baseChangeRestriction hwv y) hy
  refine ⟨baseChangeRestriction hwv ⁻¹' W,
    hW.preimage (continuous_baseChangeRestriction hwv), hyW,
    Set.preimage_mono hWU, n, (fun i => (1 : S) ⊗ₜ[R] a i), s, hs, ?_, ?_⟩
  · intro z hz i
    exact ha (baseChangeRestriction hwv z) hz i
  · intro z hz
    exact hform (baseChangeRestriction hwv z) hz

/-- The original decreasing approximating sequence pulls back through the
whole scalar-restriction map. -/
theorem IsDecrConvexPLLimitOn.fc_comp_baseChangeRestriction
    {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : IsDecrConvexPLLimitOn U u) :
    IsDecrConvexPLLimitOn (baseChangeRestriction hwv ⁻¹' U)
      (fun y => u (baseChangeRestriction hwv y)) := by
  obtain ⟨a, ha, hanti, hlim⟩ := hu
  exact ⟨fun j y => a j (baseChangeRestriction hwv y),
    fun j => (ha j).fc_comp_baseChangeRestriction hwv,
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- Locally psh functions pull back along compatible scalar extension,
without a bound on the coefficient valuation. -/
theorem IsLocallyPSHOn.fc_comp_baseChangeRestriction
    {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : IsLocallyPSHOn U u) :
    IsLocallyPSHOn (baseChangeRestriction hwv ⁻¹' U)
      (fun y => u (baseChangeRestriction hwv y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu (baseChangeRestriction hwv y) hy
  exact ⟨baseChangeRestriction hwv ⁻¹' W,
    hW.preimage (continuous_baseChangeRestriction hwv), hyW,
    Set.preimage_mono hWU, hloc.fc_comp_baseChangeRestriction hwv⟩
end LocalPSHPullback

section RationalLift
variable {F L A : Type*} [CommRing F] [CommRing L] [CommRing A]
    [Algebra F L] [Algebra F A]
    {v : Valuation F ℝ≥0} {w : Valuation L ℝ≥0}

/-- The scalar-extended evaluation of an actual rational point. -/
def fcRationalLiftEval (e : A →ₐ[F] F) : L ⊗[F] A →ₐ[L] L where
  __ := (Algebra.TensorProduct.productMap (AlgHom.id F L)
    ((Algebra.ofId F L).comp e)).toRingHom
  commutes' c := by simp [Algebra.TensorProduct.productMap]

/-- The evaluator retains every pure tensor. -/
@[simp]
theorem fcRationalLiftEval_tmul (e : A →ₐ[F] F) (c : L) (a : A) :
    fcRationalLiftEval (L := L) e (c ⊗ₜ[F] a) = c * algebraMap F L (e a) := rfl

/-- The tensor evaluator is onto the entire new coefficient ring. -/
theorem fcRationalLiftEval_surjective (e : A →ₐ[F] F) :
    Function.Surjective (fcRationalLiftEval (L := L) e) := by
  intro c
  refine ⟨c ⊗ₜ[F] (1 : A), ?_⟩
  simp

/-- The quotient by the genuine tensor evaluation kernel is the entire
new coefficient ring. In particular, over fields the lift is rational. -/
def fcRationalLiftQuotientEquiv (e : A →ₐ[F] F) :
    ((L ⊗[F] A) ⧸ RingHom.ker (fcRationalLiftEval (L := L) e).toRingHom) ≃ₐ[L] L :=
  Ideal.quotientKerAlgEquivOfSurjective (fcRationalLiftEval_surjective e)

/-- Pulling back the prescribed new valuation produces an actual rational
point over the new coefficient ring. -/
def fcRationalLift (e : A →ₐ[F] F) : RelativeSpectrum w (L ⊗[F] A) :=
  ⟨⟨w.comap (fcRationalLiftEval e).toRingHom⟩, fun c => by
    change w (fcRationalLiftEval e (algebraMap L (L ⊗[F] A) c)) = w c
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]⟩

/-- The lifted rational point restricts to the whole original rational
seminorm, with no completeness or algebraicity hypothesis. -/
theorem fcRationalLift_baseChangeRestriction (hwv : ∀ c, w (algebraMap F L c) = v c)
    (e : A →ₐ[F] F) :
    baseChangeRestriction hwv (fcRationalLift (w := w) e) = comap e ⟨⟨v⟩, fun _ => rfl⟩ := by
  apply Subtype.ext
  apply Spectrum.ext_val
  intro a
  change w (fcRationalLiftEval e ((1 : L) ⊗ₜ[F] a)) = v (e a)
  rw [fcRationalLiftEval_tmul, one_mul, hwv]

end RationalLift
end EnvelopeProperty.Berkovich.RelativeSpectrum


namespace EnvelopeProperty.Berkovich.RelativeSpectrum
section CompletionLift
variable {F A : Type*} [NormedField F] [IsUltrametricDist F]
    [CommRing A] [Algebra F A]

/-- The isometric coefficient map into the actual H(x) extends to the
completion of the original base field. -/
def fcCompletionCoefficientHom (x : RelativeSpectrum (NormedField.valuation (K := F)) A) :
    UniformSpace.Completion F →ₐ[F] H x where
  __ := UniformSpace.Completion.extensionHom (algebraMap F (H x))
    (AddMonoidHomClass.isometry_of_norm (algebraMap F (H x))
      (fun c => by simpa using norm_algebraMap_H x c)).continuous
  commutes' c := by
    exact UniformSpace.Completion.extensionHom_coe _ _ c

@[simp]
theorem fcCompletionCoefficientHom_coe
    (x : RelativeSpectrum (NormedField.valuation (K := F)) A) (c : F) :
    fcCompletionCoefficientHom x (c : UniformSpace.Completion F) = algebraMap F (H x) c :=
  (fcCompletionCoefficientHom x).commutes c

/-- The genuinely extended entire coefficient map is continuous. -/
theorem continuous_fcCompletionCoefficientHom
    (x : RelativeSpectrum (NormedField.valuation (K := F)) A) :
    Continuous (fcCompletionCoefficientHom x) := UniformSpace.Completion.continuous_extension

/-- Density retains the norm on every completed coefficient, not only on F. -/
theorem norm_fcCompletionCoefficientHom
    (x : RelativeSpectrum (NormedField.valuation (K := F)) A) (c : UniformSpace.Completion F) :
    ‖fcCompletionCoefficientHom x c‖ = ‖c‖ := by
  induction c using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (continuous_norm.comp (continuous_fcCompletionCoefficientHom x)) continuous_norm
  | ih c =>
    rw [fcCompletionCoefficientHom_coe, UniformSpace.Completion.norm_coe]
    simpa using norm_algebraMap_H x c

/-- Evaluate the actual scalar tensor in H(x), using the extended whole
coefficient map and the original A evaluation. -/
def fcCompletionEval (x : RelativeSpectrum (NormedField.valuation (K := F)) A) :
    UniformSpace.Completion F ⊗[F] A →ₐ[F] H x :=
  Algebra.TensorProduct.productMap (fcCompletionCoefficientHom x)
    (IsScalarTower.toAlgHom F A (H x))

@[simp]
theorem fcCompletionEval_tmul (x : RelativeSpectrum (NormedField.valuation (K := F)) A)
    (c : UniformSpace.Completion F) (a : A) :
    fcCompletionEval x (c ⊗ₜ[F] a) =
      fcCompletionCoefficientHom x c * Spectrum.toH x.1 a := rfl

/-- The norm on the completed base retains the original coefficient norm. -/
theorem fcCompletion_val_algebraMap (c : F) :
    NormedField.valuation (K := UniformSpace.Completion F)
      (algebraMap F (UniformSpace.Completion F) c) = NormedField.valuation (K := F) c := by
  change ‖(c : UniformSpace.Completion F)‖₊ = ‖c‖₊
  exact UniformSpace.Completion.nnnorm_coe c

/-- An actual point after completion, constructed from its completed-field
evaluator, with the entire completed coefficient norm prescribed. -/
def fcCompletionLift (x : RelativeSpectrum (NormedField.valuation (K := F)) A) :
    RelativeSpectrum (NormedField.valuation (K := UniformSpace.Completion F))
      (UniformSpace.Completion F ⊗[F] A) :=
  ⟨⟨(NormedField.valuation (K := H x)).comap (fcCompletionEval x).toRingHom⟩, by
    intro c
    change ‖fcCompletionEval x (c ⊗ₜ[F] (1 : A))‖₊ = ‖c‖₊
    rw [fcCompletionEval_tmul, map_one, mul_one]
    exact NNReal.eq (norm_fcCompletionCoefficientHom x c)⟩

/-- The constructed completion lift retains the entire original seminorm. -/
theorem fcCompletionLift_baseChangeRestriction
    (x : RelativeSpectrum (NormedField.valuation (K := F)) A) :
    baseChangeRestriction (fcCompletion_val_algebraMap (F := F)) (fcCompletionLift x) = x := by
  apply Subtype.ext
  apply Spectrum.ext_val
  intro a
  change ‖fcCompletionEval x ((1 : UniformSpace.Completion F) ⊗ₜ[F] a)‖₊ = x.1.val a
  rw [fcCompletionEval_tmul, map_one, one_mul, Spectrum.nnnorm_toH]

/-- Scalar restriction from completion is surjective for every affine
algebra: the completed-residue-field evaluator supplies each lift. -/
theorem fc_baseChangeRestriction_completion_surjective :
    Function.Surjective (baseChangeRestriction (A := A) (fcCompletion_val_algebraMap (F := F))) :=
  fun x => ⟨fcCompletionLift x, fcCompletionLift_baseChangeRestriction x⟩

end CompletionLift
section AlgebraicCompletionLift
variable {K L A : Type*} [NormedField K] [NormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [CommRing A] [Algebra K A]

/-- The completed normed extension retains every original coefficient value. -/
theorem fcCompletedExtension_val_algebraMap (c : K) :
    NormedField.valuation (K := UniformSpace.Completion L)
      (algebraMap K (UniformSpace.Completion L) c) = NormedField.valuation (K := K) c :=
  nnnorm_algebraMap' (UniformSpace.Completion L) c

/-- Completing an algebraic valued extension of a complete base preserves
surjectivity of actual scalar restriction. Algebraic point existence and the
explicit completion evaluator are composed by genuine tensor cancellation. -/
theorem fc_baseChangeRestriction_algebraicCompletion_surjective
    [CompleteSpace K] [Algebra.IsAlgebraic K L] :
    Function.Surjective (baseChangeRestriction (A := A)
      (fcCompletedExtension_val_algebraMap (K := K) (L := L))) := by
  intro x
  have hKL : ∀ c : K, NormedField.valuation (K := L) (algebraMap K L c) =
      NormedField.valuation (K := K) c := fun c => nnnorm_algebraMap' L c
  obtain ⟨y, hy⟩ := baseChangeRestriction_surjective_of_isAlgebraic (A := A) hKL x
  refine ⟨iteratedBaseChangeHomeomorph
    (NormedField.valuation (K := UniformSpace.Completion L)) (fcCompletionLift y), ?_⟩
  rw [← baseChangeRestriction_iterated hKL (fcCompletion_val_algebraMap (F := L)),
    fcCompletionLift_baseChangeRestriction, hy]

end AlgebraicCompletionLift
end EnvelopeProperty.Berkovich.RelativeSpectrum
