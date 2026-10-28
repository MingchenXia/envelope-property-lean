/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.LocalRing.Length


/-!
# Determinant norms and genuine local-module lengths

For a finite local algebra over an arbitrary field, each actual composition
factor is its residue field. Invariant-submodule determinant factorization
therefore gives the algebra norm as the residue-field norm raised to the local
module length. Nilpotent layers and inseparable residue degrees are retained.
-/

noncomputable section
namespace EnvelopeProperty

/-- Determinant of scalar action on an actual simple module over a local algebra. -/
theorem det_lsmul_simple_local {K E M : Type*} [Field K] [CommRing E] [Algebra K E]
    [IsLocalRing E] [AddCommGroup M] [Module E M] [Module K M] [IsScalarTower K E M]
    [FiniteDimensional K M] [IsSimpleModule E M] (b : E) :
    LinearMap.det (Algebra.lsmul K K M b) = Algebra.norm K (IsLocalRing.residue E b) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule E M)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  let eE : M ≃ₗ[E] IsLocalRing.ResidueField E := e
  let eK : M ≃ₗ[K] IsLocalRing.ResidueField E := eE.restrictScalars K
  have hc : (eK : M →ₗ[K] IsLocalRing.ResidueField E).comp
      ((Algebra.lsmul K K M b).comp eK.symm.toLinearMap) =
      Algebra.lmul K (IsLocalRing.ResidueField E) (IsLocalRing.residue E b) := by
    ext x
    change eE (b • eE.symm x) = IsLocalRing.residue E b * x
    rw [eE.map_smul, eE.apply_symm_apply]
    rfl
  rw [Algebra.norm_apply, ← hc, LinearMap.det_conj]

/-- Composition-factor determinant formula: each simple factor over a local
algebra is its genuine residue field, and every factor contributes its field norm. -/
theorem det_lsmul_eq_residueNorm_pow_length {K E : Type*} [Field K] [CommRing E]
    [Algebra K E] [IsLocalRing E] (b : E) (M : Type*) [AddCommGroup M] [Module E M]
    (hf : IsFiniteLength E M) : ∀ [Module K M] [IsScalarTower K E M] [FiniteDimensional K M],
    LinearMap.det (Algebra.lsmul K K M b) =
      Algebra.norm K (IsLocalRing.residue E b) ^ (Module.length E M).toNat := by
  induction hf with
  | @of_subsingleton M _ _ _ =>
    intros
    rw [Module.length_eq_zero, ENat.toNat_zero, pow_zero]
    exact LinearMap.det_eq_one_of_finrank_eq_zero (Module.finrank_zero_of_subsingleton (R := K) (M := M)) _
  | @of_simple_quotient M _ _ N _ hn ih =>
    intro _ _ _
    have : FiniteDimensional K N := Module.Finite.of_injective
      (N.subtype.restrictScalars K) N.subtype_injective
    have : FiniteDimensional K (M ⧸ N) := Module.Finite.of_surjective
      (N.mkQ.restrictScalars K) N.mkQ_surjective
    let W := N.restrictScalars K
    let f : Module.End K M := Algebra.lsmul K K M b
    have hs : W ≤ W.comap f := fun x hx => N.smul_mem b hx
    have hres : f.restrict (p := W) (q := W) (fun x hx => hs hx) = Algebra.lsmul K K N b := by
      ext x
      rfl
    have hquot : W.mapQ W f hs = Algebra.lsmul K K (M ⧸ N) b := by
      ext x
      rfl
    have hl : Module.length E M = Module.length E N + 1 := by
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
        (by rw [LinearMap.exact_iff, N.ker_mkQ, N.range_subtype]),
        Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule E (M ⧸ N))]
    rw [LinearMap.det_eq_det_mul_det W f hs, hres, hquot]
    change LinearMap.det (Algebra.lsmul K K N b) *
      LinearMap.det (Algebra.lsmul K K (M ⧸ N) b) = _
    rw [ih, det_lsmul_simple_local b, hl, ENat.toNat_add, ENat.toNat_one, pow_add, pow_one]
    · exact (Module.length_ne_top_iff.mpr hn)
    · exact ENat.one_ne_top

/-- The actual scalar algebra norm in any finite local algebra is the residue
field norm with its genuine local-length exponent, including inseparable residues. -/
theorem algebraNorm_eq_residueNorm_pow_length {K E : Type*} [Field K] [CommRing E]
    [Algebra K E] [FiniteDimensional K E] [IsLocalRing E] (b : E) :
    Algebra.norm K b = Algebra.norm K (IsLocalRing.residue E b) ^ (Module.length E E).toNat := by
  have hf : IsFiniteLength E E := isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower K (inferInstance : IsNoetherian K E),
      isArtinian_of_tower K (inferInstance : IsArtinian K E)⟩
  exact det_lsmul_eq_residueNorm_pow_length b E hf

/-- The length times the actual residue-field degree equals the algebra dimension. -/
theorem finrank_eq_length_mul_residue_finrank {K E : Type*} [Field K] [CommRing E]
    [Algebra K E] [FiniteDimensional K E] [IsLocalRing E] :
    Module.finrank K E = (Module.length E E).toNat *
      Module.finrank K (IsLocalRing.ResidueField E) := by
  have hc : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField E) =
      Module.finrank K (IsLocalRing.ResidueField E) := by
    rw [← Module.length_eq_of_surjective
      (R := IsLocalRing.ResidueField K) (M := IsLocalRing.ResidueField E)
      (show Function.Surjective (algebraMap K (IsLocalRing.ResidueField K)) from
        IsLocalRing.residue_surjective), Module.length_eq_finrank]
  have hl := IsLocalRing.length_restrictScalars K E E
  rw [Module.length_eq_finrank, hc] at hl
  have ht := congrArg ENat.toNat hl
  simpa only [ENat.toNat_natCast, ENat.toNat_mul] using ht

end EnvelopeProperty
