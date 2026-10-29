import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.CharP.Algebra

/-! # Genuine unramified rigidity from original p-th powers -/
noncomputable section
namespace EnvelopeProperty.Cartier.UnramifiedPowerRange
open scoped TensorProduct
open CategoryTheory Limits
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (p : ℕ) [hp : Fact p.Prime] [CharP S p]

omit hp in
private theorem tensorCharP : CharP (S ⊗[R] S) p := by
  apply charP_of_injective_ringHom
    (f := (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S)) _ p
  intro a b h
  have h' := congrArg (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) h
  simpa only [Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.lmul'_apply_tmul, mul_one] using h'

/-- Every ORIGINAL diagonal generator is genuinely p-nilpotent when the actual original
p-th powers lie in the original coefficient range. -/
theorem diagonalGenerator_pow
    (hpower : ∀ b : S, b^p ∈ (algebraMap R S).range) (b : S) :
    ((1 : S) ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S))^p = 0 := by
  let := tensorCharP R S p
  rw [sub_pow_char, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow]
  obtain ⟨a, ha⟩ := hpower b
  rw [← ha]
  apply sub_eq_zero.mpr
  simp only [one_pow, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

variable [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]

/-- The ENTIRE actual original diagonal ideal is zero: actual finite-type unramifiedness
supplies its idempotent generator, while original power-range derives its nilpotence. -/
theorem diagonalIdeal_eq_bot
    (hpower : ∀ b : S, b^p ∈ (algebraMap R S).range) :
    KaehlerDifferential.ideal R S = ⊥ := by
  have hnil : KaehlerDifferential.ideal R S ≤ nilradical (S ⊗[R] S) := by
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact ⟨p, diagonalGenerator_pow R S p hpower b⟩
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧
      KaehlerDifferential.ideal R S = (S ⊗[R] S) ∙ e :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg R S)).mp
      ((Ideal.cotangent_subsingleton_iff _).mp (inferInstanceAs (Subsingleton Ω[S⁄R])))
  have heI : e ∈ KaehlerDifferential.ideal R S := by
    rw [hsp]
    exact Submodule.subset_span (Set.mem_singleton e)
  have he0 : e = 0 := he.eq_zero_of_isNilpotent (hnil heI)
  rw [hsp, he0, Submodule.span_zero_singleton]

/-- The SAME two original entire tensor inclusions coincide, derived from the actual
vanishing diagonal ideal rather than assumed as a tensor comparison. -/
theorem tensorInclusions_eq
    (hpower : ∀ b : S, b^p ∈ (algebraMap R S).range) :
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S) =
      Algebra.TensorProduct.includeRight := by
  ext b
  have h := KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b
  rw [diagonalIdeal_eq_bot R S p hpower] at h
  exact (sub_eq_zero.mp h).symm

/-- The ACTUAL original coefficient homomorphism is a native ring-category epimorphism,
derived from the whole original tensor diagonal. -/
theorem epi_algebraMap
    (hpower : ∀ b : S, b^p ∈ (algebraMap R S).range) :
    Epi (CommRingCat.ofHom (algebraMap R S)) where
  left_cancellation g h hgh := by
    let P := CommRingCat.isPushout_tensorProduct R S S
    have he : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := S) (B := S)) =
        CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom :=
      congrArg (fun f : S →ₐ[R] S ⊗[R] S => CommRingCat.ofHom f.toRingHom)
        (tensorInclusions_eq R S p hpower)
    calc
      g = _ ≫ P.desc g h hgh := (P.inl_desc g h hgh).symm
      _ = _ ≫ P.desc g h hgh := congrArg (fun t => t ≫ P.desc g h hgh) he
      _ = h := P.inr_desc g h hgh

end EnvelopeProperty.Cartier.UnramifiedPowerRange
