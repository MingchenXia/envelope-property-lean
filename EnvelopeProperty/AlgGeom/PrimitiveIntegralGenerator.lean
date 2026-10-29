import EnvelopeProperty.AlgGeom.SeparatingNormalization
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Constructing an integral primitive generator

A finite generically separable domain extension admits a primitive generator
inside the original algebra. Clearing an original-base denominator of a field
primitive element retains generation of the entire fraction-field extension.
-/

open scoped Classical
noncomputable section

namespace EnvelopeProperty.FcPrimitiveIntegralGenerator

/-- A primitive generator of the finite separable fraction-field extension can
be chosen in the original finite algebra, without normality of that algebra. -/
theorem exists_primitive_element_mem_ring
    (R A K L : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra R A] [Module.Finite R A]
    [Algebra R K] [IsFractionRing R K] [Algebra A L] [IsFractionRing A L]
    [Algebra R L] [Algebra K L] [IsScalarTower R A L] [IsScalarTower R K L]
    [Algebra.FormallyEtale K L] :
    ∃ b : A, IntermediateField.adjoin K {algebraMap A L b} = ⊤ := by
  have : Algebra.EssFiniteType A L := .of_isLocalization L (nonZeroDivisors A)
  have : Algebra.EssFiniteType R L := .comp R A L
  have : Algebra.EssFiniteType K L := .of_comp R K L
  have : FiniteDimensional K L := Algebra.FormallyUnramified.finite_of_free K L
  have : Algebra.IsSeparable K L := Algebra.FormallyUnramified.isSeparable K L
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) α
  obtain ⟨b, d, hd, hdb⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R a
    (nonZeroDivisors.coe_ne_zero s)
  have hs : algebraMap A L s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr (nonZeroDivisors.coe_ne_zero s)
  have hscale : algebraMap R L d * IsLocalization.mk' L a s = algebraMap A L b := by
    apply mul_right_cancel₀ hs
    calc
      (algebraMap R L d * IsLocalization.mk' L a s) * algebraMap A L s =
          algebraMap R L d * algebraMap A L a := by
        rw [mul_assoc, IsLocalization.mk'_spec]
      _ = algebraMap A L s * algebraMap A L b := by
        have hh := congrArg (algebraMap A L) hdb
        simpa only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R A L] using hh
      _ = algebraMap A L b * algebraMap A L s := mul_comm _ _
  let E := IntermediateField.adjoin K ({algebraMap A L b} : Set L)
  have hbmem : algebraMap A L b ∈ E := IntermediateField.subset_adjoin K _ (by simp)
  have hdmem : algebraMap R L d ∈ E := by
    rw [IsScalarTower.algebraMap_apply R K L]
    exact E.algebraMap_mem (algebraMap R K d)
  have hdL : algebraMap R L d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K L]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd)
  have hαmem : IsLocalization.mk' L a s ∈ E := by
    have hh := E.mul_mem (E.inv_mem hdmem) hbmem
    rw [← hscale, ← mul_assoc, inv_mul_cancel₀ hdL, one_mul] at hh
    exact hh
  refine ⟨b, top_unique ?_⟩
  rw [← hα]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hαmem)

/-- The normalization, its actual fraction-field map, generic separability, and
an integral primitive element are all constructed from the original finite-type
domain over a perfect field. No normalization or generator is supplied. -/
theorem exists_global_normalization_with_integral_primitive_element
    (F A : Type*) [Field F] [PerfectField F] [CommRing A] [IsDomain A]
    [Algebra F A] [Algebra.FiniteType F A] :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) F →ₐ[F] A)
      (ψ : FractionRing (MvPolynomial (Fin n) F) →+* FractionRing A) (b : A),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsGenericallyEtale φ.toRingHom ∧
      (∀ p, ψ (algebraMap _ (FractionRing (MvPolynomial (Fin n) F)) p) =
        algebraMap A (FractionRing A) (φ p)) ∧
      (letI : Algebra (FractionRing (MvPolynomial (Fin n) F)) (FractionRing A) := ψ.toAlgebra
       Algebra.FormallyEtale (FractionRing (MvPolynomial (Fin n) F)) (FractionRing A) ∧
         IntermediateField.adjoin (FractionRing (MvPolynomial (Fin n) F))
           {algebraMap A (FractionRing A) b} = ⊤) := by
  obtain ⟨n, φ, hinj, hfin, het, ψ, hcompat, hsep⟩ :=
    FcSeparatingNormalization.exists_finite_separating_normalization_with_fractionMap F A
  let R := MvPolynomial (Fin n) F
  let K := FractionRing R
  let L := FractionRing A
  let : Algebra R A := φ.toRingHom.toAlgebra
  have : Module.Finite R A := hfin
  have : IsScalarTower R A L := inferInstance
  let : Algebra K L := ψ.toAlgebra
  have : IsScalarTower R K L :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [IsScalarTower.algebraMap_apply R A L]
      exact (hcompat p).symm
  have : Algebra.FormallyEtale K L := hsep
  obtain ⟨b, hb⟩ := exists_primitive_element_mem_ring R A K L
  exact ⟨n, φ, ψ, b, hinj, hfin, het, hcompat, inferInstance, hb⟩

end EnvelopeProperty.FcPrimitiveIntegralGenerator
