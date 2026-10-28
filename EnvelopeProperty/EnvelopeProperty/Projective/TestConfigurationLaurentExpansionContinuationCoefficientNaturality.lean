import EnvelopeProperty.Projective.TestConfigurationLaurentExpansionContinuationOpenBaseComparison

/-! # Actual Laurent tensor coefficients commute with original restrictions

The literal singleton reconstruction and finite-family induction derive
coefficient naturality. Its original-open specialization retains the same
native module-sheaf restriction map, without a supplied comparison.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings LaurentPolynomial
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.TestConfigurationLaurentExpansionContinuation

variable {R : Type u} [CommRing R]

/-- A singleton actual coefficient family reconstructs the literal Laurent
monomial tensor the SAME original coefficient, at any integer exponent. -/
theorem originalLaurentDomainCoefficients_symm_single (V : ModuleCat.{u} R)
    (n : ℤ) (v : V) :
    (originalLaurentDomainCoefficients V).symm (Finsupp.single n v) =
      (LaurentPolynomial.T n : R[T;T⁻¹]) ⊗ₜ[R, algebraMap R R[T;T⁻¹]] v := by
  rw [originalLaurentDomainCoefficients_symm]
  simp

/-- The actual scalar-extension map retains each literal Laurent monomial
and applies the SAME original linear map to each original coefficient. -/
theorem originalLaurentDomainCoefficients_symm_map {V W : ModuleCat.{u} R}
    (a : V ⟶ W) (c : ℤ →₀ V) :
    (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map a
        ((originalLaurentDomainCoefficients V).symm c) =
      (originalLaurentDomainCoefficients W).symm (c.mapRange a.hom a.hom.map_zero) := by
  classical
  have hzero : (0 : ℤ →₀ V).mapRange a.hom a.hom.map_zero = 0 := by
    ext n
    simp
  have hadd (c d : ℤ →₀ V) :
      (c + d).mapRange a.hom a.hom.map_zero =
        c.mapRange a.hom a.hom.map_zero + d.mapRange a.hom a.hom.map_zero := by
    ext n
    simp
  have hsingle (n : ℤ) (v : V) :
      (Finsupp.single n v).mapRange a.hom a.hom.map_zero = Finsupp.single n (a.hom v) := by
    ext i
    by_cases hi : i = n
    · subst i
      simp
    · simp [hi]
  induction c using Finsupp.induction with
  | zero => simp only [hzero, map_zero]
  | @single_add n v c _hn _hv ih =>
      simp only [map_add, hadd, hsingle, originalLaurentDomainCoefficients_symm_single, ih]
      exact congrArg
        (fun z : (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).obj W =>
          z + (originalLaurentDomainCoefficients W).symm (c.mapRange a.hom a.hom.map_zero))
        (ModuleCat.ExtendScalars.map_tmul (algebraMap R R[T;T⁻¹]) a
          (LaurentPolynomial.T n : R[T;T⁻¹]) v)

/-- Taking the ACTUAL finite Laurent coefficients commutes with the actual
original linear section map on every tensor. -/
theorem originalLaurentDomainCoefficients_map {V W : ModuleCat.{u} R}
    (a : V ⟶ W)
    (z : (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).obj V) :
    originalLaurentDomainCoefficients W
        ((ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map a z) =
      (originalLaurentDomainCoefficients V z).mapRange a.hom a.hom.map_zero := by
  apply (originalLaurentDomainCoefficients W).symm.injective
  rw [(originalLaurentDomainCoefficients W).symm_apply_apply,
    ← originalLaurentDomainCoefficients_symm_map a,
    (originalLaurentDomainCoefficients V).symm_apply_apply]

/-- For actual original opens this is precisely the ORIGINAL module-sheaf
section restriction, including every coefficient and every integer index. -/
theorem originalLaurentDomainCoefficients_restrict {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
    {U V : X.Opens} (hUV : U ≤ V)
    (z : (ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).obj
      ((originalBaseOpenPresheaf f M).obj (op V))) :
    originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op U))
        ((ModuleCat.extendScalars (algebraMap R R[T;T⁻¹])).map
          ((originalBaseOpenPresheaf f M).map (homOfLE hUV).op) z) =
      (originalLaurentDomainCoefficients ((originalBaseOpenPresheaf f M).obj (op V)) z).mapRange
        (fun s => (show (originalBaseOpenPresheaf f M).obj (op U) from
          M.presheaf.map (homOfLE hUV).op s))
        (by exact (M.presheaf.map (homOfLE hUV).op).hom.map_zero) := by
  exact originalLaurentDomainCoefficients_map
    ((originalBaseOpenPresheaf f M).map (homOfLE hUV).op) z

end EnvelopeProperty.TestConfigurationLaurentExpansionContinuation
