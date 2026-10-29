import EnvelopeProperty.AlgGeom.PrimitiveIntegralGenerator
import EnvelopeProperty.AlgGeom.FiniteBirationalOpen
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# The actual birational monogenic subalgebra

If an element of the original algebra generates its fraction field over the
base fraction field, its actual singleton adjoin is birational to that original
algebra. The fraction-field comparison and the reverse fraction embedding are
constructed from the entire algebra maps.
-/

open scoped Classical
noncomputable section

namespace EnvelopeProperty.FcPrimitiveMonogenicSubalgebra

/-- The actual primitive singleton adjoin has the same fraction field as the
original algebra. In particular the original algebra embeds into its fraction
field as an algebra over that actual singleton adjoin. -/
theorem exists_fraction_embedding_of_primitive_adjoin
    (R A K L : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra R A] [Algebra R K] [IsFractionRing R K]
    [Algebra A L] [IsFractionRing A L] [Algebra R L] [Algebra K L]
    [IsScalarTower R A L] [IsScalarTower R K L]
    (b : A) (hprim : IntermediateField.adjoin K {algebraMap A L b} = ⊤) :
    ∃ ρ : A →ₐ[Algebra.adjoin R ({b} : Set A)]
        FractionRing (Algebra.adjoin R ({b} : Set A)), Function.Injective ρ := by
  let C := Algebra.adjoin R ({b} : Set A)
  let M := FractionRing C
  have hiRL : Function.Injective (algebraMap R L) := by
    intro r s he
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply R K L] using he
  have hiRA : Function.Injective (algebraMap R A) := by
    intro r s he
    apply hiRL
    simpa only [← IsScalarTower.algebraMap_apply R A L] using congrArg (algebraMap A L) he
  have hiRC : Function.Injective (algebraMap R C) := by
    intro r s he
    apply hiRA
    exact congrArg (algebraMap C A) he
  have hiCA : Function.Injective (algebraMap C A) := Subtype.val_injective
  have hRC : nonZeroDivisors R ≤ (nonZeroDivisors C).comap (algebraMap R C) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hiRC
  have hCA : nonZeroDivisors C ≤ (nonZeroDivisors A).comap (algebraMap C A) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hiCA
  let κK : K →+* M := IsLocalization.map M (algebraMap R C) hRC
  let : Algebra K M := κK.toAlgebra
  let σ : M →+* L := IsLocalization.map L (algebraMap C A) hCA
  have hσK : σ.comp κK = algebraMap K L := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro r
    change σ (κK (algebraMap R K r)) = algebraMap K L (algebraMap R K r)
    rw [show κK (algebraMap R K r) = algebraMap C M (algebraMap R C r) from
      IsLocalization.map_eq hRC r]
    rw [show σ (algebraMap C M (algebraMap R C r)) =
      algebraMap A L (algebraMap C A (algebraMap R C r)) from
        IsLocalization.map_eq hCA (algebraMap R C r)]
    rw [← IsScalarTower.algebraMap_apply R C A,
      ← IsScalarTower.algebraMap_apply R A L, ← IsScalarTower.algebraMap_apply R K L]
  let σₐ : M →ₐ[K] L := { σ with commutes' := fun k => congrArg (fun f : K →+* L => f k) hσK }
  have hbmem : algebraMap A L b ∈ σₐ.fieldRange := by
    refine ⟨algebraMap C M ⟨b, Algebra.self_mem_adjoin_singleton R b⟩, ?_⟩
    exact IsLocalization.map_eq hCA _
  have htop : σₐ.fieldRange = ⊤ := by
    apply top_unique
    rw [← hprim]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hbmem)
  have hsσ : Function.Surjective σₐ := by
    intro z
    have hz : z ∈ σₐ.fieldRange := htop ▸ IntermediateField.mem_top
    exact hz
  let e : M ≃ₐ[K] L := AlgEquiv.ofBijective σₐ ⟨σₐ.injective, hsσ⟩
  let ρ : A →ₐ[C] M :=
    { e.symm.toRingHom.comp (algebraMap A L) with
      commutes' := fun c => by
        apply e.injective
        change e (e.symm (algebraMap A L (algebraMap C A c))) = e (algebraMap C M c)
        rw [e.apply_symm_apply]
        exact (IsLocalization.map_eq hCA c).symm }
  exact ⟨ρ, e.symm.injective.comp (IsFractionRing.injective A L)⟩

/-- The actual primitive adjoin constructs a genuine common open with the
original finite algebra, controlled by one nonzero element of the original base.
Neither a birational embedding nor a common-open isomorphism is an input. -/
theorem exists_commonOpen_of_primitive_adjoin
    (R A K L : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra R A] [Module.Finite R A]
    [Algebra R K] [IsFractionRing R K] [Algebra A L] [IsFractionRing A L]
    [Algebra R L] [Algebra K L] [IsScalarTower R A L] [IsScalarTower R K L]
    (b : A) (hprim : IntermediateField.adjoin K {algebraMap A L b} = ⊤) :
    let C := Algebra.adjoin R ({b} : Set A)
    ∃ (h : C) (g : R), h ≠ 0 ∧ g ≠ 0 ∧ h ∣ algebraMap R C g ∧
      ∃ e : Localization.Away h ≃+* Localization.Away (algebraMap C A h),
        ∀ c : C, e (algebraMap C (Localization.Away h) c) =
          algebraMap A (Localization.Away (algebraMap C A h)) (algebraMap C A c) := by
  let C := Algebra.adjoin R ({b} : Set A)
  have : Module.Finite R C := Algebra.finite_adjoin_simple_of_isIntegral
    (Algebra.IsIntegral.isIntegral b)
  have : Module.Finite C A := Module.Finite.of_restrictScalars_finite R C A
  obtain ⟨ρ, hiρ⟩ := exists_fraction_embedding_of_primitive_adjoin R A K L b hprim
  obtain ⟨h, hh, e, he⟩ := FcFiniteBirationalOpen.exists_commonPrincipalOpen_equiv ρ hiρ
  have hint : IsIntegral R h := Algebra.IsIntegral.isIntegral h
  obtain ⟨g, hg, hdiv⟩ := hint.isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_iff_ne_zero.mpr hh)
  let : Algebra C (Localization.Away (algebraMap C A h)) := OreLocalization.instAlgebra
  refine ⟨h, g, hh, hg, ?_, @AlgEquiv.toRingEquiv _ _ _ _ _ _ _ _ e, ?_⟩
  · exact hdiv
  · intro c
    exact he c

/-- Over the original normal base, the actual singleton adjoin has the genuine
monic irreducible polynomial-quotient presentation, retaining its actual generator. -/
theorem monic_irreducible_minpoly_presentation
    (R A : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] (b : A) :
    (minpoly R b).Monic ∧ Irreducible (minpoly R b) ∧
      ∃ e : AdjoinRoot (minpoly R b) ≃ₐ[R] Algebra.adjoin R ({b} : Set A),
        (e (AdjoinRoot.root (minpoly R b)) : A) = b := by
  have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  refine ⟨minpoly.monic hb, minpoly.irreducible hb, minpoly.equivAdjoin hb, ?_⟩
  change (AdjoinRoot.Minpoly.toAdjoin R b
    (AdjoinRoot.mk (minpoly R b) Polynomial.X) : A) = b
  exact AdjoinRoot.Minpoly.coe_toAdjoin_mk_X

/-- Whole coefficient compatibility turns the actual common-open ring
isomorphism into the coefficient-field algebra isomorphism used for curve closures. -/
def commonOpenAlgEquiv_of_ringEquiv
    {F C A : Type*} [CommSemiring F] [CommRing C] [CommRing A]
    [Algebra F C] [Algebra F A] (δ : C →ₐ[F] A) (h : C)
    (e : Localization.Away h ≃+* Localization.Away (δ h))
    (he : ∀ c : C, e (algebraMap C (Localization.Away h) c) =
      algebraMap A (Localization.Away (δ h)) (δ c)) :
    Localization.Away h ≃ₐ[F] Localization.Away (δ h) :=
  { e with
    commutes' := fun f => by
      rw [IsScalarTower.algebraMap_apply F C (Localization.Away h),
        IsScalarTower.algebraMap_apply F A (Localization.Away (δ h))]
      change e (algebraMap C (Localization.Away h) (algebraMap F C f)) =
        algebraMap A (Localization.Away (δ h)) (algebraMap F A f)
      rw [he, δ.commutes] }

end EnvelopeProperty.FcPrimitiveMonogenicSubalgebra
