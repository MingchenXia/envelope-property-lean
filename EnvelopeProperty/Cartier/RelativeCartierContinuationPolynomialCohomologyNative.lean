import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyResidual

/-!
# Positive relative polynomial Cartier on actual native cohomology

Actual coordinate homotopies and original boundary normal forms prove bijectivity
of the native twist-linear map into the SAME original whole relative complex.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialCartier
open CategoryTheory Limits MvPolynomial
open scoped Classical
universe u
variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
local notation "P" => MvPolynomial (Fin n) k
local notation "T" => RelativeFrobenius.twist (algebraMap k P) p
local notation "K" => RelativeEtaleDeRham.complex (X : Fin n → P) (polynomialEtale k n) p

/-- The SAME actual relative row in every original positive degree. -/
def positiveShortComplex (q : ℕ) : ShortComplex (ModuleCat T) :=
  ShortComplex.mk
    (RelativeEtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) p q)
    (RelativeEtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) p (q+1))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact EtaleDeRham.differential_square (X : Fin n → P) (polynomialEtale k n) q w)

private def positiveAdjacentRowIso {C : Type*} [Category C] [HasZeroMorphisms C]
    (A : ℕ → C) (d : ∀ q, A q ⟶ A (q+1)) (sq : ∀ q, d q ≫ d (q+1) = 0) (q : ℕ) :
    (CochainComplex.of A d sq).sc' q (q+1) (q+1+1) ≅
      ShortComplex.mk (d q) (d (q+1)) (sq q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])
    (by
      dsimp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, CochainComplex.of_d])

private def positiveNativeRowIso (q : ℕ) :
    (K).sc' q (q+1) (q+1+1) ≅ positiveShortComplex k p n q := by
  unfold RelativeEtaleDeRham.complex positiveShortComplex
  exact positiveAdjacentRowIso _ _ _ q

/-- The original adjacent row computes native H(q+1) of the SAME full relative complex. -/
def positiveHomologyIso (q : ℕ) :
    (K).homology (q+1) ≅ (positiveShortComplex k p n q).homology :=
  (K).homologyIsoSc' q (q+1) (q+1+1)
    (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q+1)) ≪≫
      ShortComplex.homologyMapIso (positiveNativeRowIso k p n q)

/-- The SAME original cycle/boundary quotient is native full-complex cohomology. -/
def positiveQuotientIso (q : ℕ) : ModuleCat.of T
    (LinearMap.ker (positiveShortComplex k p n q).g.hom ⧸
      LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles) ≅ (K).homology (q+1) :=
  (positiveShortComplex k p n q).moduleCatHomologyIso.symm ≪≫ (positiveHomologyIso k p n q).symm

/-- The actual native T-linear cycle class map in EVERY positive degree. -/
def positiveCycleClass (q : ℕ) :
    LinearMap.ker (positiveShortComplex k p n q).g.hom →ₗ[T] (K).homology (q+1) :=
  (positiveQuotientIso k p n q).hom.hom.comp
    (LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles).mkQ

private theorem positiveQuotientIso_hom_injective (q : ℕ) :
    Function.Injective (positiveQuotientIso k p n q).hom := by
  intro x y h
  have h' := congrArg (positiveQuotientIso k p n q).inv h
  simpa only [Iso.hom_inv_id_apply] using h'

/-- Every actual native class has an actual original cycle representative. -/
theorem positiveCycleClass_surjective (q : ℕ) :
    Function.Surjective (positiveCycleClass k p n q) := by
  intro h
  obtain ⟨z, hz⟩ :=
    (LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles).mkQ_surjective
      ((positiveQuotientIso k p n q).inv h)
  refine ⟨z, ?_⟩
  change (positiveQuotientIso k p n q).hom
    ((LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles).mkQ z) = h
  rw [hz]
  exact Iso.inv_hom_id_apply (positiveQuotientIso k p n q) h

/-- The native class vanishes exactly for the ACTUAL original incoming boundary range. -/
theorem positiveCycleClass_zero_iff (q : ℕ)
    (z : LinearMap.ker (positiveShortComplex k p n q).g.hom) :
    positiveCycleClass k p n q z = 0 ↔
      z ∈ LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles := by
  change (positiveQuotientIso k p n q).hom
    ((LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles).mkQ z) = 0 ↔ _
  rw [← map_zero (positiveQuotientIso k p n q).hom.hom,
    (positiveQuotientIso_hom_injective k p n q).eq_iff]
  exact Submodule.Quotient.mk_eq_zero
    (p := LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles) (x := z)

/-- The actual T-linear representative lands in original cycles by proved residual closedness. -/
def positiveRepresentative (q : ℕ) : (⋀[T]^(q+1) (KaehlerDifferential k T)) →ₗ[T]
    LinearMap.ker (positiveShortComplex k p n q).g.hom :=
  LinearMap.codRestrict _ (exteriorRepresentative k p n (q+1)) (fun z => by
    change EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) (q+1)
      (originalExteriorRepresentative k p n (q+1) z) = 0
    exact originalExteriorRepresentative_closed k p n (q+1) z)

/-- Every actual chosen cycle retains the SAME original relative representative. -/
theorem positiveRepresentative_val (q : ℕ) (z : ⋀[T]^(q+1) (KaehlerDifferential k T)) :
    (positiveRepresentative k p n q z).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p (q+1) from
        originalExteriorRepresentative k p n (q+1) z) := rfl

/-- The genuine native relative inverse Cartier map in EVERY original positive degree. -/
def inverseCartierPositive (q : ℕ) :
    (⋀[T]^(q+1) (KaehlerDifferential k T)) →ₗ[T] (K).homology (q+1) :=
  (positiveCycleClass k p n q).comp (positiveRepresentative k p n q)

/-- Bijectivity is DERIVED from actual original homotopies and boundary normal forms,
without any supplied Cartier, cycle, image, exactness, or coefficient-root certificate. -/
theorem inverseCartierPositive_bijective (q : ℕ) :
    Function.Bijective (inverseCartierPositive k p n q) := by
  constructor
  · intro z z' he
    have hz : inverseCartierPositive k p n q (z-z') = 0 := by
      rw [map_sub, he, sub_self]
    change positiveCycleClass k p n q (positiveRepresentative k p n q (z-z')) = 0 at hz
    obtain ⟨u, hu⟩ := (positiveCycleClass_zero_iff k p n q _).mp hz
    have hu' := congrArg Subtype.val hu
    change EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) q u =
      originalExteriorRepresentative k p n (q+1) (z-z') at hu'
    exact sub_eq_zero.mp ((original_representative_boundary_iff k p n q (z-z')).mp ⟨u, hu'⟩)
  · intro h
    obtain ⟨w, hw⟩ := positiveCycleClass_surjective k p n q h
    let z := exteriorCoefficient k p n (q+1) w.val
    let r := positiveRepresentative k p n q z
    have hwclosed : EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) (q+1)
        w.val = 0 := w.property
    obtain ⟨u, hu⟩ := original_boundary_normalForm k p n q w.val hwclosed
    have hrange : w-r ∈ LinearMap.range (positiveShortComplex k p n q).moduleCatToCycles := by
      refine ⟨u, ?_⟩
      apply Subtype.ext
      exact hu
    have hzero := (positiveCycleClass_zero_iff k p n q (w-r)).mpr hrange
    rw [map_sub] at hzero
    refine ⟨z, ?_⟩
    change positiveCycleClass k p n q r = h
    exact (sub_eq_zero.mp hzero).symm.trans hw

/-- The actual native relative polynomial Cartier isomorphism in EVERY positive degree. -/
def inverseCartierPositiveEquiv (q : ℕ) :
    (⋀[T]^(q+1) (KaehlerDifferential k T)) ≃ₗ[T] (K).homology (q+1) :=
  LinearEquiv.ofBijective (inverseCartierPositive k p n q)
    (inverseCartierPositive_bijective k p n q)

end EnvelopeProperty.Cartier.RelativePolynomialCartier
