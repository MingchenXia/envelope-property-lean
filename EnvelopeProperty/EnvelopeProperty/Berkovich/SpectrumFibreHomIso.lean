import EnvelopeProperty.Berkovich.SpectrumFibreScalarExtension

/-!
# Actual finite fibre equivalences for arbitrary algebra homomorphisms

A true canonical completed tensor map is allowed to be invertible at a single
basepoint even when the original algebra map is not a global isomorphism.
-/
open scoped TensorProduct
open Classical
noncomputable section
namespace EnvelopeProperty.Berkovich.Spectrum
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D]

/-- The whole original coefficient map is retained under any algebra homomorphism. -/
theorem comap_algHom_base (f : B →ₐ[A] D) (y : Spectrum D) :
    comap (algebraMap A B) (comap f.toRingHom y) = comap (algebraMap A D) y := by
  apply ext_val
  intro a
  change y.val (f (algebraMap A B a)) = y.val (algebraMap A D a)
  rw [f.commutes]

/-- Actual completed residue field maps commute on the entire coefficient field for an arbitrary algebra map. -/
theorem completedMap_algHom_comm (f : B →ₐ[A] D) (y : Spectrum D) :
    (H.map f.toRingHom (rfl : comap f.toRingHom y = _)).comp
      (H.map (algebraMap A B) (comap_algHom_base f y)) =
        H.map (algebraMap A D) (rfl : comap (algebraMap A D) y = _) := by
  have hr : f.toRingHom.comp (algebraMap A B) = algebraMap A D := by
    ext a
    exact f.commutes a
  rw [H.map_comp]
  congr 1

/-- The actual whole completed tensor square commutes for every original tensor. -/
theorem fibreHom_algHom (f : B →ₐ[A] D) (y : Spectrum D)
    (q : H (comap (algebraMap A D) y) ⊗[A] B) :
    fibreHom (rfl : comap (algebraMap A D) y = _)
      (Algebra.TensorProduct.map (AlgHom.id (H (comap (algebraMap A D) y)) (H (comap (algebraMap A D) y))) f q) =
    H.map f.toRingHom (rfl : comap f.toRingHom y = _)
      (fibreHom (comap_algHom_base f y) q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add q q' hq hq' => simp only [map_add, hq, hq']
  | tmul c b =>
    change fibreHom (rfl : comap (algebraMap A D) y = _) (c ⊗ₜ[A] f b) =
      H.map f.toRingHom (rfl : comap f.toRingHom y = _)
        (fibreHom (comap_algHom_base f y) (c ⊗ₜ[A] b))
    rw [fibreHom_tmul, fibreHom_tmul, map_mul]
    have hs := congrArg (fun g => g c) (completedMap_algHom_comm f y)
    rw [show H.map (algebraMap A D) (rfl : comap (algebraMap A D) y = _) c = _ from hs.symm]
    rw [H.map_toH]
    rfl

/-- Actual named-basepoint version of the whole tensor square. -/
theorem fibreHom_algHom_of_comap (f : B →ₐ[A] D) {x : Spectrum A} {y : Spectrum D}
    (hy : comap (algebraMap A D) y = x) (q : H x ⊗[A] B) :
    fibreHom hy (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f q) =
      H.map f.toRingHom (rfl : comap f.toRingHom y = _)
        (fibreHom ((comap_algHom_base f y).trans hy) q) := by
  subst x
  exact fibreHom_algHom f y q

/-- The genuine restriction map on the actual original point fibres. -/
def pointFibreMap (f : B →ₐ[A] D) (x : Spectrum A) :
    Fibre (B := D) x → Fibre (B := B) x :=
  fun y => ⟨comap f.toRingHom y.1, (comap_algHom_base f y.1).trans y.2⟩

/-- Actual kernel classification commutes with the same canonical tensor map. -/
theorem maximalSpectrum_comap_tensorMap
    [Algebra.IsIntegral A B] [Algebra.IsIntegral A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f))
    (y : Fibre (B := D) x) :
    maximalSpectrumAlgEquiv (AlgEquiv.ofBijective _ hf)
      (fibreEquivMaximalSpectrum (B := D) x y) =
        fibreEquivMaximalSpectrum (B := B) x (pointFibreMap f x y) := by
  apply MaximalSpectrum.ext
  ext q
  change fibreHom y.2 (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f q) = 0 ↔
    fibreHom ((comap_algHom_base f y.1).trans y.2) q = 0
  rw [fibreHom_algHom_of_comap f y.2]
  have hi := H.map_injective f.toRingHom (rfl : comap f.toRingHom y.1 = _)
  constructor
  · intro hq
    apply hi
    simpa only [map_zero] using hq
  · intro hq
    rw [hq, map_zero]

/-- Actual canonical completed tensor bijectivity makes the SAME original fibre restriction bijective. -/
theorem pointFibreMap_bijective_of_tensorMap_bijective
    [Algebra.IsIntegral A B] [Algebra.IsIntegral A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f)) :
    Function.Bijective (pointFibreMap f x) := by
  let eT := AlgEquiv.ofBijective _ hf
  have heq : pointFibreMap f x = (fibreEquivMaximalSpectrum (B := B) x).symm ∘
      maximalSpectrumAlgEquiv eT ∘ fibreEquivMaximalSpectrum (B := D) x := by
    funext y
    apply (fibreEquivMaximalSpectrum (B := B) x).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact (maximalSpectrum_comap_tensorMap f x hf y).symm
  rw [heq]
  exact (fibreEquivMaximalSpectrum (B := B) x).symm.bijective.comp
    ((maximalSpectrumAlgEquiv eT).bijective.comp (fibreEquivMaximalSpectrum (B := D) x).bijective)

/-- A genuine equivalence of whole integral point fibres, with forward map the original restriction. -/
def pointFibreTensorEquiv [Algebra.IsIntegral A B] [Algebra.IsIntegral A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f)) :
    Fibre (B := D) x ≃ Fibre (B := B) x :=
  Equiv.ofBijective (pointFibreMap f x) (pointFibreMap_bijective_of_tensorMap_bijective f x hf)

/-- Every original function value agrees with the original algebra homomorphism, on the whole fibre. -/
theorem pointFibreTensorEquiv_apply_val
    [Algebra.IsIntegral A B] [Algebra.IsIntegral A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f))
    (y : Fibre (B := D) x) (b : B) :
    (pointFibreTensorEquiv f x hf y).1.val b = y.1.val (f b) := rfl

/-- The entire forward point is restriction along the ORIGINAL homomorphism. -/
theorem pointFibreTensorEquiv_apply_coe
    [Algebra.IsIntegral A B] [Algebra.IsIntegral A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f))
    (y : Fibre (B := D) x) :
    (pointFibreTensorEquiv f x hf y).1 = comap f.toRingHom y.1 := rfl

private local instance homIso_ker_isPrime {x : Spectrum A} {y : Spectrum B}
    (h : comap (algebraMap A B) y = x) :
    (RingHom.ker (fibreHom h)).IsPrime := RingHom.ker_isPrime _

/-- The genuine local completed tensor dimensions preserve every original nonetale fibre weight. -/
theorem fibreNormMult_comap_of_tensorMap_bijective
    [Module.Finite A B] [Module.Finite A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f))
    {y : Spectrum D} (hy : comap (algebraMap A D) y = x) :
    fibreNormMult A (comap f.toRingHom y) = fibreNormMult A y := by
  let eT := AlgEquiv.ofBijective _ hf
  let m := fibreEquivMaximalSpectrum (B := D) x ⟨y, hy⟩
  have hker : (maximalSpectrumAlgEquiv eT m).asIdeal =
      RingHom.ker (fibreHom ((comap_algHom_base f y).trans hy)) :=
    congrArg MaximalSpectrum.asIdeal (maximalSpectrum_comap_tensorMap f x hf ⟨y, hy⟩)
  rw [fibreNormMult_eq_localFinrank_of_comap ((comap_algHom_base f y).trans hy),
    fibreNormMult_eq_localFinrank_of_comap hy]
  exact (localFinrank_congr (K := H x) hker.symm).trans
    (finrank_maximalLocalizationAlgEquiv eT m).symm

/-- Every weighted function sum is invariant through the actual original fibre map. -/
theorem fibreWeightedSum_of_tensorMap_bijective
    [Module.Finite A B] [Module.Finite A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f))
    {M : Type*} [AddCommMonoid M] (u : Spectrum B → M) :
    (∑ y ∈ (finite_preimage_singleton (A := D) x).toFinset,
      fibreNormMult A y • u (comap f.toRingHom y)) =
      ∑ y ∈ (finite_preimage_singleton (A := B) x).toFinset,
        fibreNormMult A y • u y := by
  let eF := pointFibreTensorEquiv f x hf
  classical
  refine Finset.sum_bij (fun y hy => (eF ⟨y, (Set.Finite.mem_toFinset (finite_preimage_singleton (A := D) x)).1 hy⟩).1) ?_ ?_ ?_ ?_
  · intro y hy
    exact (Set.Finite.mem_toFinset (finite_preimage_singleton (A := B) x)).2 (eF ⟨y, (Set.Finite.mem_toFinset (finite_preimage_singleton (A := D) x)).1 hy⟩).2
  · intro y₁ h₁ y₂ h₂ he
    exact congrArg Subtype.val (eF.injective (Subtype.ext he))
  · intro z hz
    obtain ⟨⟨y, hy⟩, he⟩ := eF.surjective ⟨z, (Set.Finite.mem_toFinset (finite_preimage_singleton (A := B) x)).1 hz⟩
    exact ⟨y, (Set.Finite.mem_toFinset (finite_preimage_singleton (A := D) x)).2 hy, congrArg Subtype.val he⟩
  · intro y hy
    have hy' : comap (algebraMap A D) y = x :=
      (Set.Finite.mem_toFinset (finite_preimage_singleton (A := D) x)).mp hy
    have hw := fibreNormMult_comap_of_tensorMap_bijective f x hf hy'
    dsimp only [eF]
    rw [pointFibreTensorEquiv_apply_coe, hw]

/-- The whole nonetale weighted product is retained under a true pointwise completed tensor isomorphism. -/
theorem fibreWeightedProduct_of_tensorMap_bijective
    [Module.Finite A B] [Module.Finite A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f))
    {M : Type*} [CommMonoid M] (u : Spectrum B → M) :
    (∏ y ∈ (finite_preimage_singleton (A := D) x).toFinset,
      u (comap f.toRingHom y) ^ fibreNormMult A y) =
      ∏ y ∈ (finite_preimage_singleton (A := B) x).toFinset,
        u y ^ fibreNormMult A y := by
  simpa using congrArg Additive.toMul
    (fibreWeightedSum_of_tensorMap_bijective f x hf (fun y => Additive.ofMul (u y)))

/-- All extended-real function norms retain the actual local-length and inseparability weights. -/
theorem fibreWeightedERealSum_of_tensorMap_bijective
    [Module.Finite A B] [Module.Finite A D]
    (f : B →ₐ[A] D) (x : Spectrum A)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (H x) (H x)) f))
    (u : Spectrum B → EReal) :
    (∑ y ∈ (finite_preimage_singleton (A := D) x).toFinset,
      (fibreNormMult A y : EReal) * u (comap f.toRingHom y)) =
      ∑ y ∈ (finite_preimage_singleton (A := B) x).toFinset,
        (fibreNormMult A y : EReal) * u y := by
  simpa only [EReal.nsmul_eq_mul] using fibreWeightedSum_of_tensorMap_bijective f x hf u

end EnvelopeProperty.Berkovich.Spectrum
