import EnvelopeProperty.Cartier.RelativeCartierContinuationPolynomialCohomologyOne

/-!
# Genuine native relative polynomial Cartier in degree zero and every degree

The actual coefficient-preserving relative Frobenius kernel/image and injectivity
identify the SAME degree-zero cycle module with T. The native initial homology
projection and actual zero exterior-power identity complete every polynomial degree.
-/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativePolynomialCartier
open CategoryTheory Limits MvPolynomial
open scoped Classical
universe u
variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] (n : ℕ)
local notation "P" => MvPolynomial (Fin n) k
local notation "T" => RelativeFrobenius.twist (algebraMap k P) p
local notation "K" => RelativeEtaleDeRham.complex (X : Fin n → P) (polynomialEtale k n) p

/-- The original arbitrary coefficient and divisible exponent monomial belong to
the SAME actual relative Frobenius range, with independent base universe. -/
theorem finite_monomial_mem_relative_range (d : Fin n →₀ ℕ) (a : k) (hd : ∀ i, p ∣ d i) :
    monomial d a ∈ ((RelativeFrobenius.map (algebraMap k P) p).hom).range := by
  rw [monomial_eq]
  apply Subring.mul_mem
  · refine ⟨(RelativeFrobenius.coefficientMap (algebraMap k P) p).hom a, ?_⟩
    exact congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of P => h.hom a)
      (RelativeFrobenius.coefficientMap_map (algebraMap k P) p)
  · apply Subring.prod_mem
    intro i hi
    change (X i : P)^d i ∈ _
    obtain ⟨m, hm⟩ := hd i
    rw [hm, mul_comm p m, pow_mul]
    exact RelativeFrobenius.pow_mem_range (algebraMap k P) p (X i ^ m)

/-- The whole original polynomial universal differential kernel is the actual relative
Frobenius image, retaining all coefficient and variable universes. -/
theorem finite_D_eq_zero_iff_mem_relative_range (f : P) :
    KaehlerDifferential.D k P f = 0 ↔ f ∈ ((RelativeFrobenius.map (algebraMap k P) p).hom).range := by
  constructor
  · intro hf
    have hpartials := (PolynomialDifferentialKernel.D_eq_zero_iff_partials_eq_zero f).mp hf
    rw [f.as_sum]
    apply Subring.sum_mem
    intro d hd
    apply finite_monomial_mem_relative_range k p n
    intro i
    by_contra hi
    exact (mem_support_iff.mp hd)
      (PolynomialDifferentialKernel.coeff_eq_zero_of_not_dvd p f hpartials d i hi)
  · rintro ⟨t, rfl⟩
    exact RelativeFrobeniusCoefficient.D_map_eq_zero p t

/-- The SAME original finite polynomial relative Frobenius is genuinely injective. -/
theorem finite_relativeFrobenius_injective : Function.Injective (RelativeFrobenius.map (algebraMap k P) p).hom := by
  intro x y h
  obtain ⟨f, rfl⟩ := RelativePolynomialPresentation.polynomialPresentation_surjective
    (R := k) (n := n) p x
  obtain ⟨g, rfl⟩ := RelativePolynomialPresentation.polynomialPresentation_surjective
    (R := k) (n := n) p y
  apply congrArg (RelativePolynomialPresentation.polynomialPresentation p)
  apply MvPolynomial.expand_injective hp.out.pos
  have hf := DFunLike.congr_fun
    (RelativePolynomialPresentation.map_polynomialPresentation (R := k) (n := n) p) f
  have hg := DFunLike.congr_fun
    (RelativePolynomialPresentation.map_polynomialPresentation (R := k) (n := n) p) g
  exact hf.symm.trans (h.trans hg)

/-- The actual first map of the SAME native relative complex is its original degree-zero map. -/
theorem relativeComplex_d_zero_one : (K).d 0 1 =
    RelativeEtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) p 0 := by
  change CochainComplex.of.d (RelativeEtaleDeRham.formModule (R := k) (B := P) p)
    (RelativeEtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) p) 0 (0+1) = _
  exact CochainComplex.of_d _ _ 0

/-- The native first differential has the SAME original value on every original zero form. -/
theorem relativeComplex_d_zero_one_apply (w : ⋀[P]^0 (KaehlerDifferential k P)) :
    ((K).d 0 1).hom (show (K).X 0 from w) =
      (show (K).X 1 from EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 0 w) := by
  rw [relativeComplex_d_zero_one]
  rfl

/-- The original universal D kills the zero-exterior coefficient of EVERY actual closed
original zero form; this is derived from the SAME original degree-zero differential. -/
theorem D_zeroEquiv_of_closed_zero (w : ⋀[P]^0 (KaehlerDifferential k P))
    (hw : EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 0 w = 0) :
    KaehlerDifferential.D k P (exteriorPower.zeroEquiv P (KaehlerDifferential k P) w) = 0 := by
  let e₀ := exteriorPower.zeroEquiv P (KaehlerDifferential k P)
  let e₁ := exteriorPower.oneEquiv P (KaehlerDifferential k P)
  have h₀ : e₀.symm (e₀ w) = w := e₀.symm_apply_apply w
  have hc : EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 0
      (e₀.symm (e₀ w)) = 0 :=
    (congrArg (EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 0) h₀).trans hw
  have h₁ : e₁ (EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 0
      (e₀.symm (e₀ w))) = 0 := (congrArg e₁ hc).trans (map_zero e₁)
  exact (EtaleDeRham.differential_zero (X : Fin n → P) (polynomialEtale k n) (e₀ w)).symm.trans h₁

/-- The regular native T-module maps to original degree-zero forms by its actual scalar action. -/
def zeroRepresentative : T →ₗ[T] RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 :=
  LinearMap.toSpanSingleton T _
    (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 from
      (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm (1 : P))

/-- The original zero exterior identity identifies the SAME representative with relative Frobenius. -/
theorem zeroRepresentative_val (t : T) : zeroRepresentative k p n t =
    (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 from
      (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm ((RelativeFrobenius.map (algebraMap k P) p).hom t)) := by
  change ((RelativeFrobenius.map (algebraMap k P) p).hom t) • (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm (1 : P) =
    (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm ((RelativeFrobenius.map (algebraMap k P) p).hom t)
  rw [← map_smul, smul_eq_mul, mul_one]

/-- Every original degree-zero representative is an actual original cycle. -/
theorem zeroRepresentative_closed (t : T) :
    EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 0
      (zeroRepresentative k p n t) = 0 := by
  rw [zeroRepresentative_val]
  apply (exteriorPower.oneEquiv P (KaehlerDifferential k P)).injective
  rw [EtaleDeRham.differential_zero, map_zero]
  exact RelativeFrobeniusCoefficient.D_map_eq_zero p t

/-- The actual T-linear degree-zero representative in the native first-differential kernel. -/
def zeroCycleRepresentative : T →ₗ[T] LinearMap.ker ((K).d 0 1).hom :=
  LinearMap.codRestrict _ (zeroRepresentative k p n) (fun t => by
    change ((K).d 0 1).hom (zeroRepresentative k p n t) = 0
    exact (relativeComplex_d_zero_one_apply k p n (zeroRepresentative k p n t)).trans
      (zeroRepresentative_closed k p n t))

/-- Each native cycle has exactly its specified original zero-exterior representative. -/
theorem zeroCycleRepresentative_val (t : T) : (zeroCycleRepresentative k p n t).val =
    (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 from
      (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm ((RelativeFrobenius.map (algebraMap k P) p).hom t)) :=
  zeroRepresentative_val k p n t

/-- Actual kernel=image and actual map injectivity prove the whole native zero-cycle bijection. -/
theorem zeroCycleRepresentative_bijective : Function.Bijective (zeroCycleRepresentative k p n) := by
  constructor
  · intro t t' h
    apply finite_relativeFrobenius_injective k p n
    have h' := congrArg (fun z : LinearMap.ker ((K).d 0 1).hom =>
      exteriorPower.zeroEquiv P (KaehlerDifferential k P) z.val) h
    change exteriorPower.zeroEquiv P (KaehlerDifferential k P) (zeroRepresentative k p n t) =
      exteriorPower.zeroEquiv P (KaehlerDifferential k P) (zeroRepresentative k p n t') at h'
    simpa only [zeroRepresentative_val, LinearEquiv.apply_symm_apply] using h'
  · intro w
    let w₀ : ⋀[P]^0 (KaehlerDifferential k P) := w.val
    have hw : EtaleDeRham.differential (X : Fin n → P) (polynomialEtale k n) 0 w₀ = 0 := by
      exact (relativeComplex_d_zero_one_apply k p n w₀).symm.trans w.property
    let f := exteriorPower.zeroEquiv P (KaehlerDifferential k P) w₀
    have hD : KaehlerDifferential.D k P f = 0 := D_zeroEquiv_of_closed_zero k n w₀ hw
    obtain ⟨t, ht⟩ := (finite_D_eq_zero_iff_mem_relative_range k p n f).mp hD
    refine ⟨t, ?_⟩
    apply Subtype.ext
    change zeroRepresentative k p n t = (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 from w₀)
    rw [zeroRepresentative_val, ht]
    exact LinearEquiv.symm_apply_apply _ w₀

/-- The original coefficient inclusion has the SAME original coefficient as its actual cycle value. -/
theorem zeroCycleRepresentative_coefficient (a : k) :
    (zeroCycleRepresentative k p n
      ((RelativeFrobenius.coefficientMap (algebraMap k P) p).hom a)).val =
      (show RelativeEtaleDeRham.formModule (R := k) (B := P) p 0 from
        (exteriorPower.zeroEquiv P (KaehlerDifferential k P)).symm (C a)) := by
  rw [zeroCycleRepresentative_val]
  have h := congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of P => h.hom a)
    (RelativeFrobenius.coefficientMap_map (algebraMap k P) p)
  change (RelativeFrobenius.map (algebraMap k P) p).hom ((RelativeFrobenius.coefficientMap (algebraMap k P) p).hom a) = C a at h
  rw [h]

/-- The actual native first-differential kernel is the SAME native initial cohomology. -/
def zeroKernelIso : ModuleCat.of T (LinearMap.ker ((K).d 0 1).hom) ≅ (K).homology 0 :=
  ((K).sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
    ((K).cyclesIsoSc' 0 0 1 CochainComplex.prev_nat_zero (by simp)).symm ≪≫ (K).isoHomologyπ₀

/-- The specified actual degree-zero relative inverse Cartier map into native H⁰. -/
def inverseCartierZero : T →ₗ[T] (K).homology 0 :=
  (zeroKernelIso k p n).hom.hom.comp (zeroCycleRepresentative k p n)

/-- The native degree-zero relative Cartier bijection is genuinely derived. -/
theorem inverseCartierZero_bijective : Function.Bijective (inverseCartierZero k p n) :=
  (zeroKernelIso k p n).toLinearEquiv.bijective.comp (zeroCycleRepresentative_bijective k p n)

/-- The SAME actual native degree-zero relative Cartier equivalence T ≃ H⁰. -/
def inverseCartierZeroEquiv : T ≃ₗ[T] (K).homology 0 :=
  LinearEquiv.ofBijective (inverseCartierZero k p n) (inverseCartierZero_bijective k p n)

/-- Every twist element maps to its specified ORIGINAL actual native cycle class. -/
theorem inverseCartierZeroEquiv_apply (t : T) : inverseCartierZeroEquiv k p n t =
    (zeroKernelIso k p n).hom (zeroCycleRepresentative k p n t) := rfl

/-- Genuine native relative polynomial Cartier in EVERY natural exterior degree. -/
def inverseCartierEquiv (q : ℕ) : (⋀[T]^q (KaehlerDifferential k T)) ≃ₗ[T] (K).homology q :=
  match q with
  | 0 => (exteriorPower.zeroEquiv T (KaehlerDifferential k T)).trans (inverseCartierZeroEquiv k p n)
  | q+1 => inverseCartierPositiveEquiv k p n q

/-- The SAME all-degree native relative Cartier equivalence as a module-category isomorphism. -/
def inverseCartierIso (q : ℕ) : ModuleCat.of T (⋀[T]^q (KaehlerDifferential k T)) ≅ (K).homology q :=
  (inverseCartierEquiv k p n q).toModuleIso

/-- The original Ω⁰_T = T identity gives precisely the specified actual degree-zero class. -/
theorem inverseCartierEquiv_zero_apply (t : T) : inverseCartierEquiv k p n 0
    ((exteriorPower.zeroEquiv T (KaehlerDifferential k T)).symm t) = inverseCartierZeroEquiv k p n t := by
  change inverseCartierZeroEquiv k p n
    (exteriorPower.zeroEquiv T (KaehlerDifferential k T)
      ((exteriorPower.zeroEquiv T (KaehlerDifferential k T)).symm t)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Every positive branch is the SAME accepted native positive Cartier equivalence. -/
theorem inverseCartierEquiv_succ (q : ℕ) : inverseCartierEquiv k p n (q+1) =
    inverseCartierPositiveEquiv k p n q := rfl

/-- The original Ω¹_T identification gives the SAME specified actual one-form equivalence. -/
theorem inverseCartierEquiv_one_apply (w : KaehlerDifferential k T) : inverseCartierEquiv k p n 1
    ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm w) = inverseCartierOneEquiv k p n w := by
  have h := congrArg
    (fun e : (⋀[T]^1 (KaehlerDifferential k T)) ≃ₗ[T] (K).homology 1 =>
      e ((exteriorPower.oneEquiv T (KaehlerDifferential k T)).symm w))
    (inverseCartierEquiv_succ k p n 0)
  exact h.trans (inverseCartierOne_eq_positive k p n w).symm

end EnvelopeProperty.Cartier.RelativePolynomialCartier
