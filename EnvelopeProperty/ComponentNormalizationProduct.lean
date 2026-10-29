/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.ReducedComponents
import EnvelopeProperty.FiniteCurveNormalization

/-!
# Actual products of original component normalizations

Every factor is the literal integral closure of the actual original prime
quotient in its own fraction field. Original ring and quotient maps retain
all elements, exact radical/nilradical kernels and coefficient actions.
Genuine perfect-field finite normalization plus the actual finite index proves
whole product finiteness and original-quotient prime lifts. This constructs
and compares a product of genuine component normalizations; identification
with an integral closure in a chosen total quotient ring remains separate.
-/

noncomputable section
namespace EnvelopeProperty.ReducedComponents
variable {R : Type*} [CommRing R]

/-- The ACTUAL product of the literal normalizations of every original minimal component. -/
abbrev NormalizationProduct (I : Ideal R) :=
  ∀ p : Index I, CurveNormalization.Ring (Component I p)

/-- Every actual component quotient maps by its genuine inclusion into its own normalization. -/
def normalizationInclusion (I : Ideal R) :
    (∀ p : Index I, Component I p) →+* NormalizationProduct I :=
  RingHom.pi fun p => (CurveNormalization.inclusion (Component I p)).comp
    (Pi.evalRingHom (Component I) p)

theorem normalizationInclusion_apply (I : Ideal R) (x : ∀ p : Index I, Component I p)
    (p : Index I) :
    normalizationInclusion I x p = CurveNormalization.inclusion (Component I p) (x p) := rfl

/-- Actual component domains make the entire product of true normalization inclusions injective. -/
theorem normalizationInclusion_injective (I : Ideal R) :
    Function.Injective (normalizationInclusion I) := by
  intro x y he
  funext p
  exact CurveNormalization.inclusion_injective (Component I p) (congrFun he p)

/-- The whole original ambient map into every actual normalized component. -/
def normalizationMap (I : Ideal R) : R →+* NormalizationProduct I :=
  (normalizationInclusion I).comp (ringMap I)

/-- Every original ring element is retained in its actual fraction-field normalization value. -/
theorem normalizationMap_apply (I : Ideal R) (r : R) (p : Index I) :
    normalizationMap I r p =
      CurveNormalization.inclusion (Component I p) (Ideal.Quotient.mk p.1 r) := rfl

/-- Its actual kernel is precisely the original ideal radical, without replacing any model ideal. -/
theorem ker_normalizationMap (I : Ideal R) : RingHom.ker (normalizationMap I) = I.radical := by
  ext r
  change normalizationInclusion I (ringMap I r) = 0 ↔ r ∈ I.radical
  rw [map_eq_zero_iff _ (normalizationInclusion_injective I), ← RingHom.mem_ker, ker_ringMap]

/-- The literal original reduction embeds into the actual product of genuine normalized components. -/
def reducedNormalizationEmbedding (I : Ideal R) : (R ⧸ I.radical) →+* NormalizationProduct I :=
  (normalizationInclusion I).comp (reducedEmbedding I)

theorem reducedNormalizationEmbedding_injective (I : Ideal R) :
    Function.Injective (reducedNormalizationEmbedding I) :=
  (normalizationInclusion_injective I).comp (reducedEmbedding_injective I)

/-- The whole original UNREDUCED quotient map into the actual normalized components. -/
def originalNormalizationMap (I : Ideal R) : (R ⧸ I) →+* NormalizationProduct I :=
  (normalizationInclusion I).comp (originalMap I)

/-- The actual original quotient map retains every entire original component normalization value. -/
theorem originalNormalizationMap_mk (I : Ideal R) (r : R) (p : Index I) :
    originalNormalizationMap I (Ideal.Quotient.mk I r) p =
      CurveNormalization.inclusion (Component I p) (Ideal.Quotient.mk p.1 r) := rfl

/-- Original quotient normalization maps factor through the literal reduced quotient on ALL elements. -/
theorem originalNormalizationMap_eq_reduced_comp (I : Ideal R) :
    originalNormalizationMap I = (reducedNormalizationEmbedding I).comp
      (Ideal.Quotient.factor I.le_radical) := by
  rw [originalNormalizationMap, originalMap_eq_reducedEmbedding_comp,
    reducedNormalizationEmbedding, RingHom.comp_assoc]

/-- The whole original quotient normalization map kills exactly its original nilradical. -/
theorem ker_originalNormalizationMap (I : Ideal R) :
    RingHom.ker (originalNormalizationMap I) = nilradical (R ⧸ I) := by
  ext x
  change normalizationInclusion I (originalMap I x) = 0 ↔ x ∈ nilradical (R ⧸ I)
  rw [map_eq_zero_iff _ (normalizationInclusion_injective I), ← RingHom.mem_ker,
    ker_originalMap_eq_nilradical]

/-- True perfect-field finite component normalizations and the actual finite index make the WHOLE original product map finite. -/
theorem normalizationMap_finite (F : Type*) [Field F] [PerfectField F]
    [Algebra F R] [Algebra.FiniteType F R] (I : Ideal R) : (normalizationMap I).Finite := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing F R
  let : ∀ p : Index I, Algebra R (CurveNormalization.Ring (Component I p)) := fun p =>
    ((CurveNormalization.inclusion (Component I p)).comp (Ideal.Quotient.mk p.1)).toAlgebra
  have : ∀ p : Index I, IsScalarTower R (Component I p)
      (CurveNormalization.Ring (Component I p)) := fun p => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ p : Index I, Module.Finite (Component I p)
      (CurveNormalization.Ring (Component I p)) := fun p => RingHom.finite_algebraMap.mp
      (CurveNormalization.finite_inclusion F (Component I p))
  have : ∀ p : Index I, Module.Finite R (CurveNormalization.Ring (Component I p)) :=
    fun p => Module.Finite.trans (Component I p) _
  change Module.Finite R (NormalizationProduct I)
  infer_instance

/-- The entire reduced embedding into actual normalized components is finite. -/
theorem reducedNormalizationEmbedding_finite (F : Type*) [Field F] [PerfectField F]
    [Algebra F R] [Algebra.FiniteType F R] (I : Ideal R) : (reducedNormalizationEmbedding I).Finite := by
  have he : (reducedNormalizationEmbedding I).comp (Ideal.Quotient.mk I.radical) =
      normalizationMap I := by
    ext r p
    rfl
  exact RingHom.Finite.of_comp_finite (he.symm ▸ normalizationMap_finite F I)

/-- The genuine map from the original UNREDUCED quotient into actual normalized components is finite. -/
theorem originalNormalizationMap_finite (F : Type*) [Field F] [PerfectField F]
    [Algebra F R] [Algebra.FiniteType F R] (I : Ideal R) : (originalNormalizationMap I).Finite := by
  have he : (originalNormalizationMap I).comp (Ideal.Quotient.mk I) = normalizationMap I := by
    ext r p
    rfl
  exact RingHom.Finite.of_comp_finite (he.symm ▸ normalizationMap_finite F I)

/-- Every whole original unreduced quotient prime has an actual normalized component lift. -/
theorem originalNormalizationMap_comap_surjective (F : Type*) [Field F] [PerfectField F]
    [Algebra F R] [Algebra.FiniteType F R] (I : Ideal R) :
    Function.Surjective (PrimeSpectrum.comap (originalNormalizationMap I)) := by
  let : Algebra (R ⧸ I) (NormalizationProduct I) := (originalNormalizationMap I).toAlgebra
  have : Module.Finite (R ⧸ I) (NormalizationProduct I) := originalNormalizationMap_finite F I
  intro ⟨P, hP⟩
  have : P.IsPrime := hP
  have hker : (⊥ : Ideal (NormalizationProduct I)).under (R ⧸ I) ≤ P := by
    change RingHom.ker (originalNormalizationMap I) ≤ P
    rw [ker_originalNormalizationMap]
    exact nilradical_le_prime P
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P
    (⊥ : Ideal (NormalizationProduct I)) hker
  exact ⟨⟨Q, hQ⟩, rfl⟩

/-- The actual entire original normalization-product map preserves every coefficient of any genuine commutative base ring. -/
def normalizationMapAlg (K : Type*) [CommRing K] [Algebra K R] (I : Ideal R) :
    R →ₐ[K] NormalizationProduct I where
  __ := normalizationMap I
  commutes' c := by
    funext p
    change algebraMap (Component I p) (CurveNormalization.Ring (Component I p))
      (algebraMap K (Component I p) c) =
        algebraMap K (CurveNormalization.Ring (Component I p)) c
    exact (IsScalarTower.algebraMap_apply K (Component I p) _ c).symm

/-- The actual UNREDUCED quotient coefficient structure is retained by the entire normalized-product homomorphism. -/
def originalNormalizationMapAlg (K : Type*) [CommRing K] [Algebra K R] (I : Ideal R) :
    (R ⧸ I) →ₐ[K] NormalizationProduct I where
  __ := originalNormalizationMap I
  commutes' c := by
    funext p
    change algebraMap (Component I p) (CurveNormalization.Ring (Component I p))
      (algebraMap K (Component I p) c) =
        algebraMap K (CurveNormalization.Ring (Component I p)) c
    exact (IsScalarTower.algebraMap_apply K (Component I p) _ c).symm

end EnvelopeProperty.ReducedComponents
