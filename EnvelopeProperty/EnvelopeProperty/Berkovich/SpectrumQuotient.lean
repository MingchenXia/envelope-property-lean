/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Spectrum

/-!
# Quotients and reduction of seminorm spectra

For an arbitrary commutative ring `A`, seminorms of `A ⧸ I` identify with seminorms
of `A` that vanish on `I`. The inverse genuinely descends each valuation to the
quotient. This identification is a homeomorphism for the evaluation topologies,
and quotient maps and all surjective ring maps induce closed embeddings.

The same constructions preserve a prescribed valuation on any commutative base
ring. In particular, absolute and relative seminorm spectra are unchanged under
quotienting by the nilradical. No field, triviality, finite type, or reducedness
assumption is required. These are spectra of real-valued ultrametric seminorms;
no boundedness condition or Banach-ring analytification is asserted.
-/

open scoped NNReal Topology
open Topology

noncomputable section

namespace EnvelopeProperty.Berkovich

namespace Spectrum

variable {A : Type*} [CommRing A]

/-- A ring isomorphism gives a homeomorphism of seminorm spectra. -/
def ringEquivHomeomorph {B : Type*} [CommRing B] (e : A ≃+* B) :
    Spectrum B ≃ₜ Spectrum A where
  toFun := comap e.toRingHom
  invFun := comap e.symm.toRingHom
  left_inv y := ext_val fun b => by simp
  right_inv x := ext_val fun a => by simp
  continuous_toFun := continuous_comap _
  continuous_invFun := continuous_comap _

@[simp]
theorem ringEquivHomeomorph_apply {B : Type*} [CommRing B] (e : A ≃+* B) (y : Spectrum B) :
    ringEquivHomeomorph e y = comap e.toRingHom y := rfl

/-- The seminorms vanishing on an ideal. -/
def zeroLocus (I : Ideal A) : Set (Spectrum A) := {x | I ≤ x.val.supp}

@[simp]
theorem mem_zeroLocus (I : Ideal A) (x : Spectrum A) : x ∈ zeroLocus I ↔ I ≤ x.val.supp :=
  Iff.rfl

theorem mem_zeroLocus_iff (I : Ideal A) (x : Spectrum A) :
    x ∈ zeroLocus I ↔ ∀ a ∈ I, x.val a = 0 := Iff.rfl

/-- Ideal vanishing is a closed condition for the evaluation topology. -/
theorem isClosed_zeroLocus (I : Ideal A) : IsClosed (zeroLocus I) := by
  have heq : zeroLocus I = ⋂ a ∈ I, {x : Spectrum A | x.val a = 0} := by
    ext x
    simp only [mem_zeroLocus_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_abs a) continuous_const

/-- Pullback along the quotient map. -/
def quotientComap (I : Ideal A) : Spectrum (A ⧸ I) → Spectrum A :=
  comap (Ideal.Quotient.mk I)

@[simp]
theorem quotientComap_val_apply (I : Ideal A) (y : Spectrum (A ⧸ I)) (a : A) :
    (quotientComap I y).val a = y.val (Ideal.Quotient.mk I a) := rfl

@[fun_prop]
theorem continuous_quotientComap (I : Ideal A) : Continuous (quotientComap I) :=
  continuous_comap _

theorem quotientComap_mem_zeroLocus (I : Ideal A) (y : Spectrum (A ⧸ I)) :
    quotientComap I y ∈ zeroLocus I :=
  y.val.self_le_supp_comap I

/-- A valuation vanishing on an ideal descends to the quotient ring. -/
def quotientLift (I : Ideal A) (x : Spectrum A) (hx : I ≤ x.val.supp) : Spectrum (A ⧸ I) :=
  ⟨x.val.onQuot hx⟩

@[simp]
theorem quotientLift_val_mk (I : Ideal A) (x : Spectrum A) (hx : I ≤ x.val.supp) (a : A) :
    (quotientLift I x hx).val (Ideal.Quotient.mk I a) = x.val a := rfl

@[simp]
theorem quotientComap_quotientLift (I : Ideal A) (x : Spectrum A) (hx : I ≤ x.val.supp) :
    quotientComap I (quotientLift I x hx) = x :=
  Spectrum.ext (x.val.onQuot_comap_eq hx)

theorem quotientComap_injective (I : Ideal A) : Function.Injective (quotientComap I) := by
  intro y₁ y₂ h
  refine ext_val fun b => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun x : Spectrum A => x.val a) h

@[simp]
theorem quotientLift_quotientComap (I : Ideal A) (y : Spectrum (A ⧸ I)) :
    quotientLift I (quotientComap I y) (quotientComap_mem_zeroLocus I y) = y :=
  quotientComap_injective I (quotientComap_quotientLift I _ _)

theorem range_quotientComap (I : Ideal A) : Set.range (quotientComap I) = zeroLocus I := by
  ext x
  refine ⟨?_, fun hx => ⟨quotientLift I x hx, quotientComap_quotientLift I x hx⟩⟩
  rintro ⟨y, rfl⟩
  exact quotientComap_mem_zeroLocus I y

@[fun_prop]
theorem continuous_quotientLift (I : Ideal A) :
    Continuous fun x : zeroLocus I => quotientLift I x.1 x.2 := by
  rw [continuous_iff]
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact (continuous_abs a).comp continuous_subtype_val

/-- Seminorms on a quotient are homeomorphic to the ideal's zero locus. -/
def quotientHomeomorph (I : Ideal A) : Spectrum (A ⧸ I) ≃ₜ zeroLocus I where
  toFun y := ⟨quotientComap I y, quotientComap_mem_zeroLocus I y⟩
  invFun x := quotientLift I x.1 x.2
  left_inv := quotientLift_quotientComap I
  right_inv x := Subtype.ext (quotientComap_quotientLift I x.1 x.2)
  continuous_toFun := (continuous_quotientComap I).subtype_mk _
  continuous_invFun := continuous_quotientLift I

@[simp]
theorem quotientHomeomorph_apply_coe (I : Ideal A) (y : Spectrum (A ⧸ I)) :
    (quotientHomeomorph I y : Spectrum A) = quotientComap I y := rfl

@[simp]
theorem quotientHomeomorph_apply_val (I : Ideal A) (y : Spectrum (A ⧸ I)) (a : A) :
    (quotientHomeomorph I y).1.val a = y.val (Ideal.Quotient.mk I a) := rfl

theorem isClosedEmbedding_quotientComap (I : Ideal A) :
    IsClosedEmbedding (quotientComap I) := by
  refine ⟨?_, by rw [range_quotientComap]; exact isClosed_zeroLocus I⟩
  exact IsEmbedding.subtypeVal.comp (quotientHomeomorph I).isEmbedding

/-- A surjective ring map induces a closed embedding of seminorm spectra. -/
theorem isClosedEmbedding_comap_of_surjective {B : Type*} [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) : IsClosedEmbedding (comap φ) := by
  let e := φ.quotientKerEquivOfSurjective hφ
  have hcomp : quotientComap (RingHom.ker φ) ∘ ringEquivHomeomorph e = comap φ := by
    funext y
    refine ext_val fun a => ?_
    change y.val (e (Ideal.Quotient.mk (RingHom.ker φ) a)) = y.val (φ a)
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [← hcomp]
  exact (isClosedEmbedding_quotientComap (RingHom.ker φ)).comp
    (ringEquivHomeomorph e).isClosedEmbedding

/-- Every real-valued multiplicative seminorm vanishes on the nilradical. -/
theorem nilradical_le_supp (x : Spectrum A) : nilradical A ≤ x.val.supp :=
  nilradical_le_prime x.val.supp

theorem val_eq_zero_of_isNilpotent (x : Spectrum A) {a : A} (ha : IsNilpotent a) :
    x.val a = 0 :=
  nilradical_le_supp x (mem_nilradical.2 ha)

/-- Quotienting by the nilradical leaves the seminorm spectrum unchanged. -/
def reductionHomeomorph : Spectrum (A ⧸ nilradical A) ≃ₜ Spectrum A where
  toFun := quotientComap (nilradical A)
  invFun x := quotientLift (nilradical A) x (nilradical_le_supp x)
  left_inv := quotientLift_quotientComap (nilradical A)
  right_inv x := quotientComap_quotientLift (nilradical A) x (nilradical_le_supp x)
  continuous_toFun := continuous_quotientComap (nilradical A)
  continuous_invFun := (continuous_quotientLift (nilradical A)).comp
    (continuous_id.subtype_mk fun x => nilradical_le_supp x)

@[simp]
theorem reductionHomeomorph_val_apply (y : Spectrum (A ⧸ nilradical A)) (a : A) :
    (reductionHomeomorph y).val a = y.val (Ideal.Quotient.mk (nilradical A) a) := rfl

@[simp]
theorem reductionHomeomorph_symm_val_mk (x : Spectrum A) (a : A) :
    (reductionHomeomorph.symm x).val (Ideal.Quotient.mk (nilradical A) a) = x.val a := rfl

end Spectrum

namespace RelativeSpectrum

variable {R : Type*} [CommRing R] (v : Valuation R ℝ≥0)
  {A : Type*} [CommRing A] [Algebra R A]

/-- An algebra isomorphism preserves a prescribed base valuation and induces a homeomorphism. -/
def algEquivHomeomorph {B : Type*} [CommRing B] [Algebra R B] (e : A ≃ₐ[R] B) :
    RelativeSpectrum v B ≃ₜ RelativeSpectrum v A where
  toFun := comap e.toAlgHom
  invFun := comap e.symm.toAlgHom
  left_inv y := Subtype.ext (Spectrum.ext_val fun b => by simp)
  right_inv x := Subtype.ext (Spectrum.ext_val fun a => by simp)
  continuous_toFun := continuous_comap _
  continuous_invFun := continuous_comap _

/-- Relative seminorms vanishing on an ideal. -/
def zeroLocus (I : Ideal A) : Set (RelativeSpectrum v A) := {x | I ≤ x.1.val.supp}

@[simp]
theorem mem_zeroLocus (I : Ideal A) (x : RelativeSpectrum v A) :
    x ∈ zeroLocus v I ↔ I ≤ x.1.val.supp := Iff.rfl

theorem isClosed_zeroLocus (I : Ideal A) : IsClosed (zeroLocus v I) :=
  (Spectrum.isClosed_zeroLocus I).preimage continuous_subtype_val

/-- Relative pullback along the quotient algebra map. -/
def quotientComap (I : Ideal A) : RelativeSpectrum v (A ⧸ I) → RelativeSpectrum v A :=
  comap (Ideal.Quotient.mkₐ R I)

@[simp]
theorem quotientComap_val_apply (I : Ideal A) (y : RelativeSpectrum v (A ⧸ I)) (a : A) :
    (quotientComap v I y).1.val a = y.1.val (Ideal.Quotient.mk I a) := rfl

@[fun_prop]
theorem continuous_quotientComap (I : Ideal A) : Continuous (quotientComap v I) :=
  continuous_comap _

theorem quotientComap_mem_zeroLocus (I : Ideal A) (y : RelativeSpectrum v (A ⧸ I)) :
    quotientComap v I y ∈ zeroLocus v I :=
  Spectrum.quotientComap_mem_zeroLocus I y.1

/-- Descend a relative seminorm to the quotient while retaining its prescribed base values. -/
def quotientLift (I : Ideal A) (x : RelativeSpectrum v A) (hx : I ≤ x.1.val.supp) :
    RelativeSpectrum v (A ⧸ I) :=
  ⟨Spectrum.quotientLift I x.1 hx, fun r => by
    change x.1.val (algebraMap R A r) = v r
    exact x.2 r⟩

@[simp]
theorem quotientLift_val_mk (I : Ideal A) (x : RelativeSpectrum v A)
    (hx : I ≤ x.1.val.supp) (a : A) :
    (quotientLift v I x hx).1.val (Ideal.Quotient.mk I a) = x.1.val a := rfl

@[simp]
theorem quotientComap_quotientLift (I : Ideal A) (x : RelativeSpectrum v A)
    (hx : I ≤ x.1.val.supp) : quotientComap v I (quotientLift v I x hx) = x :=
  Subtype.ext (Spectrum.quotientComap_quotientLift I x.1 hx)

theorem quotientComap_injective (I : Ideal A) : Function.Injective (quotientComap v I) := by
  intro y₁ y₂ h
  exact Subtype.ext (Spectrum.quotientComap_injective I (congrArg Subtype.val h))

@[simp]
theorem quotientLift_quotientComap (I : Ideal A) (y : RelativeSpectrum v (A ⧸ I)) :
    quotientLift v I (quotientComap v I y) (quotientComap_mem_zeroLocus v I y) = y :=
  quotientComap_injective v I (quotientComap_quotientLift v I _ _)

theorem range_quotientComap (I : Ideal A) :
    Set.range (quotientComap v I) = zeroLocus v I := by
  ext x
  refine ⟨?_, fun hx => ⟨quotientLift v I x hx, quotientComap_quotientLift v I x hx⟩⟩
  rintro ⟨y, rfl⟩
  exact quotientComap_mem_zeroLocus v I y

@[fun_prop]
theorem continuous_quotientLift (I : Ideal A) :
    Continuous fun x : zeroLocus v I => quotientLift v I x.1 x.2 := by
  exact ((Spectrum.continuous_quotientLift I).comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk fun x => x.2)).subtype_mk _

/-- Relative quotient seminorms identify homeomorphically with the relative ideal zero locus. -/
def quotientHomeomorph (I : Ideal A) : RelativeSpectrum v (A ⧸ I) ≃ₜ zeroLocus v I where
  toFun y := ⟨quotientComap v I y, quotientComap_mem_zeroLocus v I y⟩
  invFun x := quotientLift v I x.1 x.2
  left_inv := quotientLift_quotientComap v I
  right_inv x := Subtype.ext (quotientComap_quotientLift v I x.1 x.2)
  continuous_toFun := (continuous_quotientComap v I).subtype_mk _
  continuous_invFun := continuous_quotientLift v I

@[simp]
theorem quotientHomeomorph_apply_val (I : Ideal A) (y : RelativeSpectrum v (A ⧸ I)) (a : A) :
    (quotientHomeomorph v I y).1.1.val a = y.1.val (Ideal.Quotient.mk I a) := rfl

theorem isClosedEmbedding_quotientComap (I : Ideal A) :
    IsClosedEmbedding (quotientComap v I) := by
  refine ⟨?_, by rw [range_quotientComap]; exact isClosed_zeroLocus v I⟩
  exact IsEmbedding.subtypeVal.comp (quotientHomeomorph v I).isEmbedding

/-- A surjective algebra map induces a closed embedding preserving any prescribed base valuation. -/
theorem isClosedEmbedding_comap_of_surjective {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (hφ : Function.Surjective φ) : IsClosedEmbedding (comap (v := v) φ) := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  have hcomp : quotientComap v (RingHom.ker φ) ∘ algEquivHomeomorph v e = comap φ := by
    funext y
    refine Subtype.ext (Spectrum.ext_val fun a => ?_)
    change y.1.val (e (Ideal.Quotient.mk (RingHom.ker φ) a)) = y.1.val (φ a)
    rw [Ideal.quotientKerAlgEquivOfSurjective_mk]
  rw [← hcomp]
  exact (isClosedEmbedding_quotientComap v (RingHom.ker φ)).comp
    (algEquivHomeomorph v e).isClosedEmbedding

/-- Relative seminorm spectra are unchanged under quotienting by the nilradical. -/
def reductionHomeomorph : RelativeSpectrum v (A ⧸ nilradical A) ≃ₜ RelativeSpectrum v A where
  toFun := quotientComap v (nilradical A)
  invFun x := quotientLift v (nilradical A) x (Spectrum.nilradical_le_supp x.1)
  left_inv := quotientLift_quotientComap v (nilradical A)
  right_inv x := quotientComap_quotientLift v (nilradical A) x (Spectrum.nilradical_le_supp x.1)
  continuous_toFun := continuous_quotientComap v (nilradical A)
  continuous_invFun := (continuous_quotientLift v (nilradical A)).comp
    (continuous_id.subtype_mk fun x => Spectrum.nilradical_le_supp x.1)

@[simp]
theorem reductionHomeomorph_val_apply (y : RelativeSpectrum v (A ⧸ nilradical A)) (a : A) :
    (reductionHomeomorph v y).1.val a = y.1.val (Ideal.Quotient.mk (nilradical A) a) := rfl

@[simp]
theorem reductionHomeomorph_symm_val_mk (x : RelativeSpectrum v A) (a : A) :
    ((reductionHomeomorph v).symm x).1.val (Ideal.Quotient.mk (nilradical A) a) = x.1.val a := rfl

end RelativeSpectrum

end EnvelopeProperty.Berkovich
