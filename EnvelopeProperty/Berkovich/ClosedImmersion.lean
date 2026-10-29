/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.Basic
import EnvelopeProperty.Berkovich.SpectrumBridge
import EnvelopeProperty.Berkovich.SpectrumQuotient

/-!
# Analytification of affine closed immersions

The analytification of `Spec (A ⧸ I)` is the closed subspace of `Berk k A` on which
every element of `I` vanishes. The inverse is the seminorm induced on the quotient.
As a consequence, a surjective algebra homomorphism induces a closed embedding
on affine analytifications.

This supplies the affine closed-immersion implication used in Fang–Han–Xia,
§5.6, proof of `prop:projection-step`: the restriction of the finite projection
to the analytic closed subset is injective. The results hold for any commutative
algebra over any trivially valued field; reducedness and finite type are not needed.
-/

open scoped NNReal Topology
open Topology Classical

noncomputable section

namespace EnvelopeProperty.Berk

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-! ### Functoriality and algebra isomorphisms -/

@[simp]
theorem comap_comp {B C : Type*} [CommRing B] [CommRing C] [Algebra k B] [Algebra k C]
    (φ : A →ₐ[k] B) (ψ : B →ₐ[k] C) (x : Berk k C) :
    comap (ψ.comp φ) x = comap φ (comap ψ x) := rfl

/-- An algebra isomorphism induces a homeomorphism on affine analytifications. -/
def algEquivHomeomorph {B : Type*} [CommRing B] [Algebra k B] (e : A ≃ₐ[k] B) :
    Berk k B ≃ₜ Berk k A where
  toFun := comap e.toAlgHom
  invFun := comap e.symm.toAlgHom
  left_inv y := Berk.ext (Valuation.ext fun b => by simp)
  right_inv x := Berk.ext (Valuation.ext fun a => by simp)
  continuous_toFun := continuous_comap _
  continuous_invFun := continuous_comap _

@[simp]
theorem algEquivHomeomorph_apply {B : Type*} [CommRing B] [Algebra k B]
    (e : A ≃ₐ[k] B) (y : Berk k B) :
    algEquivHomeomorph e y = comap e.toAlgHom y := rfl

/-! ### The analytic zero locus of an ideal -/

/-- The analytic closed subset defined by an ideal: the points whose seminorm vanishes on it. -/
def zeroLocus (I : Ideal A) : Set (Berk k A) := {x | I ≤ x.val.supp}

@[simp]
theorem mem_zeroLocus (I : Ideal A) (x : Berk k A) : x ∈ zeroLocus I ↔ I ≤ x.val.supp :=
  Iff.rfl

theorem mem_zeroLocus_iff (I : Ideal A) (x : Berk k A) :
    x ∈ zeroLocus I ↔ ∀ a ∈ I, x.val a = 0 := Iff.rfl

/-- Vanishing on all elements of an ideal is a closed condition. -/
theorem isClosed_zeroLocus (I : Ideal A) : IsClosed (zeroLocus (k := k) I) := by
  have heq : zeroLocus (k := k) I = ⋂ a ∈ I, {x : Berk k A | x.val a = 0} := by
    ext x
    simp only [mem_zeroLocus_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_biInter fun a _ => isClosed_eq (continuous_abs a) continuous_const

/-! ### Quotient analytification -/

/-- Restriction along `A → A ⧸ I`, the analytification of the affine closed immersion. -/
def quotientComap (I : Ideal A) : Berk k (A ⧸ I) → Berk k A :=
  comap (Ideal.Quotient.mkₐ k I)

/-- The quotient pullback agrees with the quotient pullback in the relative spectrum. -/
@[simp]
theorem relativeSpectrumHomeomorph_quotientComap (I : Ideal A) (y : Berk k (A ⧸ I)) :
    relativeSpectrumHomeomorph (quotientComap I y) =
      Berkovich.RelativeSpectrum.quotientComap (1 : Valuation k ℝ≥0) I
        (relativeSpectrumHomeomorph y) :=
  relativeSpectrumHomeomorph_comap (Ideal.Quotient.mkₐ k I) y

@[simp]
theorem quotientComap_val_apply (I : Ideal A) (y : Berk k (A ⧸ I)) (a : A) :
    (quotientComap I y).val a = y.val (Ideal.Quotient.mk I a) := rfl

@[fun_prop]
theorem continuous_quotientComap (I : Ideal A) : Continuous (quotientComap (k := k) I) :=
  continuous_comap _

/-- The pullback of a seminorm on a quotient vanishes on the quotient ideal. -/
theorem quotientComap_mem_zeroLocus (I : Ideal A) (y : Berk k (A ⧸ I)) :
    quotientComap I y ∈ zeroLocus I :=
  y.val.self_le_supp_comap I

/-- The point of the quotient induced by a seminorm vanishing on the quotient ideal. -/
def quotientLift (I : Ideal A) (x : Berk k A) (hx : I ≤ x.val.supp) : Berk k (A ⧸ I) where
  val := x.val.onQuot hx
  val_algebraMap c hc := by
    change x.val (algebraMap k A c) = 1
    exact x.val_algebraMap c hc

@[simp]
theorem quotientLift_val_mk (I : Ideal A) (x : Berk k A) (hx : I ≤ x.val.supp) (a : A) :
    (quotientLift I x hx).val (Ideal.Quotient.mk I a) = x.val a := rfl

@[simp]
theorem quotientComap_quotientLift (I : Ideal A) (x : Berk k A) (hx : I ≤ x.val.supp) :
    quotientComap I (quotientLift I x hx) = x :=
  Berk.ext (x.val.onQuot_comap_eq hx)

/-- Restriction to the coordinate ring is injective because every quotient element
has a representative. -/
theorem quotientComap_injective (I : Ideal A) : Function.Injective (quotientComap (k := k) I) := by
  intro y₁ y₂ h
  refine Berk.ext (Valuation.ext fun b => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact congrArg (fun x : Berk k A => x.val a) h

@[simp]
theorem quotientLift_quotientComap (I : Ideal A) (y : Berk k (A ⧸ I)) :
    quotientLift I (quotientComap I y) (quotientComap_mem_zeroLocus I y) = y :=
  quotientComap_injective I (quotientComap_quotientLift I _ _)

/-- The quotient restriction map has precisely the analytic zero locus as image. -/
theorem range_quotientComap (I : Ideal A) :
    Set.range (quotientComap (k := k) I) = zeroLocus I := by
  ext x
  refine ⟨?_, fun hx => ⟨quotientLift I x hx, quotientComap_quotientLift I x hx⟩⟩
  rintro ⟨y, rfl⟩
  exact quotientComap_mem_zeroLocus I y

@[fun_prop]
theorem continuous_quotientLift (I : Ideal A) :
    Continuous fun x : zeroLocus (k := k) I => quotientLift I x.1 x.2 := by
  rw [continuous_iff]
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact (continuous_abs a).comp continuous_subtype_val

/-- The analytification of `Spec (A ⧸ I)` is the analytic zero locus of `I`. -/
def quotientHomeomorph (I : Ideal A) : Berk k (A ⧸ I) ≃ₜ zeroLocus (k := k) I where
  toFun y := ⟨quotientComap I y, quotientComap_mem_zeroLocus I y⟩
  invFun x := quotientLift I x.1 x.2
  left_inv := quotientLift_quotientComap I
  right_inv x := Subtype.ext (quotientComap_quotientLift I x.1 x.2)
  continuous_toFun := (continuous_quotientComap I).subtype_mk _
  continuous_invFun := continuous_quotientLift I

@[simp]
theorem quotientHomeomorph_apply_coe (I : Ideal A) (y : Berk k (A ⧸ I)) :
    (quotientHomeomorph I y : Berk k A) = quotientComap I y := rfl

@[simp]
theorem quotientHomeomorph_apply_val (I : Ideal A) (y : Berk k (A ⧸ I)) (a : A) :
    (quotientHomeomorph I y).1.val a = y.val (Ideal.Quotient.mk I a) := rfl

/-- The analytification of an affine quotient is a closed embedding. -/
theorem isClosedEmbedding_quotientComap (I : Ideal A) :
    IsClosedEmbedding (quotientComap (k := k) I) := by
  refine ⟨?_, by rw [range_quotientComap]; exact isClosed_zeroLocus I⟩
  exact IsEmbedding.subtypeVal.comp (quotientHomeomorph I).isEmbedding

/-! ### General surjective algebra homomorphisms -/

/-- A closed immersion of affine schemes induces a closed embedding on analytifications. -/
theorem isClosedEmbedding_comap_of_surjective {B : Type*} [CommRing B] [Algebra k B]
    (φ : A →ₐ[k] B) (hφ : Function.Surjective φ) : IsClosedEmbedding (comap (k := k) φ) := by
  let eA := relativeSpectrumHomeomorph (k := k) (A := A)
  let eB := relativeSpectrumHomeomorph (k := k) (A := B)
  have hcomp : comap φ = eA.symm ∘ Berkovich.RelativeSpectrum.comap φ ∘ eB := by
    funext y
    apply eA.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact relativeSpectrumHomeomorph_comap φ y
  rw [hcomp]
  exact eA.symm.isClosedEmbedding.comp
    ((Berkovich.RelativeSpectrum.isClosedEmbedding_comap_of_surjective
      (1 : Valuation k ℝ≥0) φ hφ).comp eB.isClosedEmbedding)

/-- If a morphism restricts to a closed immersion on an affine closed subset,
its analytification is injective on that subset. -/
theorem comap_injOn_zeroLocus_of_surjective_quotient {B : Type*} [CommRing B] [Algebra k B]
    (φ : B →ₐ[k] A) (I : Ideal A)
    (hφ : Function.Surjective ((Ideal.Quotient.mkₐ k I).comp φ)) :
    Set.InjOn (comap φ) (zeroLocus I) := by
  intro y hy y' hy' h
  have hlift : quotientLift I y hy = quotientLift I y' hy' := by
    apply (isClosedEmbedding_comap_of_surjective ((Ideal.Quotient.mkₐ k I).comp φ) hφ).injective
    rw [comap_comp, comap_comp]
    change comap φ (quotientComap I (quotientLift I y hy)) =
      comap φ (quotientComap I (quotientLift I y' hy'))
    rw [quotientComap_quotientLift I y hy, quotientComap_quotientLift I y' hy']
    exact h
  have heq := congrArg (quotientComap I) hlift
  rw [quotientComap_quotientLift I y hy, quotientComap_quotientLift I y' hy'] at heq
  exact heq

end EnvelopeProperty.Berk
