/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.InfinitesimalIdempotents
import EnvelopeProperty.ProperBirationalSections
import EnvelopeProperty.AdicCompletionEvalCompatibility

/-! # Original adic coefficient maps into the actual infinitesimal section limit -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.AdicCompletionSections
open InfinitesimalSchemes
variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The ORIGINAL coefficient RingHom of the literal order-n pullback. -/
def coefficient (n : ℕ) : ring I n →+* Γ(model I f n,⊤) :=
  ProperBirationalSections.coefficientMap (structureMap I f n)

/-- BOTH original coefficient/section corners of EVERY whole transition agree as actual RingHoms. -/
theorem transition_coefficient {n m : ℕ} (h : n≤m) :
    ((transition I f h).appTop.hom).comp (coefficient I f m) =
      (coefficient I f n).comp (Ideal.Quotient.factorPow I h) := by
  change ((Scheme.ΓSpecIso (.of (ring I m))).inv ≫
    (structureMap I f m).appTop ≫ (transition I f h).appTop).hom =
      (CommRingCat.ofHom (Ideal.Quotient.factorPow I h) ≫
        (Scheme.ΓSpecIso (.of (ring I n))).inv ≫ (structureMap I f n).appTop).hom
  rw [← Scheme.Hom.comp_appTop,transition_structureMap,Scheme.Hom.comp_appTop,
    ← Category.assoc,← Scheme.ΓSpecIso_inv_naturality,Category.assoc]

/-- EVERY actual transition preserves EVERY original quotient coefficient element. -/
theorem restriction_coefficient {n m : ℕ} (h : n≤m) (a : ring I (m+1)) :
    InfinitesimalIdempotents.restriction I f h (coefficient I f (m+1) a)=
      coefficient I f (n+1) (Ideal.Quotient.factorPow I (Nat.succ_le_succ h) a) :=
  congrArg (fun g => g a) (transition_coefficient I f (Nat.succ_le_succ h))

/-- The ORIGINAL R coefficients form a genuine whole compatible section family. -/
def coefficientFamily : R →+* InfinitesimalIdempotents.compatibleSections I f where
  toFun r := ⟨fun n => coefficient I f (n+1) (Ideal.Quotient.mk (I^(n+1)) r),by
    intro n m h
    rw [restriction_coefficient]
    rfl⟩
  map_one' := by
    apply Subtype.ext
    funext n
    exact map_one ((coefficient I f (n+1)).comp (Ideal.Quotient.mk (I^(n+1))))
  map_mul' r s := by
    apply Subtype.ext
    funext n
    exact map_mul ((coefficient I f (n+1)).comp (Ideal.Quotient.mk (I^(n+1)))) r s
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero ((coefficient I f (n+1)).comp (Ideal.Quotient.mk (I^(n+1))))
  map_add' r s := by
    apply Subtype.ext
    funext n
    exact map_add ((coefficient I f (n+1)).comp (Ideal.Quotient.mk (I^(n+1)))) r s

/-- EVERY original coefficient coordinate is EXACTLY the genuine original quotient/section composite. -/
theorem coefficientFamily_apply (r : R) (n : ℕ) :
    (coefficientFamily I f r).1 n=coefficient I f (n+1) (Ideal.Quotient.mk (I^(n+1)) r) := rfl

/-- The ACTUAL completion coefficient RingHom into the ORIGINAL compatible-section subring. -/
def completionCoefficient : AdicCompletion I R →+* InfinitesimalIdempotents.compatibleSections I f where
  toFun a := ⟨fun n => coefficient I f (n+1) (AdicCompletion.evalₐ I (n+1) a),by
    intro n m h
    rw [restriction_coefficient,AdicCompletionEvalCompatibility.factorPow_eval]⟩
  map_one' := by
    apply Subtype.ext
    funext n
    exact map_one ((coefficient I f (n+1)).comp (AdicCompletion.evalₐ I (n+1)).toRingHom)
  map_mul' a b := by
    apply Subtype.ext
    funext n
    exact map_mul ((coefficient I f (n+1)).comp (AdicCompletion.evalₐ I (n+1)).toRingHom) a b
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero ((coefficient I f (n+1)).comp (AdicCompletion.evalₐ I (n+1)).toRingHom)
  map_add' a b := by
    apply Subtype.ext
    funext n
    exact map_add ((coefficient I f (n+1)).comp (AdicCompletion.evalₐ I (n+1)).toRingHom) a b

/-- EVERY genuine evaluation coordinate retains the ENTIRE original completion and coefficient maps. -/
theorem completionCoefficient_apply (a : AdicCompletion I R) (n : ℕ) :
    (completionCoefficient I f a).1 n=coefficient I f (n+1) (AdicCompletion.evalₐ I (n+1) a) := rfl

/-- The SAME actual completion map recovers every ORIGINAL R coefficient. -/
theorem completionCoefficient_of (r : R) :
    completionCoefficient I f (AdicCompletion.of I R r)=coefficientFamily I f r := by
  apply Subtype.ext
  funext n
  simp only [completionCoefficient_apply,coefficientFamily_apply,AdicCompletion.evalₐ_of]

/-- The WHOLE original R/completion/section-limit triangle commutes as genuine RingHoms. -/
theorem completionCoefficient_comp_algebraMap :
    (completionCoefficient I f).comp (algebraMap R (AdicCompletion I R))=coefficientFamily I f := by
  apply RingHom.ext
  intro r
  exact completionCoefficient_of I f r

/-- An actual original completion idempotent gives its whole compatible idempotent family. -/
def idempotentFamily (a : {a : AdicCompletion I R // IsIdempotentElem a}) :
    {s : InfinitesimalIdempotents.compatibleSections I f // IsIdempotentElem s} :=
  ⟨completionCoefficient I f a.1,a.2.map (completionCoefficient I f)⟩

/-- Its original order-one section is EXACTLY the SAME completion evaluation followed by the original coefficient map. -/
theorem idempotentFamily_zero (a : {a : AdicCompletion I R // IsIdempotentElem a}) :
    (InfinitesimalIdempotents.coordinate I f (idempotentFamily I f a) 0).1=
      coefficient I f 1 (AdicCompletion.evalₐ I 1 a.1) := rfl

end EnvelopeProperty.AdicCompletionSections
