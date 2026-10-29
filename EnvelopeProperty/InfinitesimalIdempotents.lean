/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.InfinitesimalSchemes

/-! # Actual compatible original idempotents in the literal infinitesimal section limit -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.InfinitesimalIdempotents
open InfinitesimalSchemes
variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The ORIGINAL whole section restriction between actual positive infinitesimal models, indexed by n+1. -/
def restriction {n m : ℕ} (h : n≤m) : Γ(model I f (m+1),⊤) →+* Γ(model I f (n+1),⊤) :=
  (transition I f (Nat.succ_le_succ h)).appTop.hom

/-- Every original idempotent on the order-one model has its genuinely unique whole positive-order lift. -/
def lift (e : {e : Γ(model I f 1,⊤) // IsIdempotentElem e}) (n : ℕ) :
    {e : Γ(model I f (n+1),⊤) // IsIdempotentElem e} :=
  (idempotentRestrictionEquiv I f (by omega : 0<1) (Nat.succ_le_succ (Nat.zero_le n))).symm e

/-- The true original section restriction recovers the ENTIRE original idempotent on the order-one model. -/
theorem restriction_lift (e : {e : Γ(model I f 1,⊤) // IsIdempotentElem e}) (n : ℕ) :
    SchemeIdempotentRestriction.map (transition I f (Nat.succ_le_succ (Nat.zero_le n)))
      (lift I f e n)=e :=
  (idempotentRestrictionEquiv I f (by omega : 0<1) (Nat.succ_le_succ (Nat.zero_le n))).apply_symm_apply e

/-- Genuine whole transition composition and actual idempotent injection DERIVE EVERY compatibility equation. -/
theorem lift_compatible (e : {e : Γ(model I f 1,⊤) // IsIdempotentElem e})
    {n m : ℕ} (h : n≤m) : restriction I f h (lift I f e m).1=(lift I f e n).1 := by
  have heq : SchemeIdempotentRestriction.map (transition I f (Nat.succ_le_succ h))
      (lift I f e m)=lift I f e n := by
    apply (idempotentRestrictionEquiv I f (by omega : 0<1)
      (Nat.succ_le_succ (Nat.zero_le n))).injective
    change (SchemeIdempotentRestriction.map (transition I f (Nat.succ_le_succ (Nat.zero_le n))) ∘
      SchemeIdempotentRestriction.map (transition I f (Nat.succ_le_succ h))) (lift I f e m) =
        SchemeIdempotentRestriction.map (transition I f (Nat.succ_le_succ (Nat.zero_le n))) (lift I f e n)
    rw [← SchemeIdempotentRestriction.map_comp,transition_comp,
      restriction_lift,restriction_lift]
  exact congrArg Subtype.val heq


/-- The ACTUAL inverse-limit ring is the genuine subring of ENTIRE original compatible section families. -/
def compatibleSections : Subring (∀ n : ℕ, Γ(model I f (n+1),⊤)) where
  carrier := {s | ∀ n m (h : n≤m), restriction I f h (s m)=s n}
  one_mem' := by intro n m h; exact map_one _
  mul_mem' := by intro s t hs ht n m h; rw [Pi.mul_apply,map_mul,hs n m h,ht n m h];rfl
  zero_mem' := by intro n m h; exact map_zero _
  add_mem' := by intro s t hs ht n m h; rw [Pi.add_apply,map_add,hs n m h,ht n m h];rfl
  neg_mem' := by intro s hs n m h; rw [Pi.neg_apply,map_neg,hs n m h];rfl

/-- The uniquely constructed original lifts form an ACTUAL idempotent of the whole compatible-section ring. -/
def liftFamily (e : {e : Γ(model I f 1,⊤) // IsIdempotentElem e}) :
    {s : compatibleSections I f // IsIdempotentElem s} := by
  refine ⟨⟨fun n => (lift I f e n).1,fun n m h => lift_compatible I f e h⟩,?_⟩
  apply Subtype.ext
  funext n
  exact (lift I f e n).2

/-- The actual zero-index coordinate is the SAME original order-one model, with its ENTIRE original idempotent. -/
theorem lift_zero (e : {e : Γ(model I f 1,⊤) // IsIdempotentElem e}) : lift I f e 0=e := by
  have h := restriction_lift I f e 0
  rw [transition_self,SchemeIdempotentRestriction.map_id] at h
  exact h

/-- Every original coordinate of an actual idempotent compatible family is a true WHOLE section idempotent. -/
def coordinate (e : {s : compatibleSections I f // IsIdempotentElem s}) (n : ℕ) :
    {s : Γ(model I f (n+1),⊤) // IsIdempotentElem s} :=
  ⟨e.1.1 n,congrArg (fun s : compatibleSections I f => s.1 n) e.2⟩

/-- Evaluation on the ORIGINAL order-one model genuinely bijects the ACTUAL inverse-limit idempotents. -/
def familyEquiv : {e : Γ(model I f 1,⊤) // IsIdempotentElem e} ≃
    {s : compatibleSections I f // IsIdempotentElem s} where
  toFun := liftFamily I f
  invFun e := coordinate I f e 0
  left_inv e := lift_zero I f e
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    funext n
    have hleft : SchemeIdempotentRestriction.map (transition I f (Nat.succ_le_succ (Nat.zero_le n)))
        (coordinate I f e n)=coordinate I f e 0 := by
      apply Subtype.ext
      exact e.1.2 0 n (Nat.zero_le n)
    have heq := (idempotentRestrictionEquiv I f (by omega : 0<1)
      (Nat.succ_le_succ (Nat.zero_le n))).injective
        ((restriction_lift I f (coordinate I f e 0) n).trans hleft.symm)
    exact congrArg Subtype.val heq

end EnvelopeProperty.InfinitesimalIdempotents
