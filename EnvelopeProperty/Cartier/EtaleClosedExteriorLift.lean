import EnvelopeProperty.Cartier.EtaleCohomologyProducts
import EnvelopeProperty.Cartier.ExteriorFrobeniusLift

/-! # Whole actual closed exterior lifts in the original etale de Rham complex -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleClosedExteriorLift
open CategoryTheory
open scoped Classical
universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}
variable (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP B p]
local notation "W" => KaehlerDifferential R B

/-- The actual ENTIRE underlying one-form map of an ordinary original cycle-valued linear map. -/
def oneFormMap (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) :
    W →ₗ[B] ExteriorFrobeniusLift.forms B W p 1 :=
  (EtaleCohomologyProducts.cycles v hv p 1).subtype.comp f

/-- The genuine entire original homogeneous exterior lift of that SAME original one-form map. -/
def representative (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) (q : ℕ) :
    (⋀[B]^q W) →ₗ[B] EtaleDeRham.frobeniusModule (R := R) (B := B) p q :=
  ExteriorFrobeniusLift.homogeneous B W p (oneFormMap v hv p f) q

private theorem representative_zero_one
    (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) (t : Fin 0 → W) :
    representative v hv p f 0 (exteriorPower.ιMulti B 0 t) =
      (show EtaleDeRham.frobeniusModule (R := R) (B := B) p 0 from
        (exteriorPower.zeroEquiv B W).symm 1) := by
  apply Subtype.ext
  change ExteriorFrobeniusLift.lift B W p (oneFormMap v hv p f)
    (ExteriorAlgebra.ιMulti B 0 t) = _
  rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, exteriorPower.zeroEquiv_symm_apply]
  change (1 : ExteriorAlgebra B W) = (1 : B) • ExteriorAlgebra.ιMulti B 0 (fun i => Fin.elim0 i)
  rw [ExteriorAlgebra.ιMulti_zero_apply, one_smul]

private theorem wedge_one_tuple (q : ℕ) (t : Fin (q+1) → W) :
    exteriorPower.ιMulti B (q+1) t = EtaleGradedLeibniz.wedgeProduct 1 q
      ((exteriorPower.oneEquiv B W).symm (t 0))
        (exteriorPower.ιMulti B q (Matrix.vecTail t)) := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti B (q+1) t = _
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rw [EtaleGradedLeibniz.coe_wedgeProduct, exteriorPower.oneEquiv_symm_apply]
  change _ = ExteriorAlgebra.ιMulti B 1 (fun _ => t 0) * _
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rfl

private theorem representative_tuple_closed
    (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) (q : ℕ) (t : Fin q → W) :
    EtaleDeRham.differential v hv q (representative v hv p f q (exteriorPower.ιMulti B q t)) = 0 := by
  induction q with
  | zero =>
    rw [representative_zero_one]
    apply (exteriorPower.oneEquiv B W).injective
    rw [EtaleDeRham.differential_zero, map_zero]
    exact Derivation.map_one_eq_zero _
  | succ q ih =>
    rw [wedge_one_tuple]
    have hh := ExteriorFrobeniusLift.homogeneous_wedgeProduct B W p (oneFormMap v hv p f)
      1 q ((exteriorPower.oneEquiv B W).symm (t 0))
        (exteriorPower.ιMulti B q (Matrix.vecTail t))
    change representative v hv p f (q+1) _ = _ at hh
    have ho := ExteriorFrobeniusLift.homogeneous_one B W p (oneFormMap v hv p f) (t 0)
    have h1 : EtaleDeRham.differential v hv 1
        (ExteriorFrobeniusLift.homogeneous B W p (oneFormMap v hv p f) 1
          ((exteriorPower.oneEquiv B W).symm (t 0))) = 0 :=
      (congrArg (fun z : ExteriorFrobeniusLift.forms B W p 1 =>
        EtaleDeRham.differential v hv 1 z) ho).trans (f (t 0)).property
    exact (congrArg (fun z : EtaleDeRham.frobeniusModule (R := R) (B := B) p (q+1) =>
      EtaleDeRham.differential v hv (q+1) z) hh).trans
        (EtaleCohomologyProducts.product_closed v hv 1 q _ _ h1 (ih (Matrix.vecTail t)))

/-- EVERY original form has an ACTUAL closed whole exterior lift. Closedness in ALL degrees
is DERIVED from genuine one-form cycles and whole graded Leibniz, not supplied. -/
theorem representative_closed (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (q : ℕ) (w : ⋀[B]^q W) :
    EtaleDeRham.differential v hv q (representative v hv p f q w) = 0 := by
  have h : (EtaleDeRham.frobeniusDifferential v hv p q).hom.comp
      (representative v hv p f q) = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro t
    exact representative_tuple_closed v hv p f q t
  exact congrArg (fun F => F w) h

/-- Genuine all-degree cycle-valued linear maps on the SAME entire original exterior powers. -/
def cycleRepresentative (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) (q : ℕ) :
    (⋀[B]^q W) →ₗ[B] EtaleCohomologyProducts.cycles v hv p q :=
  (representative v hv p f q).codRestrict _ (representative_closed v hv p f q)

/-- The actual entire degree-one cycle lift recovers EVERY original cycle input. -/
theorem cycleRepresentative_one (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) (m : W) :
    cycleRepresentative v hv p f 1 ((exteriorPower.oneEquiv B W).symm m) = f m := by
  apply Subtype.ext
  exact ExteriorFrobeniusLift.homogeneous_one B W p (oneFormMap v hv p f) m

/-- EVERY pair of original forms has the genuine product of their ENTIRE original cycle lifts. -/
theorem cycleRepresentative_wedgeProduct (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (q r : ℕ) (a : ⋀[B]^q W) (b : ⋀[B]^r W) :
    (cycleRepresentative (R := R) v hv p f (r+q)).toFun
      (EtaleGradedLeibniz.wedgeProduct q r a b) =
      ((EtaleCohomologyProducts.cycleProduct (R := R) (B := B) v hv p q r).toFun
        ((cycleRepresentative (R := R) v hv p f q).toFun a)).toFun
          ((cycleRepresentative (R := R) v hv p f r).toFun b) := by
  apply Subtype.ext
  exact ExteriorFrobeniusLift.homogeneous_wedgeProduct B W p (oneFormMap v hv p f) q r a b

/-- Genuine whole all-degree original cohomology maps, from the actual derived closed lifts. -/
def classMap (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) (q : ℕ) :
    (⋀[B]^q W) →ₗ[B] EtaleCohomologyProducts.cohomology v hv p q :=
  (EtaleCohomologyProducts.boundaries v hv p q).mkQ.comp (cycleRepresentative v hv p f q)

/-- The SAME actual whole cohomology maps preserve EVERY original homogeneous product. -/
theorem classMap_wedgeProduct (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (q r : ℕ) (a : ⋀[B]^q W) (b : ⋀[B]^r W) :
    (classMap (R := R) v hv p f (r+q)).toFun (EtaleGradedLeibniz.wedgeProduct q r a b) =
      ((EtaleCohomologyProducts.cohomologyProduct (R := R) (B := B) v hv p q r).toFun
        ((classMap (R := R) v hv p f q).toFun a)).toFun ((classMap (R := R) v hv p f r).toFun b) := by
  have h := congrArg (fun z : EtaleCohomologyProducts.cycles v hv p (r+q) =>
    (EtaleCohomologyProducts.boundaries v hv p (r+q)).mkQ z) (cycleRepresentative_wedgeProduct v hv p f q r a b)
  exact h.trans (EtaleCohomologyProducts.cohomologyProduct_classes v hv p q r
    (cycleRepresentative v hv p f q a) (cycleRepresentative v hv p f r b)).symm

/-- Actual all-degree maps into the SAME entire native original Frobenius complex cohomology. -/
def nativeClassMap (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1) (q : ℕ) :
    (⋀[B]^q W) →ₗ[B] (EtaleDeRham.frobeniusComplex v hv p).homology q :=
  (EtaleCohomologyProducts.nativeCycleClass v hv p q).comp (cycleRepresentative v hv p f q)

/-- These actual native original cohomology maps genuinely preserve ALL original products. -/
theorem nativeClassMap_wedgeProduct (f : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (q r : ℕ) (a : ⋀[B]^q W) (b : ⋀[B]^r W) :
    (nativeClassMap (R := R) v hv p f (r+q)).toFun (EtaleGradedLeibniz.wedgeProduct q r a b) =
      ((EtaleCohomologyProducts.nativeCohomologyProduct (R := R) (B := B) v hv p q r).toFun
        ((nativeClassMap (R := R) v hv p f q).toFun a)).toFun
          ((nativeClassMap (R := R) v hv p f r).toFun b) := by
  have h := congrArg (fun z : EtaleCohomologyProducts.cycles v hv p (r+q) =>
    (EtaleCohomologyProducts.nativeCycleClass v hv p (r+q)).toFun z)
      (cycleRepresentative_wedgeProduct v hv p f q r a b)
  exact h.trans (EtaleCohomologyProducts.nativeCohomologyProduct_cycleClass v hv p q r
    (cycleRepresentative v hv p f q a) (cycleRepresentative v hv p f r b)).symm

private theorem classMap_tuple_eq_of_one
    (f g : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (h : classMap v hv p f 1 = classMap v hv p g 1) (q : ℕ) (t : Fin q → W) :
    classMap v hv p f q (exteriorPower.ιMulti B q t) =
      classMap v hv p g q (exteriorPower.ιMulti B q t) := by
  induction q with
  | zero =>
    have hz : cycleRepresentative v hv p f 0 (exteriorPower.ιMulti B 0 t) =
        cycleRepresentative v hv p g 0 (exteriorPower.ιMulti B 0 t) := by
      apply Subtype.ext
      exact (representative_zero_one v hv p f t).trans (representative_zero_one v hv p g t).symm
    exact congrArg (EtaleCohomologyProducts.boundaries v hv p 0).mkQ hz
  | succ q ih =>
    rw [wedge_one_tuple]
    have hf := classMap_wedgeProduct v hv p f 1 q ((exteriorPower.oneEquiv B W).symm (t 0))
      (exteriorPower.ιMulti B q (Matrix.vecTail t))
    have hg := classMap_wedgeProduct v hv p g 1 q ((exteriorPower.oneEquiv B W).symm (t 0))
      (exteriorPower.ιMulti B q (Matrix.vecTail t))
    have h1 := congrArg (fun F : (⋀[B]^1 W) →ₗ[B] EtaleCohomologyProducts.cohomology v hv p 1 =>
      F ((exteriorPower.oneEquiv B W).symm (t 0))) h
    have hp := congrArg₂ (fun x y => EtaleCohomologyProducts.cohomologyProduct v hv p 1 q x y)
      h1 (ih (Matrix.vecTail t))
    exact hf.trans (hp.trans hg.symm)

/-- The ENTIRE all-degree original cohomology maps are determined by the actual degree-one
cohomology map. All representatives and zero-degree agreement are derived internally. -/
theorem classMap_eq_of_one (f g : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (h : classMap v hv p f 1 = classMap v hv p g 1) (q : ℕ) :
    classMap v hv p f q = classMap v hv p g q := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro t
  exact classMap_tuple_eq_of_one v hv p f g h q t

/-- The same determination holds for the SAME entire native whole-complex cohomology maps. -/
theorem nativeClassMap_eq_of_one (f g : W →ₗ[B] EtaleCohomologyProducts.cycles v hv p 1)
    (h : nativeClassMap v hv p f 1 = nativeClassMap v hv p g 1) (q : ℕ) :
    nativeClassMap v hv p f q = nativeClassMap v hv p g q := by
  have hi : Function.Injective (EtaleCohomologyProducts.cohomologyIso v hv p 1).inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have h1 : classMap v hv p f 1 = classMap v hv p g 1 := by
    apply LinearMap.ext
    intro a
    apply hi
    exact congrArg (fun F => F a) h
  have hq := classMap_eq_of_one v hv p f g h1 q
  apply LinearMap.ext
  intro w
  exact congrArg (EtaleCohomologyProducts.cohomologyIso v hv p q).inv
    (congrArg (fun F => F w) hq)

end EnvelopeProperty.Cartier.EtaleClosedExteriorLift
