import EnvelopeProperty.DeligneIllusie.WittTwoRelativeLift
import EnvelopeProperty.Cartier.RelativeFrobenius

/-! # The genuine LEFT-Witt-copy residue is the actual native Frobenius twist

The outer residue uses the ordinary reduction of the LEFT coefficient copy.
It does not use the old Frobenius-balanced W action on the inner tensor.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist

private def tensorRingLift {R S A D : Type u} [CommRing R] [CommRing S]
    [CommRing A] [CommRing D] [Algebra R S] [Algebra R A]
    (f : S →+* D) (g : A →+* D)
    (h : ∀ r, f (algebraMap R S r) = g (algebraMap R A r)) :
    S ⊗[R] A →+* D :=
  ((CommRingCat.isPushout_tensorProduct R S A).desc
    (CommRingCat.ofHom f) (CommRingCat.ofHom g) (by ext r; exact h r)).hom

private theorem tensorRingLift_left {R S A D : Type u} [CommRing R] [CommRing S]
    [CommRing A] [CommRing D] [Algebra R S] [Algebra R A]
    (f : S →+* D) (g : A →+* D)
    (h : ∀ r, f (algebraMap R S r) = g (algebraMap R A r)) (s : S) :
    tensorRingLift f g h (s ⊗ₜ[R] (1 : A)) = f s := by
  exact congrArg (fun q : CommRingCat.of S ⟶ CommRingCat.of D => q.hom s)
    ((CommRingCat.isPushout_tensorProduct R S A).inl_desc
      (CommRingCat.ofHom f) (CommRingCat.ofHom g) (by ext r; exact h r))

private theorem tensorRingLift_right {R S A D : Type u} [CommRing R] [CommRing S]
    [CommRing A] [CommRing D] [Algebra R S] [Algebra R A]
    (f : S →+* D) (g : A →+* D)
    (h : ∀ r, f (algebraMap R S r) = g (algebraMap R A r)) (a : A) :
    tensorRingLift f g h ((1 : S) ⊗ₜ[R] a) = g a := by
  exact congrArg (fun q : CommRingCat.of A ⟶ CommRingCat.of D => q.hom a)
    ((CommRingCat.isPushout_tensorProduct R S A).inr_desc
      (CommRingCat.ofHom f) (CommRingCat.ofHom g) (by ext r; exact h r))

private theorem tensorRingLift_tmul {R S A D : Type u} [CommRing R] [CommRing S]
    [CommRing A] [CommRing D] [Algebra R S] [Algebra R A]
    (f : S →+* D) (g : A →+* D)
    (h : ∀ r, f (algebraMap R S r) = g (algebraMap R A r)) (s : S) (a : A) :
    tensorRingLift f g h (s ⊗ₜ[R] a) = f s * g a := by
  have ht : s ⊗ₜ[R] a = (s ⊗ₜ[R] (1 : A)) * ((1 : S) ⊗ₜ[R] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, map_mul, tensorRingLift_left, tensorRingLift_right]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule

abbrev CoefficientCopy := ULift.{0} (WittTwo.Ring p k)

/-- Ordinary reduction of the genuine LEFT coefficient copy, with no Witt Frobenius composed. -/
def copyReduction : CoefficientCopy p k →+* k :=
  (WittTwo.reduction p k).comp ULift.ringEquiv.toRingHom

@[instance_reducible] def copyReductionAlgebra : Algebra (CoefficientCopy p k) k :=
  (copyReduction p k).toAlgebra

/-- Pin the scalar module to ordinary copied reduction, rather than generic ULift inference. -/
@[instance_reducible] def copyReductionModule : Module (CoefficientCopy p k) k :=
  (copyReductionAlgebra p k).toModule

attribute [local instance] copyReductionAlgebra copyReductionModule

variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]

abbrev LiftSource := WittTwoRelativeLift.TwistAlgebra p k A
abbrev ResidueAlgebra := WittTwoSmoothDifferentials.ResidueAlgebra p k A

/-- The genuine left-copy action, explicitly distinguished from the old W action. -/
@[instance_reducible] def sourceLeftAlgebra :
    Algebra (CoefficientCopy p k) (LiftSource p k A) :=
  Algebra.TensorProduct.leftAlgebra

/-- The outer tensor MUST use this genuine left action, not ULift of the old W action. -/
@[instance_reducible] def sourceLeftModule :
    Module (CoefficientCopy p k) (LiftSource p k A) :=
  (sourceLeftAlgebra p k A).toModule

attribute [local instance] sourceLeftAlgebra sourceLeftModule

/-- This residue is over W' with its ordinary reduction and the genuine LEFT W' action. -/
abbrev SourceResidue := k ⊗[CoefficientCopy p k] LiftSource p k A

abbrev NativeTwist := Cartier.RelativeFrobenius.twist
  (algebraMap k (ResidueAlgebra p k A)) p

def nativeCoefficient : k →+* NativeTwist p k A :=
  (Cartier.RelativeFrobenius.coefficientMap (algebraMap k (ResidueAlgebra p k A)) p).hom

def nativeSource : ResidueAlgebra p k A →+* NativeTwist p k A :=
  (Cartier.RelativeFrobenius.sourceMap (algebraMap k (ResidueAlgebra p k A)) p).hom

@[instance_reducible] def nativeCoefficientAlgebra : Algebra k (NativeTwist p k A) :=
  (nativeCoefficient p k A).toAlgebra

attribute [local instance] nativeCoefficientAlgebra

def originalReduction : A →+* ResidueAlgebra p k A :=
  Algebra.TensorProduct.includeRight.toRingHom

private theorem native_balance (d : k) :
    nativeCoefficient p k A (d ^ p) =
      nativeSource p k A (algebraMap k (ResidueAlgebra p k A) d) := by
  exact congrArg (fun q : CommRingCat.of k ⟶ NativeTwist p k A => q.hom d)
    (pushout.condition (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A))))

omit [CharP k p] in
private theorem originalReduction_base (w : WittTwo.Ring p k) :
    originalReduction p k A (algebraMap (WittTwo.Ring p k) A w) =
      algebraMap k (ResidueAlgebra p k A) (WittTwo.reduction p k w) :=
  (Algebra.TensorProduct.tmul_one_eq_one_tmul w).symm

private theorem inner_balance (w : WittTwo.Ring p k) :
    (nativeCoefficient p k A).comp (copyReduction p k)
        (algebraMap (WittTwo.Ring p k) (CoefficientCopy p k) w) =
      (nativeSource p k A).comp (originalReduction p k A)
        (algebraMap (WittTwo.Ring p k) A w) := by
  change nativeCoefficient p k A
      (WittTwo.reduction p k (WittTwoFrobenius.frobenius p k w)) = _
  rw [WittTwoFrobenius.reduction_frobenius, native_balance, RingHom.comp_apply,
    originalReduction_base]

private def sourceToNative : LiftSource p k A →+* NativeTwist p k A :=
  tensorRingLift ((nativeCoefficient p k A).comp (copyReduction p k))
    ((nativeSource p k A).comp (originalReduction p k A)) (inner_balance p k A)

private theorem sourceToNative_tmul (w : CoefficientCopy p k) (a : A) :
    sourceToNative p k A (w ⊗ₜ[WittTwo.Ring p k] a) =
      nativeCoefficient p k A (copyReduction p k w) *
        nativeSource p k A (originalReduction p k A a) :=
  tensorRingLift_tmul _ _ _ w a

private theorem outer_balance (w : CoefficientCopy p k) :
    nativeCoefficient p k A (algebraMap (CoefficientCopy p k) k w) =
      sourceToNative p k A (algebraMap (CoefficientCopy p k) (LiftSource p k A) w) := by
  change nativeCoefficient p k A (copyReduction p k w) =
    sourceToNative p k A (w ⊗ₜ[WittTwo.Ring p k] (1 : A))
  rw [sourceToNative_tmul, map_one, map_one, mul_one]

private def forward : SourceResidue p k A →+* NativeTwist p k A :=
  tensorRingLift (R := CoefficientCopy p k) (S := k) (A := LiftSource p k A)
    (nativeCoefficient p k A) (sourceToNative p k A) (outer_balance p k A)

private theorem forward_tmul (d : k) (w : CoefficientCopy p k) (a : A) :
    forward p k A (d ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] a)) =
      nativeCoefficient p k A (d * copyReduction p k w) *
        nativeSource p k A (originalReduction p k A a) := by
  rw [forward, tensorRingLift_tmul, sourceToNative_tmul, map_mul, mul_assoc]

private def residueCoefficient : k →+* SourceResidue p k A :=
  Algebra.TensorProduct.includeLeftRingHom
    (R := CoefficientCopy p k) (A := k) (B := LiftSource p k A)

private def sourceIntoResidue : A →+* SourceResidue p k A :=
  (Algebra.TensorProduct.includeRight : LiftSource p k A →ₐ[CoefficientCopy p k]
    SourceResidue p k A).toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[WittTwo.Ring p k] LiftSource p k A).toRingHom

private theorem sourceIntoResidue_base (w : WittTwo.Ring p k) :
    sourceIntoResidue p k A (algebraMap (WittTwo.Ring p k) A w) =
      residueCoefficient p k A ((WittTwo.reduction p k w) ^ p) := by
  change (1 : k) ⊗ₜ[CoefficientCopy p k]
      ((1 : CoefficientCopy p k) ⊗ₜ[WittTwo.Ring p k] (algebraMap (WittTwo.Ring p k) A w)) = _
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul w]
  have ht := Algebra.TensorProduct.tmul_one_eq_one_tmul
    (R := CoefficientCopy p k) (A := k) (B := LiftSource p k A)
    (algebraMap (WittTwo.Ring p k) (CoefficientCopy p k) w)
  change (WittTwo.reduction p k (WittTwoFrobenius.frobenius p k w)) ⊗ₜ
      (1 : LiftSource p k A) =
    (1 : k) ⊗ₜ[CoefficientCopy p k]
      ((algebraMap (WittTwo.Ring p k) (CoefficientCopy p k) w) ⊗ₜ[WittTwo.Ring p k] (1 : A)) at ht
  rw [WittTwoFrobenius.reduction_frobenius] at ht
  exact ht.symm

private theorem inverseSource_balance (w : WittTwo.Ring p k) :
    ((residueCoefficient p k A).comp (frobenius k p))
        (algebraMap (WittTwo.Ring p k) k w) =
      sourceIntoResidue p k A (algebraMap (WittTwo.Ring p k) A w) := by
  change residueCoefficient p k A ((WittTwo.reduction p k w) ^ p) = _
  exact (sourceIntoResidue_base p k A w).symm

private def inverseSource : ResidueAlgebra p k A →+* SourceResidue p k A :=
  tensorRingLift (R := WittTwo.Ring p k) (S := k) (A := A) (D := SourceResidue p k A)
    ((residueCoefficient p k A).comp (frobenius k p))
    (sourceIntoResidue p k A) (inverseSource_balance p k A)

private theorem inverseSource_tmul (d : k) (a : A) :
    inverseSource p k A (d ⊗ₜ[WittTwo.Ring p k] a) =
      (d ^ p) ⊗ₜ[CoefficientCopy p k] ((1 : CoefficientCopy p k) ⊗ₜ[WittTwo.Ring p k] a) := by
  rw [inverseSource, tensorRingLift_tmul]
  change ((d ^ p) ⊗ₜ[CoefficientCopy p k] (1 : LiftSource p k A)) *
      ((1 : k) ⊗ₜ[CoefficientCopy p k] ((1 : CoefficientCopy p k) ⊗ₜ[WittTwo.Ring p k] a)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem inverse_balance :
    CommRingCat.ofHom (frobenius k p) ≫ CommRingCat.ofHom (R := k) (S := SourceResidue p k A) (residueCoefficient p k A) =
      CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)) ≫
        CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := SourceResidue p k A) (inverseSource p k A) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro d
  change residueCoefficient p k A (d ^ p) =
    inverseSource p k A (d ⊗ₜ[WittTwo.Ring p k] (1 : A))
  rw [inverseSource_tmul]
  rfl

private def inverse : NativeTwist p k A →+* SourceResidue p k A :=
  (pushout.desc (f := CommRingCat.ofHom (frobenius k p))
    (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
    (CommRingCat.ofHom (R := k) (S := SourceResidue p k A) (residueCoefficient p k A))
    (CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := SourceResidue p k A) (inverseSource p k A)) (inverse_balance p k A)).hom

private theorem inverse_coefficient (d : k) :
    inverse p k A (nativeCoefficient p k A d) = residueCoefficient p k A d := by
  exact congrArg (fun q : CommRingCat.of k ⟶ CommRingCat.of (SourceResidue p k A) => q.hom d)
    (pushout.inl_desc (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
      (CommRingCat.ofHom (R := k) (S := SourceResidue p k A) (residueCoefficient p k A))
      (CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := SourceResidue p k A) (inverseSource p k A)) (inverse_balance p k A))

private theorem inverse_source (b : ResidueAlgebra p k A) :
    inverse p k A (nativeSource p k A b) = inverseSource p k A b := by
  exact congrArg (fun q : CommRingCat.of (ResidueAlgebra p k A) ⟶
    CommRingCat.of (SourceResidue p k A) => q.hom b)
    (pushout.inr_desc (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
      (CommRingCat.ofHom (R := k) (S := SourceResidue p k A) (residueCoefficient p k A))
      (CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := SourceResidue p k A) (inverseSource p k A)) (inverse_balance p k A))

private theorem inverse_forward_double (d : k) (w : CoefficientCopy p k) (a : A) :
    inverse p k A (forward p k A (d ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] a))) =
      d ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] a) := by
  rw [forward_tmul, map_mul, inverse_coefficient, inverse_source]
  change (residueCoefficient p k A (d * copyReduction p k w)) *
      inverseSource p k A ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) = _
  rw [inverseSource_tmul, one_pow]
  change ((d * copyReduction p k w) ⊗ₜ[CoefficientCopy p k] (1 : LiftSource p k A)) *
      ((1 : k) ⊗ₜ[CoefficientCopy p k] ((1 : CoefficientCopy p k) ⊗ₜ[WittTwo.Ring p k] a)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have ht := Algebra.TensorProduct.tmul_one_eq_one_tmul
    (R := CoefficientCopy p k) (A := k) (B := LiftSource p k A) w
  change (copyReduction p k w) ⊗ₜ[CoefficientCopy p k] (1 : LiftSource p k A) =
    (1 : k) ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] (1 : A)) at ht
  have hm := congrArg (fun z : SourceResidue p k A =>
    (d ⊗ₜ[CoefficientCopy p k] (1 : LiftSource p k A)) * z *
      ((1 : k) ⊗ₜ[CoefficientCopy p k] ((1 : CoefficientCopy p k) ⊗ₜ[WittTwo.Ring p k] a))) ht
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hm

private theorem inverse_forward (z : SourceResidue p k A) :
    inverse p k A (forward p k A z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul d r =>
    induction r using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | tmul w a => exact inverse_forward_double p k A d w a

private theorem forward_inverseSource (b : ResidueAlgebra p k A) :
    forward p k A (inverseSource p k A b) = nativeSource p k A b := by
  induction b using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul d a =>
    rw [inverseSource_tmul, forward_tmul, map_one, mul_one, native_balance]
    change nativeSource p k A (d ⊗ₜ[WittTwo.Ring p k] (1 : A)) *
        nativeSource p k A ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) = _
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem forward_inverse (x : NativeTwist p k A) :
    forward p k A (inverse p k A x) = x := by
  have h : CommRingCat.ofHom ((forward p k A).comp (inverse p k A)) =
      𝟙 (NativeTwist p k A) := by
    apply pushout.hom_ext
      (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      change forward p k A (inverse p k A (nativeCoefficient p k A d)) = nativeCoefficient p k A d
      rw [inverse_coefficient]
      exact tensorRingLift_left (R := CoefficientCopy p k) (S := k)
        (A := LiftSource p k A) (nativeCoefficient p k A) (sourceToNative p k A)
        (outer_balance p k A) d
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change forward p k A (inverse p k A (nativeSource p k A b)) = nativeSource p k A b
      rw [inverse_source, forward_inverseSource]
  exact congrArg (fun q : NativeTwist p k A ⟶ NativeTwist p k A => q.hom x) h

/-- The genuine LEFT-copy residue is the actual native relative-Frobenius pushout. -/
def nativeResidueEquiv : SourceResidue p k A ≃ₐ[k] NativeTwist p k A where
  toFun := forward p k A
  invFun := inverse p k A
  left_inv := inverse_forward p k A
  right_inv := forward_inverse p k A
  map_mul' := (forward p k A).map_mul
  map_add' := (forward p k A).map_add
  commutes' d := tensorRingLift_left (R := CoefficientCopy p k) (S := k)
    (A := LiftSource p k A) (nativeCoefficient p k A) (sourceToNative p k A)
    (outer_balance p k A) d

/-- Every original double pure tensor retains its actual coefficient and source maps. -/
theorem nativeResidueEquiv_tmul (d : k) (w : CoefficientCopy p k) (a : A) :
    nativeResidueEquiv p k A (d ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] a)) =
      nativeCoefficient p k A (d * copyReduction p k w) *
        nativeSource p k A (originalReduction p k A a) :=
  forward_tmul p k A d w a

/-- The inverse preserves EVERY actual coefficient of the native pushout. -/
theorem nativeResidueEquiv_symm_coefficient (d : k) :
    (nativeResidueEquiv p k A).symm (nativeCoefficient p k A d) =
      d ⊗ₜ[CoefficientCopy p k] (1 : LiftSource p k A) :=
  inverse_coefficient p k A d

/-- The inverse source formula has the genuine pth coefficient, without coefficient roots. -/
theorem nativeResidueEquiv_symm_source_tmul (d : k) (a : A) :
    (nativeResidueEquiv p k A).symm (nativeSource p k A (d ⊗ₜ[WittTwo.Ring p k] a)) =
      (d ^ p) ⊗ₜ[CoefficientCopy p k] ((1 : CoefficientCopy p k) ⊗ₜ[WittTwo.Ring p k] a) :=
  (inverse_source p k A _).trans (inverseSource_tmul p k A d a)

end EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist
