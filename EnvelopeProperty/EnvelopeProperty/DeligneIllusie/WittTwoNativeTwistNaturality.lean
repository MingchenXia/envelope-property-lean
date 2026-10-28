import EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistLift

/-! Canonical residue/native-twist maps respect actual W-algebra homomorphisms.

The chosen smooth infinitesimal lifts are not asserted to be natural.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  copyReductionAlgebra copyReductionModule sourceLeftAlgebra sourceLeftModule
  nativeCoefficientAlgebra

variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
  (f : A →ₐ[WittTwo.Ring p k] A')

/-- The original residue tensor map, preserving every genuine field coefficient. -/
def residueMap : ResidueAlgebra p k A →ₐ[k] ResidueAlgebra p k A' :=
  Algebra.TensorProduct.map (AlgHom.id k k) f

/-- The original model tensor map preserves the genuine LEFT W' action. -/
def liftSourceMap : LiftSource p k A →ₐ[CoefficientCopy p k] LiftSource p k A' :=
  Algebra.TensorProduct.map (AlgHom.id (CoefficientCopy p k) (CoefficientCopy p k)) f

/-- The ordinary residue extension of the actual left-copy model map. -/
def sourceResidueMap : SourceResidue p k A →ₐ[k] SourceResidue p k A' :=
  Algebra.TensorProduct.map (AlgHom.id k k) (liftSourceMap p k f)

omit [CharP k p] in
theorem residueMap_tmul (d : k) (a : A) :
    residueMap p k f (d ⊗ₜ[WittTwo.Ring p k] a) = d ⊗ₜ[WittTwo.Ring p k] f a := rfl

theorem liftSourceMap_tmul (w : CoefficientCopy p k) (a : A) :
    liftSourceMap p k f (w ⊗ₜ[WittTwo.Ring p k] a) = w ⊗ₜ[WittTwo.Ring p k] f a := rfl

theorem sourceResidueMap_tmul (d : k) (r : LiftSource p k A) :
    sourceResidueMap p k f (d ⊗ₜ[CoefficientCopy p k] r) =
      d ⊗ₜ[CoefficientCopy p k] liftSourceMap p k f r := rfl

omit [CharP k p] in
theorem residueMap_originalReduction (a : A) :
    residueMap p k f (originalReduction p k A a) = originalReduction p k A' (f a) := rfl

private theorem nativeMap_balance :
    CommRingCat.ofHom (frobenius k p) ≫
        CommRingCat.ofHom (R := k) (S := NativeTwist p k A') (nativeCoefficient p k A') =
      CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)) ≫
        CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := NativeTwist p k A')
          ((nativeSource p k A').comp (residueMap p k f).toRingHom) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro d
  change nativeCoefficient p k A' (d ^ p) =
    nativeSource p k A' (residueMap p k f (algebraMap k (ResidueAlgebra p k A) d))
  rw [(residueMap p k f).commutes]
  exact congrArg (fun q : CommRingCat.of k ⟶ NativeTwist p k A' => q.hom d)
    (pushout.condition (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A'))))

/-- The actual native pushout map, constructed from the residue tensor map. -/
def nativeMap : NativeTwist p k A →+* NativeTwist p k A' :=
  (pushout.desc (f := CommRingCat.ofHom (frobenius k p))
    (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
    (CommRingCat.ofHom (R := k) (S := NativeTwist p k A') (nativeCoefficient p k A'))
    (CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := NativeTwist p k A')
      ((nativeSource p k A').comp (residueMap p k f).toRingHom)) (nativeMap_balance p k f)).hom

theorem nativeMap_coefficient (d : k) :
    nativeMap p k f (nativeCoefficient p k A d) = nativeCoefficient p k A' d := by
  exact congrArg (fun q : CommRingCat.of k ⟶ NativeTwist p k A' => q.hom d)
    (pushout.inl_desc (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
      (CommRingCat.ofHom (R := k) (S := NativeTwist p k A') (nativeCoefficient p k A'))
      (CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := NativeTwist p k A')
        ((nativeSource p k A').comp (residueMap p k f).toRingHom)) (nativeMap_balance p k f))

theorem nativeMap_source (b : ResidueAlgebra p k A) :
    nativeMap p k f (nativeSource p k A b) =
      nativeSource p k A' (residueMap p k f b) := by
  exact congrArg (fun q : CommRingCat.of (ResidueAlgebra p k A) ⟶
    NativeTwist p k A' => q.hom b)
    (pushout.inr_desc (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
      (CommRingCat.ofHom (R := k) (S := NativeTwist p k A') (nativeCoefficient p k A'))
      (CommRingCat.ofHom (R := ResidueAlgebra p k A) (S := NativeTwist p k A')
        ((nativeSource p k A').comp (residueMap p k f).toRingHom)) (nativeMap_balance p k f))

/-- The whole canonical residue equivalence respects actual original model maps. -/
theorem nativeResidueEquiv_naturality :
    (nativeResidueEquiv p k A').toRingHom.comp (sourceResidueMap p k f).toRingHom =
      (nativeMap p k f).comp (nativeResidueEquiv p k A).toRingHom := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul d r =>
    induction r using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | tmul w a =>
      change nativeResidueEquiv p k A'
          (d ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] f a)) =
        nativeMap p k f (nativeResidueEquiv p k A
          (d ⊗ₜ[CoefficientCopy p k] (w ⊗ₜ[WittTwo.Ring p k] a)))
      rw [nativeResidueEquiv_tmul, nativeResidueEquiv_tmul, (nativeMap p k f).map_mul,
        nativeMap_coefficient, nativeMap_source, residueMap_originalReduction]

/-- Canonical actual source reductions respect model restriction as WHOLE ring maps. -/
theorem sourceReduction_naturality :
    (sourceReduction p k A').comp (liftSourceMap p k f).toRingHom =
      (nativeMap p k f).comp (sourceReduction p k A) := by
  apply RingHom.ext
  intro x
  have h := RingHom.congr_fun (nativeResidueEquiv_naturality p k f)
    ((1 : k) ⊗ₜ[CoefficientCopy p k] x)
  exact h

/-- The zero-safe geometric beta maps respect the same original model map. -/
theorem nativeBeta_naturality :
    (nativeBeta p k A').comp (nativeMap p k f) =
      (residueMap p k f).toRingHom.comp (nativeBeta p k A) := by
  have h : CommRingCat.ofHom (R := NativeTwist p k A) (S := ResidueAlgebra p k A')
        ((nativeBeta p k A').comp (nativeMap p k f)) =
      CommRingCat.ofHom (R := NativeTwist p k A) (S := ResidueAlgebra p k A')
        ((residueMap p k f).toRingHom.comp (nativeBeta p k A)) := by
    apply pushout.hom_ext
      (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k (ResidueAlgebra p k A)))
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      change nativeBeta p k A' (nativeMap p k f (nativeCoefficient p k A d)) =
        residueMap p k f (nativeBeta p k A (nativeCoefficient p k A d))
      rw [nativeMap_coefficient, nativeBeta_coefficient, nativeBeta_coefficient,
        (residueMap p k f).commutes]
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change nativeBeta p k A' (nativeMap p k f (nativeSource p k A b)) =
        residueMap p k f (nativeBeta p k A (nativeSource p k A b))
      rw [nativeMap_source, nativeBeta_source, nativeBeta_source, map_pow]
  exact congrArg CommRingCat.Hom.hom h

end EnvelopeProperty.DeligneIllusie.WittTwoNativeTwist
