import EnvelopeProperty.DeligneIllusie.WittTwoFrobenius
import EnvelopeProperty.DeligneIllusie.WittTwoSmoothDifferentials
import EnvelopeProperty.Cartier.AlgebraFrobenius

/-!
# Witt Two Relative Lift

Actual coefficient-twisted affine relative Frobenius lifts over W2. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoRelativeLift

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra

/-- The original Witt Frobenius acts into a distinct canonical copy of the coefficient ring. -/
@[instance_reducible] def twistBaseAlgebra : Algebra (WittTwo.Ring p k) (ULift.{0} (WittTwo.Ring p k)) :=
  (ULift.ringEquiv.symm.toRingHom.comp (WittTwoFrobenius.frobenius p k)).toAlgebra

@[instance_reducible] def twistBaseModule :
    Module (WittTwo.Ring p k) (ULift.{0} (WittTwo.Ring p k)) :=
  (twistBaseAlgebra p k).toModule

attribute [local instance] twistBaseAlgebra twistBaseModule

variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]

abbrev TwistAlgebra := ULift.{0} (WittTwo.Ring p k) ⊗[WittTwo.Ring p k] A

private abbrev Residue := WittTwoSmoothDifferentials.ResidueAlgebra p k A

@[instance_reducible] def copyAlgebra : Algebra (ULift.{0} (WittTwo.Ring p k)) A :=
  ((algebraMap (WittTwo.Ring p k) A).comp ULift.ringEquiv.toRingHom).toAlgebra

@[instance_reducible] def residueCopyAlgebra : Algebra (ULift.{0} (WittTwo.Ring p k)) (Residue p k A) :=
  ((algebraMap (WittTwo.Ring p k) (Residue p k A)).comp ULift.ringEquiv.toRingHom).toAlgebra

attribute [local instance] residueCopyAlgebra

/-- Original residue reduction, with the canonical copied coefficient structure retained. -/
def reductionMap :
    letI := copyAlgebra p k A
    A →ₐ[ULift.{0} (WittTwo.Ring p k)] Residue p k A := by
  letI := copyAlgebra p k A
  refine { (Algebra.TensorProduct.includeRight : A →ₐ[WittTwo.Ring p k] Residue p k A).toRingHom with
    commutes' := ?_ }
  intro w
  change (1 : k) ⊗ₜ[WittTwo.Ring p k] (algebraMap (WittTwo.Ring p k) A w.down) =
    (WittTwo.reduction p k w.down) ⊗ₜ (1 : A)
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul w.down).symm

omit [CharP k p] [PerfectRing k p] in
/-- The SAME actual original algebra reduction is onto. -/
theorem reduction_surjective : Function.Surjective (reductionMap p k A) :=
  WittTwoResidue.tensorReduction_surjective p k A

private def tensorLift {R S C D : Type u} [CommRing R] [CommRing S]
    [CommRing C] [CommRing D] [Algebra R S] [Algebra R C] [Algebra S D]
    (g : C →+* D)
    (hg : ∀ r, g (algebraMap R C r) = algebraMap S D (algebraMap R S r)) :
    S ⊗[R] C →ₐ[S] D := by
  letI : Algebra R D := ((algebraMap S D).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S D := IsScalarTower.of_algebraMap_eq' rfl
  let g' : C →ₐ[R] D := { g with commutes' := hg }
  exact Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S D) g'

private theorem tensorLift_tmul {R S C D : Type u} [CommRing R] [CommRing S]
    [CommRing C] [CommRing D] [Algebra R S] [Algebra R C] [Algebra S D]
    (g : C →+* D)
    (hg : ∀ r, g (algebraMap R C r) = algebraMap S D (algebraMap R S r)) (s : S) (c : C) :
    tensorLift g hg (s ⊗ₜ[R] c) = algebraMap S D s * g c := rfl

omit [PerfectRing k p] in
private theorem residue_balance (w : WittTwo.Ring p k) :
    ((Cartier.AlgebraFrobenius.map k (Residue p k A) p).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[WittTwo.Ring p k] Residue p k A).toRingHom) (algebraMap (WittTwo.Ring p k) A w) =
        algebraMap (ULift.{0} (WittTwo.Ring p k)) (Residue p k A)
          (algebraMap (WittTwo.Ring p k) (ULift.{0} (WittTwo.Ring p k)) w) := by
  rw [RingHom.comp_apply, Cartier.AlgebraFrobenius.map_apply]
  change ((1 : k) ⊗ₜ[WittTwo.Ring p k] (algebraMap (WittTwo.Ring p k) A w)) ^ p =
    (WittTwo.reduction p k (WittTwoFrobenius.frobenius p k w)) ⊗ₜ (1 : A)
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul w,
    WittTwoFrobenius.reduction_frobenius, Algebra.TensorProduct.tmul_pow, one_pow]
  rfl

/-- The actual residue relative Frobenius on the actual coefficient-twisted algebra. -/
def residueFrobenius : TwistAlgebra p k A →ₐ[ULift.{0} (WittTwo.Ring p k)] Residue p k A :=
  tensorLift ((Cartier.AlgebraFrobenius.map k (Residue p k A) p).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[WittTwo.Ring p k] Residue p k A).toRingHom) (residue_balance p k A)

omit [PerfectRing k p] in
/-- Every original pure tensor retains the actual coefficient and original relative pth power. -/
theorem residueFrobenius_tmul (w : ULift.{0} (WittTwo.Ring p k)) (a : A) :
    residueFrobenius p k A (w ⊗ₜ[WittTwo.Ring p k] a) =
      ((WittTwo.reduction p k w.down) ⊗ₜ[WittTwo.Ring p k] (1 : A)) *
        (((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ p) := by
  rw [residueFrobenius, tensorLift_tmul, RingHom.comp_apply,
    Cartier.AlgebraFrobenius.map_apply]
  rfl

variable [Algebra.Smooth (WittTwo.Ring p k) A]

/-- Smoothness and the actual prime exactness prove square-zero of the ENTIRE actual kernel. -/
theorem reduction_kernel_square_zero :
    (letI := copyAlgebra p k A; RingHom.ker (reductionMap p k A).toRingHom ^ 2 = ⊥) := by
  let := copyAlgebra p k A
  apply le_antisymm _ bot_le
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  have hx0 : WittTwoResidue.tensorReduction p k A x = 0 := hx
  have hy0 : WittTwoResidue.tensorReduction p k A y = 0 := hy
  obtain ⟨a, ha⟩ := (WittTwoResidue.tensorReduction_exact p k A x).mp hx0
  obtain ⟨b, hb⟩ := (WittTwoResidue.tensorReduction_exact p k A y).mp hy0
  change x * y = 0
  change (p : WittTwo.Ring p k) • a = x at ha
  change (p : WittTwo.Ring p k) • b = y at hb
  rw [← ha, ← hb, Algebra.smul_def, Algebra.smul_def]
  calc
    (algebraMap (WittTwo.Ring p k) A p * a) * (algebraMap (WittTwo.Ring p k) A p * b) =
        algebraMap (WittTwo.Ring p k) A ((p : WittTwo.Ring p k) ^ 2) * (a*b) := by
          rw [map_pow, pow_two]
          ring
    _ = 0 := by rw [WittTwo.prime_square_zero, map_zero, zero_mul]

/-- An ACTUAL relative Frobenius lift, produced by actual smooth infinitesimal lifting. -/
def relativeLift :
    letI := copyAlgebra p k A
    TwistAlgebra p k A →ₐ[ULift.{0} (WittTwo.Ring p k)] A := by
  letI := copyAlgebra p k A
  exact Algebra.FormallySmooth.liftOfSurjective (residueFrobenius p k A)
    (reductionMap p k A) (reduction_surjective p k A)
    ⟨2, reduction_kernel_square_zero p k A⟩

/-- The ENTIRE original lift reduces to the actual relative Frobenius, internally derived. -/
theorem relativeLift_reduction :
    letI := copyAlgebra p k A
    (reductionMap p k A).comp (relativeLift p k A) = residueFrobenius p k A := by
  let := copyAlgebra p k A
  exact Algebra.FormallySmooth.comp_liftOfSurjective (residueFrobenius p k A)
    (reductionMap p k A) (reduction_surjective p k A)
    ⟨2, reduction_kernel_square_zero p k A⟩

/-- Every original coefficient-one coordinate has its actual relative Frobenius residue. -/
theorem relativeLift_one_reduction (a : A) :
    letI := copyAlgebra p k A
    reductionMap p k A (relativeLift p k A ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ a)) =
      ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ p := by
  let := copyAlgebra p k A
  have h := AlgHom.congr_fun (relativeLift_reduction p k A)
    ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a)
  exact h.trans (by
    rw [residueFrobenius_tmul]
    change ((WittTwo.reduction p k (1 : WittTwo.Ring p k)) ⊗ₜ (1 : A)) * _ = _
    rw [map_one]
    exact one_mul _)

/-- Actual correction terms are produced for every original coordinate of the constructed lift. -/
theorem relativeLift_coordinate_correction (a : A) :
    letI := copyAlgebra p k A
    ∃ b : A, relativeLift p k A ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ a) =
      a ^ p + (p : A) * b := by
  let := copyAlgebra p k A
  let z := relativeLift p k A ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ a) - a ^ p
  have hz : WittTwoResidue.tensorReduction p k A z = 0 := by
    change reductionMap p k A z = 0
    rw [map_sub, map_pow, relativeLift_one_reduction]
    change (((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ p) - (((1 : k) ⊗ₜ[WittTwo.Ring p k] a) ^ p) = 0
    exact sub_self _
  obtain ⟨b, hb⟩ := (WittTwoResidue.tensorReduction_exact p k A z).mp hz
  refine ⟨b, ?_⟩
  change (p : WittTwo.Ring p k) • b = z at hb
  rw [Algebra.smul_def, map_natCast] at hb
  exact (sub_eq_iff_eq_add.mp hb.symm).trans (add_comm _ _)

end EnvelopeProperty.DeligneIllusie.WittTwoRelativeLift
