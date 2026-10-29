import EnvelopeProperty.DeligneIllusie.WittTwoSourceResidue

/-!
# Witt Two Residue Untwist

Actual original tensor untwisting and genuine residue relative Frobenius values. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoResidueUntwist
universe u
private def nativeTensorUntwist {R S D : Type u} [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D] (e : R ≃ₐ[R] S) : S ⊗[R] D ≃ₐ[R] D :=
  (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl : D ≃ₐ[R] D)).trans
    (Algebra.TensorProduct.lid R D)

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
private abbrev W := WittTwo.Ring p k
private abbrev W' := ULift.{0} (W p k)

/-- The SAME actual Witt coefficient equivalence as its genuine original base algebra equivalence. -/
def baseAlgEquiv : W p k ≃ₐ[W p k] W' p k :=
  { WittTwoSourceResidue.twistBaseEquiv p k with commutes' := fun _ => rfl }

variable (A : Type u) [CommRing A] [Algebra (W p k) A]
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev C := k ⊗[W p k] T p k A

/-- Genuine original algebra untwisting of the ACTUAL original Witt-twisted tensor. -/
def sourceUntwist : T p k A ≃ₐ[W p k] A :=
  nativeTensorUntwist (baseAlgEquiv p k)

/-- EVERY original pure tensor has its actual inverse-Witt-coefficient value. -/
theorem sourceUntwist_tmul (w : W' p k) (a : A) :
    sourceUntwist p k A (w ⊗ₜ[W p k] a) =
      algebraMap (W p k) A ((WittTwoFrobenius.frobeniusEquiv p k).symm w.down) * a := by
  change Algebra.TensorProduct.lid (W p k) A (((baseAlgEquiv p k).symm w) ⊗ₜ[W p k] a) = _
  rw [Algebra.TensorProduct.lid_tmul, Algebra.smul_def]
  rfl

/-- In particular coefficient-one original coordinates retain EXACTLY their original value. -/
theorem sourceUntwist_one_tmul (a : A) :
    sourceUntwist p k A ((1 : W' p k) ⊗ₜ[W p k] a) = a := by
  rw [sourceUntwist_tmul]
  simp only [show (1 : W' p k).down = (1 : W p k) from rfl, map_one, one_mul]

/-- The SAME actual residue presentation is genuinely the SAME original residue algebra over k. -/
def residueUntwist : C p k A ≃ₐ[k] B p k A :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) (sourceUntwist p k A)

/-- EVERY original pure residue tensor has its actual entire source-untwist value. -/
theorem residueUntwist_tmul (c : k) (t : T p k A) :
    residueUntwist p k A (c ⊗ₜ[W p k] t) = c ⊗ₜ[W p k] sourceUntwist p k A t := rfl

/-- Original coefficient-one coordinate residues are genuinely retained by the SAME actual residue equivalence. -/
theorem residueUntwist_one_coordinate (a : A) :
    residueUntwist p k A ((1 : k) ⊗ₜ[W p k] ((1 : W' p k) ⊗ₜ[W p k] a)) =
      (1 : k) ⊗ₜ[W p k] a := by
  rw [residueUntwist_tmul, sourceUntwist_one_tmul]

private theorem inverse_coefficient_frobenius (w : W' p k) :
    (WittTwo.reduction p k ((WittTwoFrobenius.frobeniusEquiv p k).symm w.down)) ^ p =
      WittTwo.reduction p k w.down := by
  have h := WittTwoFrobenius.reduction_frobenius p k
    ((WittTwoFrobenius.frobeniusEquiv p k).symm w.down)
  change WittTwo.reduction p k ((WittTwoFrobenius.frobeniusEquiv p k)
    ((WittTwoFrobenius.frobeniusEquiv p k).symm w.down)) = _ at h
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- The SAME ACTUAL residue relative Frobenius is exactly pth power of the SAME actual untwisted residue. -/
theorem residueFrobenius_untwist (t : T p k A) :
    WittTwoRelativeLift.residueFrobenius p k A t =
      ((1 : k) ⊗ₜ[W p k] sourceUntwist p k A t) ^ p := by
  let r : T p k A →+* B p k A := (WittTwoRelativeLift.residueFrobenius p k A).toRingHom
  let q : T p k A →+* B p k A := (Cartier.AlgebraFrobenius.map k (B p k A) p).comp
    ((algebraMap A (B p k A)).comp (sourceUntwist p k A).toRingHom)
  have he : r t = q t := by
    induction t using TensorProduct.induction_on with
    | zero => rw [r.map_zero, q.map_zero]
    | add z w hz hw => rw [r.map_add, q.map_add, hz, hw]
    | tmul w a =>
      dsimp only [q, RingHom.comp_apply]
      rw [Cartier.AlgebraFrobenius.map_apply]
      change WittTwoRelativeLift.residueFrobenius p k A (w ⊗ₜ[W p k] a) =
        (algebraMap A (B p k A) (sourceUntwist p k A (w ⊗ₜ[W p k] a))) ^ p
      rw [WittTwoRelativeLift.residueFrobenius_tmul, sourceUntwist_tmul, map_mul]
      have hc : algebraMap A (B p k A)
          (algebraMap (W p k) A ((WittTwoFrobenius.frobeniusEquiv p k).symm w.down)) =
          (WittTwo.reduction p k ((WittTwoFrobenius.frobeniusEquiv p k).symm w.down)) ⊗ₜ[W p k] (1 : A) :=
        (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
      rw [hc, mul_pow]
      simp only [Algebra.TensorProduct.tmul_pow, one_pow, inverse_coefficient_frobenius]
      rw [← map_pow]
      rfl
  have hq : q t = (algebraMap A (B p k A) (sourceUntwist p k A t)) ^ p := by
    dsimp only [q, RingHom.comp_apply]
    rw [Cartier.AlgebraFrobenius.map_apply]
    rfl
  exact he.trans hq

end EnvelopeProperty.DeligneIllusie.WittTwoResidueUntwist
