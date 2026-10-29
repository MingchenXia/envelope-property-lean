import EnvelopeProperty.DeligneIllusie.WittTwoDividedLift

/-!
# Witt Two Source Residue

The original twisted source prime quotient as its genuine native residue Kähler module. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoSourceResidue

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule

private abbrev W := WittTwo.Ring p k
private abbrev W' := ULift.{0} (W p k)

local instance twistSMul : SMul (W p k) (W' p k) :=
  (WittTwoRelativeLift.twistBaseAlgebra p k).toSMul

/-- The actual original twisted structural coefficient map is an actual ring equivalence. -/
def twistBaseEquiv : W p k ≃+* W' p k :=
  (WittTwoFrobenius.frobeniusEquiv p k).trans ULift.ringEquiv.symm

private theorem twistBaseEquiv_algebraMap (w : W p k) :
    twistBaseEquiv p k w = algebraMap (W p k) (W' p k) w := rfl

variable (A : Type u) [CommRing A] [Algebra (W p k) A] [Algebra.Smooth (W p k) A]
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A

local instance sourceBaseSMul : SMul (W' p k) (T p k A) :=
  (Algebra.TensorProduct.leftAlgebra : Algebra (W' p k) (T p k A)).toSMul
local instance sourceBaseModule : Module (W' p k) (T p k A) :=
  (Algebra.TensorProduct.leftAlgebra : Algebra (W' p k) (T p k A)).toModule
local instance sourceOriginalSMul : SMul (W p k) (T p k A) :=
  (inferInstance : Algebra (W p k) (T p k A)).toSMul
local instance sourceOriginalModule : Module (W p k) (T p k A) :=
  (inferInstance : Algebra (W p k) (T p k A)).toModule
local instance sourceBaseTower : IsScalarTower (W p k) (W' p k) (T p k A) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The SAME actual twisted tensor algebra is smooth over the original Witt base. -/
theorem source_smooth : Algebra.Smooth (W p k) (T p k A) := by
  let : Algebra.Smooth (W p k) (W' p k) := Algebra.Smooth.of_equiv
    (AlgEquiv.ofBijective (Algebra.ofId (W p k) (W' p k))
      (show Function.Bijective (algebraMap (W p k) (W' p k)) from
        (twistBaseEquiv p k).bijective))
  exact Algebra.Smooth.comp (W p k) (W' p k) (T p k A)

attribute [local instance] source_smooth WittTwoSmoothDifferentials.differentials_flat

omit [Algebra.Smooth (W p k) A] in
private theorem source_base_compat (w : W' p k) :
    algebraMap (W p k) (T p k A) ((twistBaseEquiv p k).symm w) =
      algebraMap (W' p k) (T p k A) w := by
  rw [IsScalarTower.algebraMap_apply (W p k) (W' p k) (T p k A)]
  rw [← twistBaseEquiv_algebraMap, RingEquiv.apply_symm_apply]

/-- Original coefficient-base equivalence on the SAME actual source Kähler module. -/
def sourceBaseEquiv : KaehlerDifferential (W' p k) (T p k A) ≃ₗ[T p k A]
    KaehlerDifferential (W p k) (T p k A) :=
  KaehlerBaseRingEquivalence.equiv (twistBaseEquiv p k).symm (source_base_compat p k A)

omit [Algebra.Smooth (W p k) A] in
/-- Every original universal differential is retained by the SAME source base equivalence. -/
theorem sourceBaseEquiv_D (t : T p k A) :
    sourceBaseEquiv p k A (KaehlerDifferential.D (W' p k) (T p k A) t) =
      KaehlerDifferential.D (W p k) (T p k A) t :=
  KaehlerBaseRingEquivalence.equiv_D (twistBaseEquiv p k).symm
    (source_base_compat p k A) t

/-- The actual residue algebra of the SAME actual twisted source with its original coefficient action. -/
abbrev SourceResidue := k ⊗[W p k] T p k A

/-- The actual original source Kähler reduction through equivalent coefficient bases. -/
def sourceReduction : KaehlerDifferential (W' p k) (T p k A) →ₗ[T p k A]
    KaehlerDifferential k (SourceResidue p k A) :=
  (KaehlerDifferential.map (W p k) k (T p k A) (SourceResidue p k A)).comp
    (sourceBaseEquiv p k A).toLinearMap

omit [Algebra.Smooth (W p k) A] in
/-- Actual source universal differentials retain their original residue differential. -/
theorem sourceReduction_D (t : T p k A) :
    sourceReduction p k A (KaehlerDifferential.D (W' p k) (T p k A) t) =
      KaehlerDifferential.D k (SourceResidue p k A) ((1 : k) ⊗ₜ[W p k] t) := by
  change KaehlerDifferential.map (W p k) k (T p k A) (SourceResidue p k A)
    (sourceBaseEquiv p k A (KaehlerDifferential.D (W' p k) (T p k A) t)) = _
  rw [sourceBaseEquiv_D, KaehlerDifferential.map_D]
  rfl

private theorem nativeReduction_kernel (C : Type u) [CommRing C] [Algebra (W p k) C]
    [Algebra.Smooth (W p k) C] (z : KaehlerDifferential (W p k) C) :
    KaehlerDifferential.map (W p k) k C (k ⊗[W p k] C) z = 0 ↔
      ∃ w : KaehlerDifferential (W p k) C, z = (p : C) • w := by
  change WittTwoSmoothDifferentials.reductionDifferential p k C z = 0 ↔ _
  rw [WittTwoSmoothDifferentials.reductionDifferential_eq_zero_iff]
  simp only [Nat.cast_smul_eq_nsmul]

omit [CharP k p] [PerfectRing k p] in
private theorem nativeReduction_surjective (C : Type u) [CommRing C] [Algebra (W p k) C] :
    Function.Surjective (KaehlerDifferential.map (W p k) k C (k ⊗[W p k] C)) := by
  intro y
  let e := KaehlerDifferential.tensorKaehlerEquivBase (W p k) k C (k ⊗[W p k] C)
  obtain ⟨x, hx⟩ := WittTwoResidue.tensorReduction_surjective p k
    (KaehlerDifferential (W p k) C) (e.symm y)
  refine ⟨x, ?_⟩
  have he : e ((1 : k) ⊗ₜ[W p k] x) =
      KaehlerDifferential.map (W p k) k C (k ⊗[W p k] C) x := by
    rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, one_smul]
  exact he.symm.trans ((congrArg e hx).trans (e.apply_symm_apply y))

/-- The SAME actual source reduction has precisely the original source prime image as kernel. -/
theorem sourceReduction_kernel :
    LinearMap.ker (sourceReduction p k A) = WittTwoDividedLift.sourcePrimeForms p k A := by
  ext w
  change sourceReduction p k A w = 0 ↔
    w ∈ WittTwoDividedLift.sourcePrimeForms p k A
  change KaehlerDifferential.map (W p k) k (T p k A) (SourceResidue p k A)
    (sourceBaseEquiv p k A w) = 0 ↔ _
  rw [nativeReduction_kernel]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(sourceBaseEquiv p k A).symm z, ?_⟩
    change (p : T p k A) • (sourceBaseEquiv p k A).symm z = w
    apply (sourceBaseEquiv p k A).injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact hz.symm
  · rintro ⟨z, hz⟩
    refine ⟨sourceBaseEquiv p k A z, ?_⟩
    change (p : T p k A) • z = w at hz
    rw [← hz, map_smul]

omit [Algebra.Smooth (W p k) A] in
/-- The actual native source Kähler reduction is onto its genuine native residue module. -/
theorem sourceReduction_surjective : Function.Surjective (sourceReduction p k A) := by
  intro y
  obtain ⟨x, hx⟩ := nativeReduction_surjective p k (T p k A) y
  refine ⟨(sourceBaseEquiv p k A).symm x, ?_⟩
  change KaehlerDifferential.map (W p k) k (T p k A) (SourceResidue p k A)
    (sourceBaseEquiv p k A ((sourceBaseEquiv p k A).symm x)) = y
  rw [LinearEquiv.apply_symm_apply]
  exact hx

/-- The SAME original source prime quotient is the genuine native residue Kähler module. -/
def sourceResidueEquiv :
    (KaehlerDifferential (W' p k) (T p k A) ⧸ WittTwoDividedLift.sourcePrimeForms p k A)
      ≃ₗ[T p k A] KaehlerDifferential k (SourceResidue p k A) :=
  (Submodule.quotEquivOfEq _ _ (sourceReduction_kernel p k A).symm).trans
    ((sourceReduction p k A).quotKerEquivOfSurjective (sourceReduction_surjective p k A))

/-- Every original source class has its SAME actual native reduction as value. -/
theorem sourceResidueEquiv_mk (w : KaehlerDifferential (W' p k) (T p k A)) :
    sourceResidueEquiv p k A ((WittTwoDividedLift.sourcePrimeForms p k A).mkQ w) =
      sourceReduction p k A w := by
  change (sourceReduction p k A).quotKerEquivOfSurjective
    (sourceReduction_surjective p k A) (Submodule.Quotient.mk w) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- Original universal differential classes map to the SAME genuine residue differentials. -/
theorem sourceResidueEquiv_D (t : T p k A) :
    sourceResidueEquiv p k A ((WittTwoDividedLift.sourcePrimeForms p k A).mkQ
      (KaehlerDifferential.D (W' p k) (T p k A) t)) =
      KaehlerDifferential.D k (SourceResidue p k A) ((1 : k) ⊗ₜ[W p k] t) := by
  rw [sourceResidueEquiv_mk, sourceReduction_D]

attribute [local instance] WittTwoDividedLift.residueLiftAlgebra

/-- The SAME whole divided lift is now defined on the actual native residue Kähler source. -/
def residueDividedLift : KaehlerDifferential k (SourceResidue p k A) →ₗ[T p k A]
    KaehlerDifferential k (WittTwoSmoothDifferentials.ResidueAlgebra p k A) :=
  (WittTwoDividedLift.reductionDividedLift p k A).comp (sourceResidueEquiv p k A).symm.toLinearMap

/-- On EVERY actual native reduction the new map retains the SAME whole original divided value. -/
theorem residueDividedLift_reduction (w : KaehlerDifferential (W' p k) (T p k A)) :
    residueDividedLift p k A (sourceReduction p k A w) =
      WittTwoDividedLift.dividedLiftDifferential p k A w := by
  rw [← sourceResidueEquiv_mk]
  change WittTwoDividedLift.reductionDividedLift p k A
    ((sourceResidueEquiv p k A).symm (sourceResidueEquiv p k A
      ((WittTwoDividedLift.sourcePrimeForms p k A).mkQ w))) = _
  rw [LinearEquiv.symm_apply_apply, WittTwoDividedLift.reductionDividedLift_mk]

end EnvelopeProperty.DeligneIllusie.WittTwoSourceResidue
