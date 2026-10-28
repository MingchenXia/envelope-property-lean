import EnvelopeProperty.DeligneIllusie.WittTwoSourceResidue
import EnvelopeProperty.Cartier.EtaleDifferentialLeibniz

/-! Actual closedness of the same entire divided lift differential on native residue charts. -/

noncomputable section
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoDividedLiftClosed

universe u

private def nativeClosedDerivative {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    {j : ℕ} (c : Fin j → C) (hc : (MvPolynomial.aeval (R := R) c).toRingHom.Etale) :
    KaehlerDifferential R C →+ (⋀[C]^2 (KaehlerDifferential R C)) where
  toFun w := Cartier.EtaleDeRham.differential c hc 1
    ((exteriorPower.oneEquiv C (KaehlerDifferential R C)).symm w)
  map_zero' := by rw [map_zero, map_zero]
  map_add' w z := by rw [map_add, map_add]

private theorem nativeClosedDerivative_smul {R C : Type u}
    [CommRing R] [CommRing C] [Algebra R C] {j : ℕ}
    (c : Fin j → C) (hc : (MvPolynomial.aeval (R := R) c).toRingHom.Etale)
    (a : C) (w : KaehlerDifferential R C) :
    nativeClosedDerivative c hc (a • w) =
      Cartier.PolynomialDeRham.leftWedge (KaehlerDifferential.D R C a) 1
        ((exteriorPower.oneEquiv C (KaehlerDifferential R C)).symm w) +
      a • nativeClosedDerivative c hc w := by
  change Cartier.EtaleDeRham.differential c hc 1
    ((exteriorPower.oneEquiv C (KaehlerDifferential R C)).symm (a • w)) = _
  rw [map_smul, Cartier.EtaleDifferentialLeibniz.differential_smul]
  rfl

private theorem nativeClosedDerivative_smul_of_constant {R C : Type u}
    [CommRing R] [CommRing C] [Algebra R C] {j : ℕ}
    (c : Fin j → C) (hc : (MvPolynomial.aeval (R := R) c).toRingHom.Etale)
    (a : C) (w : KaehlerDifferential R C) (ha : KaehlerDifferential.D R C a = 0) :
    nativeClosedDerivative c hc (a • w) = a • nativeClosedDerivative c hc w := by
  rw [nativeClosedDerivative_smul, ha]
  change Cartier.EtaleDifferentialLeibniz.leftWedgeLinear 1 0 _ + _ = _
  rw [map_zero, LinearMap.zero_apply, zero_add]

private theorem nativeClosedDerivative_power_add {R C : Type u}
    [CommRing R] [CommRing C] [Algebra R C] {j : ℕ}
    (c : Fin j → C) (hc : (MvPolynomial.aeval (R := R) c).toRingHom.Etale)
    (a b : C) (m : ℕ) :
    nativeClosedDerivative c hc (a^m • KaehlerDifferential.D R C a + KaehlerDifferential.D R C b) = 0 := by
  change Cartier.EtaleDeRham.differential c hc 1
    ((exteriorPower.oneEquiv C (KaehlerDifferential R C)).symm
      (a^m • KaehlerDifferential.D R C a + KaehlerDifferential.D R C b)) = 0
  rw [map_add, map_smul, map_add,
    Cartier.EtaleDifferentialLeibniz.differential_power_universalD,
    Cartier.EtaleDifferentialLeibniz.differential_universalD, add_zero]

private theorem nativeTensorDifferential_tmul {R S C : Type u}
    [CommRing R] [CommRing S] [CommRing C] [Algebra R S] [Algebra R C]
    (s : S) (a : C) :
    KaehlerDifferential.D S (S ⊗[R] C) (s ⊗ₜ[R] a) =
      algebraMap S (S ⊗[R] C) s •
        KaehlerDifferential.D S (S ⊗[R] C) ((1 : S) ⊗ₜ[R] a) := by
  have ht : s ⊗ₜ[R] a = algebraMap S (S ⊗[R] C) s * ((1 : S) ⊗ₜ[R] a) := by
    change s ⊗ₜ[R] a = (s ⊗ₜ[R] (1 : C)) * ((1 : S) ⊗ₜ[R] a)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule

variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev N := KaehlerDifferential k (B p k A)
variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- The actual original degree-one residue exterior differential on native Kähler forms. -/
def closedDerivative : N p k A →+ (⋀[B p k A]^2 (N p k A)) := nativeClosedDerivative v hv

/-- The SAME actual produced divided coordinate value is closed in the actual residue complex. -/
theorem coordinate_closed (a : A) :
    closedDerivative p k A v hv (WittTwoDividedLift.dividedLiftDifferential p k A
      (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A)
        ((1 : ULift.{0} (WittTwo.Ring p k)) ⊗ₜ[WittTwo.Ring p k] a))) = 0 := by
  obtain ⟨b, _, hb⟩ := WittTwoDividedLift.dividedLiftDifferential_coordinate p k A a
  rw [hb]
  unfold closedDerivative
  let abar : B p k A := (1 : k) ⊗ₜ[WittTwo.Ring p k] a
  let bbar : B p k A := (1 : k) ⊗ₜ[WittTwo.Ring p k] b
  have hclosed := nativeClosedDerivative_power_add (R := k) (C := B p k A) v hv abar bbar (p-1)
  convert hclosed using 1

attribute [local instance] WittTwoDividedLift.residueLiftAlgebra

private theorem sourceCoefficient_closed (t : T p k A) :
    KaehlerDifferential.D k (B p k A) (algebraMap (T p k A) (B p k A) t) = 0 := by
  have h := WittTwoRelativeDifferential.residueFrobenius_differential_zero p k A t
  rw [← WittTwoRelativeDifferential.liftRingMap_reduction] at h
  convert h using 1
  rfl

private theorem closedDerivative_source_smul (t : T p k A) (w : N p k A) :
    closedDerivative p k A v hv (t • w) =
      algebraMap (T p k A) (B p k A) t • closedDerivative p k A v hv w := by
  have h := nativeClosedDerivative_smul_of_constant (R := k) (C := B p k A) v hv
    (algebraMap (T p k A) (B p k A) t) w (sourceCoefficient_closed p k A t)
  unfold closedDerivative
  convert h using 1
  rw [IsScalarTower.algebraMap_smul (B p k A)]

/-- EVERY original universal source differential has its SAME actual closed divided image. -/
theorem universal_closed (t : T p k A) :
    closedDerivative p k A v hv (WittTwoDividedLift.dividedLiftDifferential p k A
      (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A) t)) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
  | tmul s a =>
    have hd := nativeTensorDifferential_tmul (R := WittTwo.Ring p k)
      (S := ULift.{0} (WittTwo.Ring p k)) (C := A) s a
    rw [hd, map_smul, closedDerivative_source_smul, coordinate_closed, smul_zero]

/-- The SAME entire actual divided lift differential has genuinely closed image on EVERY source form. -/
theorem dividedLift_closed
    (w : KaehlerDifferential (ULift.{0} (WittTwo.Ring p k)) (T p k A)) :
    closedDerivative p k A v hv (WittTwoDividedLift.dividedLiftDifferential p k A w) = 0 := by
  have hw : w ∈ Submodule.span (T p k A)
      (Set.range (KaehlerDifferential.D (ULift.{0} (WittTwo.Ring p k)) (T p k A))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact universal_closed p k A v hv t
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul t x _ hx => rw [map_smul, closedDerivative_source_smul, hx, smul_zero]

/-- EVERY genuine native residue source form has a closed image under the SAME actual divided map. -/
theorem residueDividedLift_closed
    (w : KaehlerDifferential k (WittTwoSourceResidue.SourceResidue p k A)) :
    closedDerivative p k A v hv (WittTwoSourceResidue.residueDividedLift p k A w) = 0 := by
  obtain ⟨z, rfl⟩ := WittTwoSourceResidue.sourceReduction_surjective p k A w
  rw [WittTwoSourceResidue.residueDividedLift_reduction]
  exact dividedLift_closed p k A v hv z

end EnvelopeProperty.DeligneIllusie.WittTwoDividedLiftClosed
