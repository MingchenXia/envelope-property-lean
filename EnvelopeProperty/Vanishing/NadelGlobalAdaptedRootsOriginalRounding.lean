import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsRoundedLine
import EnvelopeProperty.Char0.RoundedCanonicalModule
import Mathlib.Algebra.Order.Floor.Semifield

/-! # The original rational exponent, actual residues, and WHOLE intrinsic rounding

All fractional root weights are computed from the ORIGINAL rational exponent
and ORIGINAL SNC multiplicities. The intrinsic rounded ideal is retained and
the actual whole cleared ideal/line identities are proved internally.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry Char0
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original rational exponent and original multiplicity determine
the fractional weight; it is not an arbitrary incoming root weight. -/
def fractionalRootWeight (q : ℚ) (b : ℕ) : ℕ :=
  (q.num.toNat * b) % q.den

/-- The actual original fractional weight satisfies the canonical trace bound. -/
theorem fractionalRootWeight_lt (q : ℚ) (b : ℕ) :
    fractionalRootWeight q b < q.den := Nat.mod_lt _ q.den_pos

/-- The natural floor is the literal original quotient exponent. -/
theorem originalFloorExponent (q : ℚ) (hq : 0 ≤ q) (b : ℕ) :
    ⌊q * (b : ℚ)⌋₊ = q.num.toNat * b / q.den := by
  have hN : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hcast : (q.num.toNat : ℚ) = (q.num : ℚ) := by exact_mod_cast hN
  have hq' : q = (q.num.toNat : ℚ) / (q.den : ℚ) := by
    rw [hcast]
    exact q.num_div_den.symm
  have hqb : q * (b : ℚ) = ((q.num.toNat * b : ℕ) : ℚ) / (q.den : ℚ) := by
    calc
      q * (b : ℚ) = ((q.num.toNat : ℚ) / (q.den : ℚ)) * (b : ℚ) :=
        congrArg (fun t : ℚ => t * (b : ℚ)) hq'
      _ = _ := by rw [Nat.cast_mul]; ring
  exact (congrArg (fun t : ℚ => ⌊t⌋₊) hqb).trans (Nat.floor_div_eq_div _ _)

/-- Actual floor and residue exponents clear the SAME original denominator. -/
theorem originalClearedExponent (q : ℚ) (hq : 0 ≤ q) (b d : ℕ)
    (hd : q.den ∣ d) :
    ⌊q * (b : ℚ)⌋₊ * d + fractionalRootWeight q b * (d / q.den) =
      b * (q.num.toNat * (d / q.den)) := by
  rw [originalFloorExponent q hq b]
  unfold fractionalRootWeight
  have hfirst : (q.num.toNat * b / q.den) * d =
      (q.den * (q.num.toNat * b / q.den)) * (d / q.den) := by
    calc
      (q.num.toNat * b / q.den) * d =
          (q.num.toNat * b / q.den) * (q.den * (d / q.den)) :=
        congrArg (fun t : ℕ => (q.num.toNat * b / q.den) * t)
          (Nat.mul_div_cancel' hd).symm
      _ = _ := by ac_rfl
  rw [hfirst]
  calc
    (q.den * (q.num.toNat * b / q.den)) * (d / q.den) +
        (q.num.toNat * b % q.den) * (d / q.den) =
      (q.num.toNat * b % q.den + q.den * (q.num.toNat * b / q.den)) *
        (d / q.den) := by ring
    _ = (q.num.toNat * b) * (d / q.den) :=
      congrArg (fun t : ℕ => t * (d / q.den)) (Nat.mod_add_div _ _)
    _ = b * (q.num.toNat * (d / q.den)) := by ac_rfl

/-- The entire ORIGINAL intrinsic rounded ideal clears to the original
SNC ideal's power. No rounded/divisor comparison is an input. -/
theorem originalRoundedIdeal_clearedPower {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (F : X.DivisorFamily) (hF : F.IsSnc)
    (b : F.ι → ℕ) (hJF : J = ∏ i, F.component i ^ b i)
    (q : ℚ) (hq : 0 ≤ q) (d : ℕ) (hd : q.den ∣ d) :
    RoundedSncIdealSheaf.rounded J hJ q ^ d *
        clearedRoundedIdeal F (fun _ => q.den) (fun i => fractionalRootWeight q (b i)) d =
      J ^ (q.num.toNat * (d / q.den)) := by
  classical
  rw [RoundedSncIdealSheaf.rounded_eq_product f J hJ hF b hJF q]
  unfold RoundedSncIdealSheaf.product clearedRoundedIdeal
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, hJF, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  calc
    (F.component i ^ ⌊q * (b i : ℚ)⌋₊) ^ d *
        F.component i ^ (fractionalRootWeight q (b i) * (d / q.den)) =
      F.component i ^ (⌊q * (b i : ℚ)⌋₊ * d +
        fractionalRootWeight q (b i) * (d / q.den)) := by simp only [pow_add, pow_mul]
    _ = F.component i ^ (b i * (q.num.toNat * (d / q.den))) :=
      congrArg (fun e : ℕ => F.component i ^ e) (originalClearedExponent q hq (b i) d hd)
    _ = (F.component i ^ b i) ^ (q.num.toNat * (d / q.den)) := pow_mul _ _ _

/-- The SAME original ceil line has its internally computed actual cleared
line comparison, retaining the entire intrinsic RoundedCanonicalModule ideal. -/
def originalClearedRoundedLineIso {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (F : X.DivisorFamily) (hF : F.IsSnc)
    (b : F.ι → ℕ) (hJF : J = ∏ i, F.component i ^ b i)
    (M : X.Modules) (q : ℚ) (hq : 0 ≤ q) (d : ℕ) (hd : q.den ∣ d) :
    Scheme.Modules.tensorObj
      (bundleTensorPower (Scheme.Modules.tensorObj M (RoundedCanonicalModule.idealModule J hJ q)) d)
      (clearedRoundedIdeal F (fun _ => q.den) (fun i => fractionalRootWeight q (b i)) d).toModules ≅
      Scheme.Modules.tensorObj (bundleTensorPower M d)
        (J ^ (q.num.toNat * (d / q.den))).toModules := by
  let I := RoundedSncIdealSheaf.rounded J hJ q
  let K := clearedRoundedIdeal F (fun _ => q.den) (fun i => fractionalRootWeight q (b i)) d
  have hI : I.IsInvertible := RoundedSncIdealSheaf.rounded_isInvertible f J hJ q
  have hpower : I ^ d * K = J ^ (q.num.toNat * (d / q.den)) :=
    originalRoundedIdeal_clearedPower f J hJ F hF b hJF q hq d hd
  let E : bundleTensorPower (Scheme.Modules.tensorObj M I.toModules) d ≅
      bundleTensorPower M d ⊗ (I ^ d).toModules :=
    BundleTensorPowerPullback.powerIso (ModularCurves.monoidalTensorObjIso M I.toModules).symm d ≪≫
      BundleTensorPowerTensor.powerTensorIso M I.toModules d ≪≫
      (Iso.refl _ ⊗ᵢ NadelBlowupCanonicalIdealPowers.tensorPowerIso I hI d)
  exact (ModularCurves.monoidalTensorObjIso _ K.toModules).symm ≪≫
    (E ⊗ᵢ Iso.refl K.toModules) ≪≫
    (α_ (bundleTensorPower M d) (I ^ d).toModules K.toModules) ≪≫
    (Iso.refl _ ⊗ᵢ
      (ModularCurves.monoidalTensorObjIso (I ^ d).toModules K.toModules ≪≫
        NadelBlowupCanonicalIdealProduct.tensorProductIso (I ^ d)
          (Scheme.IdealSheafData.isInvertible_pow hI d) K ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.toModules hpower))) ≪≫
    ModularCurves.monoidalTensorObjIso (bundleTensorPower M d) _

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
