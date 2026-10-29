import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceBaseChange
import EnvelopeProperty.Vanishing.NadelMixedKummerDifferential

/-! # Actual branch-root divisibility with original variable units

The factor retains the derivative of the original unit coefficient.  No
unit is treated as a constant, and no bounded differential certificate
is supplied by the caller.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual differential of a branch coordinate is divisible by the
original root to order m−1, with its entire original variable-unit term. -/
theorem unitRootDifferential_factor
    {k B M : Type u} [CommRing k] [CommRing B] [Algebra k B]
    [AddCommGroup M] [Module B M] [Module k M] (D : Derivation k B M)
    (U : Bˣ) (x t : B) (m : ℕ) (hm : 0 < m)
    (hroot : t ^ m = (U : B) * x) :
    D x = t ^ (m - 1) •
      ((((U⁻¹ : Bˣ) : B) * (m : B)) • D t -
        (((U⁻¹ : Bˣ) : B) ^ 2 * t) • D (U : B)) := by
  let v : B := ((U⁻¹ : Bˣ) : B)
  have hv : v * (U : B) = 1 := U.inv_val
  have hp : t ^ m = t ^ (m - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hm)]
  have hx : x = v * t ^ m := by
    calc
      x = v * ((U : B) * x) := by rw [← mul_assoc, hv, one_mul]
      _ = v * t ^ m := congrArg (fun z : B => v * z) hroot.symm
  have hd := congrArg (fun z : M => v • z) (congrArg D hroot)
  simp only [Derivation.leibniz_pow, Derivation.leibniz, smul_add, smul_smul,
    hv, one_smul] at hd
  have hd' : ((v * (m : B)) * t ^ (m - 1)) • D t =
      D x + (v * x) • D (U : B) := by
    simpa only [← Nat.cast_smul_eq_nsmul B, smul_smul, mul_assoc] using hd
  have hc : v * x = t ^ (m - 1) * (v ^ 2 * t) := by
    rw [hx, hp]
    ring
  calc
    D x = ((v * (m : B)) * t ^ (m - 1)) • D t -
        (v * x) • D (U : B) := (eq_sub_iff_add_eq.mpr hd'.symm)
    _ = t ^ (m - 1) • ((v * (m : B)) • D t -
        (v ^ 2 * t) • D (U : B)) := by
      rw [smul_sub, smul_smul, smul_smul, hc]
      exact congrArg (fun z : B => z • D t -
        (t ^ (m - 1) * (v ^ 2 * t)) • D (U : B))
        (mul_comm (v * (m : B)) (t ^ (m - 1)))

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
local notation "B" => mixedRing x N I σ u

/-- EVERY actual original active branch in the SAME whole mixed quotient
has its required root-order differential factor.  The derivative of the
original unit remains in the produced factor.  No coordinate-smoothness,
root regularity, differential model or desired divisibility is assumed. -/
theorem mixedBranchDifferential_factor (hN : ∀ i, 0 < N i) (i : I) :
    KaehlerDifferential.D k B (algebraMap A B (x (σ i))) =
      root N (mixedCoefficient x I σ u) i.1 ^ (N i.1 - 1) •
        ((((((u i.1).map (algebraMap A B))⁻¹ : Bˣ) : B) *
            (N i.1 : B)) • KaehlerDifferential.D k B
              (root N (mixedCoefficient x I σ u) i.1) -
          (((((u i.1).map (algebraMap A B))⁻¹ : Bˣ) : B) ^ 2 *
            root N (mixedCoefficient x I σ u) i.1) •
              KaehlerDifferential.D k B (algebraMap A B (u i.1 : A))) := by
  let U : Bˣ := (u i.1).map (algebraMap A B)
  have hU : (U : B) = algebraMap A B (u i.1 : A) := rfl
  have hc : mixedCoefficient x I σ u i.1 = (u i.1 : A) * x (σ i) := by
    exact dif_pos i.2
  have hroot : root N (mixedCoefficient x I σ u) i.1 ^ N i.1 =
      (U : B) * algebraMap A B (x (σ i)) := by
    calc
      _ = algebraMap A B (mixedCoefficient x I σ u i.1) :=
        root_pow N (mixedCoefficient x I σ u) i.1
      _ = algebraMap A B ((u i.1 : A) * x (σ i)) := congrArg (algebraMap A B) hc
      _ = algebraMap A B (u i.1 : A) * algebraMap A B (x (σ i)) :=
        map_mul (algebraMap A B) (u i.1 : A) (x (σ i))
      _ = (U : B) * algebraMap A B (x (σ i)) :=
        congrArg (fun z : B => z * algebraMap A B (x (σ i))) hU.symm
  exact unitRootDifferential_factor (KaehlerDifferential.D k B) U
    (algebraMap A B (x (σ i))) (root N (mixedCoefficient x I σ u) i.1)
    (N i.1) (hN i.1) hroot

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
