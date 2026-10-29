import EnvelopeProperty.Vanishing.NadelMixedKummerPresentation
import Mathlib.Algebra.Group.Commute.Units

/-! # Whole varying-degree common-branch quotient maps

Every equation and every original root is retained. The input equalities are
literal coefficient multiplication identities; neither an algebra comparison
nor a normalization comparison is an input.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.MultiRatio
open NadelMixedKummer
variable {R : Type u} [CommRing R] {q : ℕ}
  (N : Fin q → ℕ) (c b : Fin q → R) (H : Fin q → Fin q)
  (hH : ∀ i, H (H i) = H i) (hN : ∀ i, N (H i) = N i)
  (hb : ∀ i, b (H i) = c (H i))
  (hc : ∀ i, i ≠ H i → c i = c (H i) * b i)

/-- The actual monomial value of EVERY original raw root. -/
def forwardRoots (i : Fin q) : Ring N b :=
  if i = H i then root N b i else root N b (H i) * root N b i

include hN hb hc in
/-- Every original varying-degree raw equation holds in the WHOLE ratio ring. -/
theorem forwardRoots_pow (i : Fin q) :
    forwardRoots N b H i ^ N i = algebraMap R (Ring N b) (c i) := by
  by_cases hi : i = H i
  · rw [forwardRoots, if_pos hi, root_pow]
    apply congrArg (algebraMap R (Ring N b))
    simpa only [← hi] using hb i
  · rw [forwardRoots, if_neg hi, mul_pow, ← hN i, root_pow, hN i, root_pow,
      hb i, ← map_mul, ← hc i hi]

/-- The actual WHOLE raw-to-ratio algebra map, before inverting any branch. -/
def rawToRatio : Ring N c →+* Ring N b :=
  evaluate N c (algebraMap R (Ring N b)) (forwardRoots N b H)
    (forwardRoots_pow N c b H hN hb hc)

/-- The SAME original coefficient triangle for the whole map. -/
theorem rawToRatio_structure : (rawToRatio N c b H hN hb hc).comp
    (algebraMap R (Ring N c)) = algebraMap R (Ring N b) :=
  evaluate_structure _ _ _ _ _

/-- The whole original raw map is linear over the SAME original ring. -/
def rawAlgHom : Ring N c →ₐ[R] Ring N b :=
  { toRingHom := rawToRatio N c b H hN hb hc
    commutes' := fun z => congrArg (fun f : R →+* Ring N b => f z)
      (rawToRatio_structure N c b H hN hb hc) }

/-- Every original raw root has its actual monomial value. -/
theorem rawToRatio_root (i : Fin q) :
    rawToRatio N c b H hN hb hc (root N c i) = forwardRoots N b H i :=
  evaluate_root _ _ _ _ _ _

variable (hpositive : ∀ i, 0 < N i) (hunit : ∀ i, IsUnit (c (H i)))

include hpositive hunit in
/-- The SAME original distinguished root is a unit on the whole branch
complement, from its actual positive power equation. -/
theorem commonRoot_isUnit (i : Fin q) : IsUnit (root N c (H i)) := by
  apply (isUnit_pow_iff (Nat.ne_of_gt (hpositive (H i)))).mp
  rw [root_pow]
  exact (hunit i).map (algebraMap R (Ring N c))

/-- The actual internally constructed original distinguished-root unit. -/
def commonRootUnit (i : Fin q) : (Ring N c)ˣ :=
  (commonRoot_isUnit N c H hpositive hunit i).unit

/-- The constructed unit is the SAME actual original root. -/
theorem commonRootUnit_coe (i : Fin q) :
    (commonRootUnit N c H hpositive hunit i : Ring N c) = root N c (H i) :=
  (commonRoot_isUnit N c H hpositive hunit i).unit_spec

/-- Every ratio root has its actual original root quotient value. -/
def backwardRoots (i : Fin q) : Ring N c :=
  if i = H i then root N c i else root N c i *
    (((commonRootUnit N c H hpositive hunit i)⁻¹ : (Ring N c)ˣ) : Ring N c)

include hN hb hc in
/-- Every original ratio equation holds in the whole original raw algebra
when the original distinguished coefficients are units. -/
theorem backwardRoots_pow (i : Fin q) :
    backwardRoots N c H hpositive hunit i ^ N i = algebraMap R (Ring N c) (b i) := by
  by_cases hi : i = H i
  · rw [backwardRoots, if_pos hi, root_pow]
    apply congrArg (algebraMap R (Ring N c))
    simpa only [← hi] using (hb i).symm
  · rw [backwardRoots, if_neg hi, mul_pow, root_pow, hc i hi, map_mul]
    have hp : (commonRootUnit N c H hpositive hunit i : Ring N c) ^ N i =
        algebraMap R (Ring N c) (c (H i)) := by
      rw [commonRootUnit_coe, ← hN i, root_pow]
    rw [← hp]
    calc
      _ = algebraMap R (Ring N c) (b i) *
          ((commonRootUnit N c H hpositive hunit i : Ring N c) ^ N i *
            (((commonRootUnit N c H hpositive hunit i)⁻¹ : (Ring N c)ˣ) : Ring N c) ^ N i) := by ring
      _ = _ := by rw [← mul_pow, Units.mul_inv, one_pow, mul_one]

/-- The reverse WHOLE algebra map on the branch complement. -/
def ratioToRaw : Ring N b →+* Ring N c :=
  evaluate N b (algebraMap R (Ring N c)) (backwardRoots N c H hpositive hunit)
    (backwardRoots_pow N c b H hN hb hc hpositive hunit)

theorem ratioToRaw_structure : (ratioToRaw N c b H hN hb hc hpositive hunit).comp
    (algebraMap R (Ring N b)) = algebraMap R (Ring N c) := evaluate_structure _ _ _ _ _

theorem ratioToRaw_root (i : Fin q) :
    ratioToRaw N c b H hN hb hc hpositive hunit (root N b i) =
      backwardRoots N c H hpositive hunit i := evaluate_root _ _ _ _ _ _

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.MultiRatio
