import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceBaseChange
import EnvelopeProperty.Vanishing.NadelWholeCoverDegree
import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeCore

/-! # The actual normalized coefficient trace on the same whole unit cover

The original whole degree and trace are reused.  The coefficient trace is
normalized only to construct an actual splitting of scalar extension; this
does not change the normalization of the desired original canonical trace.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory
open NadelCanonicalMixed
open scoped TensorProduct ChangeOfRings
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalTensorRetraction
    {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (ε : (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) →ₗ[R] R)
    (M : ModuleCat R) :
    (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M) ⟶ M := by
  let r := (TensorProduct.lid R M).toLinearMap.comp
    (TensorProduct.map ε (LinearMap.id : M →ₗ[R] M))
  exact ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M)) (Y := M)
    { toFun := r
      map_add' := r.map_add
      map_smul' a z := by
        change r (φ a • (show (ModuleCat.extendScalars φ).obj M from z)) = a • r z
        induction z using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
        | tmul s m =>
            change ε (φ a * (show S from s)) • m = a • (ε s • m)
            have h := ε.map_smul a s
            change ε (φ a * (show S from s)) = a * ε s at h
            rw [h, mul_smul] }

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {q : ℕ} (N : Fin q → ℕ) (u : Fin q → Aˣ) (hN : ∀ i, 0 < N i)
local notation "S" => UnitCover N u

/-- Actual normalized native trace of the SAME entire unit-root algebra.
The degree inverse is produced from the original characteristic-zero field. -/
def unitCoverCoefficientRetraction : S →ₗ[A] A :=
  (((NadelWholeCoverDegree.degree_isUnit (R := A) (k := k) N hN).unit⁻¹ : Aˣ) : A) •
    Algebra.trace A S

/-- The actual coefficient trace sends the original unit to the original unit. -/
theorem unitCoverCoefficientRetraction_one :
    unitCoverCoefficientRetraction (k := k) N u hN 1 = 1 := by
  let hD := NadelWholeCoverDegree.degree_isUnit (R := A) (k := k) N hN
  change ((hD.unit⁻¹ : Aˣ) : A) * Algebra.trace A S 1 = (1 : A)
  have h : Algebra.trace A S 1 = (hD.unit : A) :=
    (NadelWholeCoverDegree.trace_one N (fun i => (u i : A)) hN).trans hD.unit_spec.symm
  exact (congrArg (fun z : A => ((hD.unit⁻¹ : Aˣ) : A) * z) h).trans hD.unit.inv_val

/-- Every ORIGINAL base coefficient is fixed by the same produced trace. -/
theorem unitCoverCoefficientRetraction_algebraMap (a : A) :
    unitCoverCoefficientRetraction (k := k) N u hN (algebraMap A S a) = a := by
  let ε := unitCoverCoefficientRetraction (k := k) N u hN
  have hs : algebraMap A S a = a • (1 : S) := Algebra.algebraMap_eq_smul_one a
  have hε : ε 1 = 1 := unitCoverCoefficientRetraction_one (k := k) N u hN
  calc
    ε (algebraMap A S a) = ε (a • (1 : S)) := congrArg ε hs
    _ = a • ε 1 := ε.map_smul a 1
    _ = a • (1 : A) := congrArg (fun z : A => a • z) hε
    _ = a := mul_one a

/-- The genuine ε⊗id map on the native original scalar extension, with its
ORIGINAL restricted A action.  The coefficient retraction is produced internally. -/
def unitCoverSectionsRetraction (M : ModuleCat A) :
    (ModuleCat.restrictScalars (algebraMap A S)).obj
      ((ModuleCat.extendScalars (algebraMap A S)).obj M) ⟶ M :=
  originalTensorRetraction (algebraMap A S)
    ((unitCoverCoefficientRetraction (k := k) N u hN).comp
      (NadelKummerCanonicalBaseChange.algebraRestrictionEquiv (A := A) (B := S)).toLinearMap) M

omit [Nontrivial A] in
/-- Every original coefficient and original section is retained by ε⊗id. -/
theorem unitCoverSectionsRetraction_tmul (M : ModuleCat A) (s : S) (m : M) :
    unitCoverSectionsRetraction (k := k) N u hN M
      (show (ModuleCat.extendScalars (algebraMap A S)).obj M from
        s ⊗ₜ[A,algebraMap A S] m) =
      unitCoverCoefficientRetraction (k := k) N u hN s • m := rfl

/-- Whole native adjunction-unit splitting, not an incoming retraction certificate. -/
theorem unitCoverSectionsRetraction_unit (M : ModuleCat A) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A S)).unit.app M ≫
      unitCoverSectionsRetraction (k := k) N u hN M = 𝟙 M := by
  ext m
  change unitCoverCoefficientRetraction (k := k) N u hN (1 : S) • m = m
  rw [unitCoverCoefficientRetraction_one, one_smul]

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
