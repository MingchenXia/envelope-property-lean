import EnvelopeProperty.AlgGeom.CurveDenominatorCartier
import EnvelopeProperty.AlgGeom.CurveFiniteClosedSubschemes
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.KrullDimension.Field

/-! # Actual original curve local DVRs, rational valuations and section parameters -/
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped WithZero
noncomputable section
universe u
namespace EnvelopeProperty.CurveLocalDVRValuations
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (x : X) (hx : x ≠ genericPoint X)

include hdim hNormal hx

/-- Every SAME original nongeneric normal curve stalk is genuinely a DVR. -/
theorem stalk_isDiscreteValuationRing : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let := CurveDenominatorCartier.stalk_isPrincipalIdealRing hdim hNormal x
  refine { not_a_field' := ?_ }
  intro hz
  let : Field (X.presheaf.stalk x) :=
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hz).toField
  have hzero := ringKrullDim_eq_zero_of_field (X.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight, CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx] at hzero
  norm_num at hzero

/-- The actual original maximal ideal's valuation on the SAME canonical function field. -/
def functionFieldValuation : Valuation X.functionField ℤᵐ⁰ :=
  letI := stalk_isDiscreteValuationRing hdim hNormal x hx
  (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk x)).valuation X.functionField

/-- The original actual maximal-ideal valuation is genuinely rank-one discrete. -/
theorem functionFieldValuation_isRankOneDiscrete :
    (functionFieldValuation hdim hNormal x hx).IsRankOneDiscrete := by
  let := stalk_isDiscreteValuationRing hdim hNormal x hx
  exact IsDiscreteValuationRing.isRankOneDiscrete (X.presheaf.stalk x) X.functionField

/-- The SAME original scheme order homomorphism is the inverse of its actual stalk valuation. -/
theorem ordHom_eq_valuation_inv (f : X.functionField) :
    X.ordHom x (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) f =
      (functionFieldValuation hdim hNormal x hx f)⁻¹ := by
  let := stalk_isDiscreteValuationRing hdim hNormal x hx
  exact Ring.ordFrac_eq_valuation_inv f

/-- The actual valuation of EVERY SAME original nonzero rational function retains its native order. -/
theorem valuation_eq_exp_neg_ord (f : X.functionField) (hf : f ≠ 0) :
    functionFieldValuation hdim hNormal x hx f = WithZero.exp (-X.ord f x) := by
  have ho : X.ordHom x (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) f =
      WithZero.exp (X.ord f x) :=
    (X.ord_eq_iff (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) hf).mp rfl
  calc
    functionFieldValuation hdim hNormal x hx f =
        (X.ordHom x (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) f)⁻¹ := by
      rw [ordHom_eq_valuation_inv, inv_inv]
    _ = (WithZero.exp (X.ord f x))⁻¹ := congrArg Inv.inv ho
    _ = WithZero.exp (-X.ord f x) := by simp

/-- An actual original stalk parameter has original maximal ideal, order one and valuation exp(-1). -/
theorem exists_uniformizer :
    ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) = Ideal.span {π} ∧
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField π) x = 1 ∧
      functionFieldValuation hdim hNormal x hx
        (algebraMap (X.presheaf.stalk x) X.functionField π) = WithZero.exp (-1) := by
  let := stalk_isDiscreteValuationRing hdim hNormal x hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have hπK : algebraMap (X.presheaf.stalk x) X.functionField π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr hπ.ne_zero
  have ho : X.ord (algebraMap (X.presheaf.stalk x) X.functionField π) x = 1 := by
    apply (X.ord_eq_iff (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) hπK).mpr
    exact Ring.ordFrac_irreducible hπ
  refine ⟨π, hπ.ne_zero, hπ.maximalIdeal_eq, ho, ?_⟩
  rw [valuation_eq_exp_neg_ord hdim hNormal x hx _ hπK, ho]

/-- A true original neighborhood section represents an actual original parameter with order one. -/
theorem exists_local_parameter_section :
    ∃ (U : X.Opens) (hxU : x ∈ U) (c : Γ(X, U)),
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        Ideal.span {X.presheaf.germ U x hxU c} ∧
      (letI : Nonempty U := ⟨⟨x, hxU⟩⟩
       X.ord (X.germToFunctionField U c) x = 1 ∧
        functionFieldValuation hdim hNormal x hx (X.germToFunctionField U c) = WithZero.exp (-1)) := by
  obtain ⟨π, hπ0, hπ, ho, hv⟩ := exists_uniformizer hdim hNormal x hx
  obtain ⟨U, hxU, c, hc⟩ := X.presheaf.exists_germ_eq π
  refine ⟨U, hxU, c, ?_, ?_⟩
  · rw [hc]
    exact hπ
  · let : Nonempty U := ⟨⟨x, hxU⟩⟩
    have he : X.germToFunctionField U c = algebraMap (X.presheaf.stalk x) X.functionField π :=
      (X.algebraMap_germ_eq_germToFunctionField hxU c).symm.trans (congrArg
        (algebraMap (X.presheaf.stalk x) X.functionField) hc)
    rw [he]
    exact ⟨ho, hv⟩

end EnvelopeProperty.CurveLocalDVRValuations
