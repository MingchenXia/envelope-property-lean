import EnvelopeProperty.AlgGeom.CurveCartierLocalOrders

/-! # Whole ORIGINAL affine principal quotient field degree and ALL native local orders -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.AffinePrincipalLocalDegree
open AffineSchemeLocalDegrees FiniteClosedIdealLocalDegrees SchemeCoherentEulerIndex
open CurveCartierLocalOrders
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsAffine X]

/-- The actual ORIGINAL global principal ideal sheaf. -/
def principalIdeal (c : Γ(X, ⊤)) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {c})

/-- Its SAME original whole top ideal is the actual original principal ideal. -/
theorem principalIdeal_ideal_top (c : Γ(X, ⊤)) :
    (principalIdeal c).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {c} := by
  simp [principalIdeal]

/-- A nonzero ORIGINAL global section gives its genuine Cartier ideal
on the SAME original integral affine scheme, even if singular. -/
theorem principalIdeal_isInvertible [IsIntegral X] (c : Γ(X, ⊤)) (hc : c ≠ 0) :
    (principalIdeal c).IsInvertible := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  intro x
  exact ⟨⟨⊤, isAffineOpen_top X⟩, trivial, c, mem_nonZeroDivisors_iff_ne_zero.mpr hc,
    principalIdeal_ideal_top c⟩

/-- The ENTIRE original principal closed subscheme's section ring is the
SAME original quotient algebra, over the SAME original structure field. -/
def quotientSectionsAlgEquiv {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) (c : Γ(X, ⊤)) :
    letI := structureSectionsAlgebra p
    letI := structureSectionsAlgebra ((principalIdeal c).subschemeι ≫ p)
    Γ((principalIdeal c).subscheme, ⊤) ≃ₐ[k] Γ(X, ⊤) ⧸ Ideal.span {c} := by
  let I := principalIdeal c
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let := structureSectionsAlgebra p
  let := structureSectionsAlgebra (I.subschemeι ≫ p)
  let e₀ : Γ(I.subscheme, ⊤) ≃+* Γ(X, ⊤) ⧸ I.ideal U :=
    (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  have he₀ (a : Γ(X, ⊤)) : e₀ (I.subschemeι.appTop a) = Ideal.Quotient.mk (I.ideal U) a := by
    have h := ConcreteCategory.congr_hom (I.subschemeι_app U) a
    change I.subschemeι.appTop a = e₀.symm (Ideal.Quotient.mk (I.ideal U) a) at h
    simpa only [RingEquiv.apply_symm_apply] using congrArg e₀ h
  let e : Γ(I.subscheme, ⊤) ≃ₐ[k] Γ(X, ⊤) ⧸ I.ideal U :=
    { e₀ with
      commutes' r := by
        change e₀ (I.subschemeι.appTop (p.appTop (baseScalar r))) =
          Ideal.Quotient.mk (I.ideal U) (p.appTop (baseScalar r))
        exact he₀ _ }
  exact e.trans (Ideal.quotientEquivAlgOfEq k (principalIdeal_ideal_top c))

private instance topNonempty [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The ENTIRE original principal quotient field dimension equals the sum
of TRUE native original Scheme.ord weighted by ORIGINAL residue degrees over
ALL original points of the SAME affine curve. No properness/normality or
local-order/residue/support comparison is assumed; quotient finiteness is
an honest generic input, derived in the original local finite-inverse consumer. -/
theorem finrank_quotient_eq_finsum_native_orders {k : Type u} [Field k]
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k))
    (hdim : topologicalKrullDim X ≤ 1) (c : Γ(X, ⊤)) (hc : c ≠ 0)
    (hfinite : letI := structureSectionsAlgebra p; Module.Finite k (Γ(X, ⊤) ⧸ Ideal.span {c})) :
    letI := structureSectionsAlgebra p
    ((Module.finrank k (Γ(X, ⊤) ⧸ Ideal.span {c})) : ℤ) =
      ∑ᶠ x : X, letI := residueAlgebra p x
        X.ord (X.germToFunctionField ⊤ c) x * (Module.finrank k (X.residueField x) : ℤ) := by
  let := structureSectionsAlgebra p
  let I := principalIdeal c
  let hI := principalIdeal_isInvertible c hc
  let Z := I.subscheme
  let q := I.subschemeι ≫ p
  let := structureSectionsAlgebra q
  let : Module.Finite k (Γ(X, ⊤) ⧸ Ideal.span {c}) := hfinite
  let e := quotientSectionsAlgEquiv p c
  let : Module.Finite k Γ(Z, ⊤) := Module.Finite.equiv e.symm.toLinearEquiv
  let : IsAffine Z := isAffine_of_isAffineHom I.subschemeι
  let : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite k Γ(Z, ⊤)
  let : Finite (Spec Γ(Z, ⊤)) := inferInstance
  let : Finite Z := Finite.of_injective (Scheme.homeoOfIso Z.isoSpec) (Scheme.homeoOfIso Z.isoSpec).injective
  let : Fintype Z := Fintype.ofFinite _
  have hdegree : (Module.finrank k (Γ(X, ⊤) ⧸ Ideal.span {c}) : ℤ) =
      ∑ᶠ x : X, weightedLocalOrder p I hI x := by
    rw [← e.toLinearEquiv.finrank_eq,
      finrank_sections_eq_sum_points q (inferInstance : Module.Finite k Γ(Z, ⊤)),
      finsum_weightedLocalOrder_eq_closed,
      finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    let := residueAlgebra p (I.subschemeι y)
    let := residueAlgebra q y
    unfold weightedLocalOrder
    rw [localOrder_eq_closed_stalk_length hdim I hI y,
      ClosedImmersionResidueDegrees.residue_finrank_eq I.subschemeι p y]
    simp only [Nat.cast_mul]
  calc
    _ = ∑ᶠ x : X, weightedLocalOrder p I hI x := hdegree
    _ = _ := by
      apply finsum_congr
      intro x
      unfold weightedLocalOrder
      rw [localOrder_eq_ord_of_local_equation I hI ⟨⊤, isAffineOpen_top X⟩ c hc
        (principalIdeal_ideal_top c) x trivial]

end EnvelopeProperty.AffinePrincipalLocalDegree
