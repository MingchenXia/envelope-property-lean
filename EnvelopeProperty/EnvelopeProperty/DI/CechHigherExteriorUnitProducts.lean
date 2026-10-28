import EnvelopeProperty.DI.CechTotalCupEvaluation

/-! # Original exterior units under the ordered last-entry product -/
noncomputable section
namespace EnvelopeProperty.DI.CechHigherExteriorUnitProducts
open AlgebraicGeometry CategoryTheory Opposite
open Cartier Cartier.DeligneIllusieCechCupProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coe_degreeCast {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    {a b : ℕ} (h : a=b) (x : ⋀[R]^a M) :
    ((h ▸ x : ⋀[R]^b M) : ExteriorAlgebra R M) = (x : ExteriorAlgebra R M) := by
  cases h
  rfl

/-- The original homogeneous product retains the initial tuple followed by its LAST input. -/
theorem wedgeProduct_init_last {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (q : ℕ) (m : Fin (q+1) → M) :
    (Nat.add_comm 1 q ▸ EtaleGradedLeibniz.wedgeProduct q 1
      (exteriorPower.ιMulti R q (Fin.init m))
      (exteriorPower.ιMulti R 1 (fun _ => m (Fin.last q)))) =
      exteriorPower.ιMulti R (q+1) m := by
  apply Subtype.ext
  rw [coe_degreeCast, EtaleGradedLeibniz.coe_wedgeProduct]
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  conv_rhs => rw [List.ofFn_succ', List.prod_concat]
  congr 1
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]


section OriginalUnits
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (p : ℕ) [Fact p.Prime] [CharP k p] (U : X.Opens)

/-- The original target unit along the ACTUAL relative-preimage equality. -/
def targetUnit (q : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U)) :
    Γ(SchemeRelativeFrobeniusDeRham.formModule f p q,
      RelativeTwistedAffineBasis.twistedOpen f p U) :=
  (CanonicalGeometry.exteriorCotangentSheaf f q).presheaf.map
    (eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)).op
      ((CanonicalGeometry.exteriorSheafificationMap
        (CanonicalGeometry.cotangentPresheaf f) q).app (op U) a)

/-- No coefficient identification is chosen: the original target units preserve
actual homogeneous multiplication along the original open-equality restriction. -/
theorem targetUnit_product (q r : ℕ)
    (a : (CanonicalGeometry.exteriorCotangentPresheaf f q).obj (op U))
    (b : (CanonicalGeometry.exteriorCotangentPresheaf f r).obj (op U)) :
    formWedge f p q r (RelativeTwistedAffineBasis.twistedOpen f p U)
      (targetUnit f p U q a) (targetUnit f p U r b) =
      targetUnit f p U (r+q) (EtaleGradedLeibniz.wedgeProduct q r a b) := by
  let P := CanonicalGeometry.cotangentPresheaf f
  let i := eqToHom (RelativeTwistedAffineBasis.relative_preimage f p U)
  have hr := exteriorSheafProductSection_restrict P q r i
    ((CanonicalGeometry.exteriorSheafificationMap P q).app (op U) a)
    ((CanonicalGeometry.exteriorSheafificationMap P r).app (op U) b)
  exact hr.symm.trans (congrArg
    ((CanonicalGeometry.exteriorCotangentSheaf f (r+q)).presheaf.map i.op)
    (exteriorSheafProductSection_unit P q r U a b))

private theorem targetUnit_cast {a b : ℕ} (h : a=b)
    (x : (CanonicalGeometry.exteriorCotangentPresheaf f a).obj (op U)) :
    CechWholeSectionLeibniz.degreeCast f p h
      (RelativeTwistedAffineBasis.twistedOpen f p U) (targetUnit f p U a x) =
        targetUnit f p U b (h ▸ x) := by
  cases h
  rfl

/-- Every native ordered target wedge retains the SAME original unit and the
actual final-entry degree transport. -/
theorem targetUnit_init_last (q : ℕ)
    (m : letI := CanonicalGeometry.cotangentOpenAlgebra f U
      Fin (q+1) → KaehlerDifferential k Γ(X,U)) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U
    CechWholeSectionLeibniz.degreeCast f p (Nat.add_comm 1 q)
      (RelativeTwistedAffineBasis.twistedOpen f p U)
      (formWedge f p q 1 (RelativeTwistedAffineBasis.twistedOpen f p U)
        (targetUnit f p U q (exteriorPower.ιMulti Γ(X,U) q (Fin.init m)))
        (targetUnit f p U 1 (exteriorPower.ιMulti Γ(X,U) 1 (fun _ => m (Fin.last q))))) =
      targetUnit f p U (q+1) (exteriorPower.ιMulti Γ(X,U) (q+1) m) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  rw [targetUnit_product, targetUnit_cast]
  exact congrArg (targetUnit f p U (q+1)) (wedgeProduct_init_last q m)

end OriginalUnits

end EnvelopeProperty.DI.CechHigherExteriorUnitProducts
