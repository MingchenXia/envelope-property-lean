import EnvelopeProperty.AlgGeom.SchemeTraitResidueFinite

/-! # Actual closed trait centers give genuine proper residual models -/
open AlgebraicGeometry CategoryTheory IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemePolynomialTraitClosure

private theorem point_structure {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) (z : Y) :
    Y.fromSpecResidueField z ≫ f = Spec.map (CommRingCat.ofHom
      ((Y.residue z).hom.comp (SchemeStalkCoefficients.coefficientMap f z))) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [Category.assoc,SchemeStalkCoefficients.fromSpecStalk_structureMap,← Spec.map_comp]
  rfl

private theorem hom_ext_toSpec {A : Type u} [CommRing A] {S T : Scheme.{u}}
    (g : S ⟶ T) [IsSchemeTheoreticallyDominant g] [QuasiCompact g]
    (a b : T ⟶ Spec (.of A)) (h : g ≫ a = g ≫ b) : a = b := by
  let : Mono g.appTop := ConcreteCategory.mono_of_injective _ (g.app_injective ⊤)
  apply ext_to_Spec
  have ht := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop,Scheme.Hom.comp_appTop] at ht
  exact congrArg (fun a => (Scheme.ΓSpecIso (.of A)).inv ≫ a)
    ((cancel_mono g.appTop).mp ht)

variable {E V : Type u} [Field E] [CommRing V] [IsLocalRing V] [Algebra E V]
  {Y : Scheme.{u}} (f : Y ⟶ Spec (.of (Polynomial E)))
  (q : Spec (.of V) ⟶ Y) (t : V)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (Polynomial.aeval t).toRingHom))
  (ht : t ∈ maximalIdeal V)

/-- The actual original coefficient structure of the polynomial model. -/
def coefficientBaseMap : Y ⟶ Spec (.of E) :=
  f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))

include hq in
omit [IsLocalRing V] in
private theorem trait_coefficientBaseMap :
    q ≫ coefficientBaseMap f = Spec.map (CommRingCat.ofHom (algebraMap E V)) := by
  rw [coefficientBaseMap,← Category.assoc,hq,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact Polynomial.aeval_C t c

include hq ht in
/-- The SAME original trait center residue point genuinely lies in the actual
zero-parameter fibre, preserving the entire original coefficient diagram. -/
theorem residuePoint_structure_zero :
    Y.fromSpecResidueField (q (closedPoint V)) ≫ f =
      (Y.fromSpecResidueField (q (closedPoint V)) ≫ coefficientBaseMap f) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : E))) := by
  let z := q (closedPoint V)
  let := SchemePointClosureCurve.residueAlgebra z (coefficientBaseMap f)
  let ψ : Polynomial E →+* Y.residueField z :=
    (Y.residue z).hom.comp (SchemeStalkCoefficients.coefficientMap f z)
  let α := SchemeLocalResidueCoefficients.residueAlgHom (coefficientBaseMap f) q
    (trait_coefficientBaseMap f q t hq)
  have hc : ψ.comp Polynomial.C = algebraMap E (Y.residueField z) := by
    have hcat : CommRingCat.ofHom (ψ.comp Polynomial.C) =
        CommRingCat.ofHom (algebraMap E (Y.residueField z)) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom Polynomial.C ≫ CommRingCat.ofHom ψ) = _
      rw [Spec.map_comp,← point_structure f z]
      exact point_structure (coefficientBaseMap f) z
    exact congrArg CommRingCat.Hom.hom hcat
  have hx : ψ Polynomial.X = 0 := by
    apply α.injective
    rw [map_zero]
    change residue V ((Scheme.stalkClosedPointTo q)
      (SchemeStalkCoefficients.coefficientMap f z Polynomial.X)) = 0
    have hs : (Scheme.stalkClosedPointTo q).hom
        (SchemeStalkCoefficients.coefficientMap f z Polynomial.X) = t := by
      exact (RingHom.congr_fun (SchemeLocalResidueCoefficients.stalkClosedPointTo_coefficients
          f q (Polynomial.aeval t).toRingHom hq) Polynomial.X).trans (Polynomial.aeval_X t)
    exact (congrArg (residue V) hs).trans ((residue_eq_zero_iff t).mpr ht)
  have hψ : ψ = (algebraMap E (Y.residueField z)).comp (Polynomial.evalRingHom (0 : E)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_C] using
        RingHom.congr_fun hc c
    · simpa only [RingHom.comp_apply,Polynomial.coe_evalRingHom,Polynomial.eval_X,map_zero] using hx
  rw [point_structure f z,point_structure (coefficientBaseMap f) z,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact hψ

include hq ht in
/-- The WHOLE actual native center closure genuinely factors through the
original zero section, derived from its actual schematically dense residue point. -/
theorem closure_structure_zero :
    SchemePointClosureCurve.structureMap (q (closedPoint V)) f =
      SchemePointClosureCurve.structureMap (q (closedPoint V)) (coefficientBaseMap f) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : E))) := by
  let z := q (closedPoint V)
  let := SchemePointClosureCurve.closure_isIntegral z
  let : QuasiCompact (Y.fromSpecResidueField z) :=
    ⟨fun U _ _ => (Set.toFinite ((Y.fromSpecResidueField z) ⁻¹' U)).isCompact⟩
  let : QuasiCompact (SchemePointClosureCurve.genericMap z) := by
    dsimp only [SchemePointClosureCurve.genericMap]
    infer_instance
  let : IsDominant (SchemePointClosureCurve.genericMap z) := by
    dsimp only [SchemePointClosureCurve.genericMap]
    infer_instance
  let : IsSchemeTheoreticallyDominant (SchemePointClosureCurve.genericMap z) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  apply hom_ext_toSpec (SchemePointClosureCurve.genericMap z)
  calc
    _ = Y.fromSpecResidueField z ≫ f := by
      dsimp only [SchemePointClosureCurve.structureMap]
      rw [← Category.assoc,SchemePointClosureCurve.genericMap_inclusion]
    _ = (Y.fromSpecResidueField z ≫ coefficientBaseMap f) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : E))) :=
      residuePoint_structure_zero f q t hq ht
    _ = _ := by
      dsimp only [SchemePointClosureCurve.structureMap]
      change (Y.fromSpecResidueField z ≫ coefficientBaseMap f) ≫ _ =
        SchemePointClosureCurve.genericMap z ≫
          ((SchemePointClosureCurve.inclusion z ≫ coefficientBaseMap f) ≫ _)
      rw [← Category.assoc,← Category.assoc,SchemePointClosureCurve.genericMap_inclusion]

include hq ht in
/-- Original properness and the genuine closed-center factorization derive
true properness of the SAME native residual closure over its coefficient field. -/
theorem closure_isProper [IsProper f] :
    IsProper (SchemePointClosureCurve.structureMap (q (closedPoint V)) (coefficientBaseMap f)) := by
  let : IsProper (SchemePointClosureCurve.structureMap (q (closedPoint V)) f) :=
    SchemePointClosureCurve.structureMap_isProper _ f
  let : IsProper (SchemePointClosureCurve.structureMap (q (closedPoint V)) (coefficientBaseMap f) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : E)))) := by
    rw [← closure_structure_zero f q t hq ht]
    infer_instance
  exact IsProper.of_comp
    (SchemePointClosureCurve.structureMap (q (closedPoint V)) (coefficientBaseMap f))
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : E))))

end EnvelopeProperty.SchemePolynomialTraitClosure
