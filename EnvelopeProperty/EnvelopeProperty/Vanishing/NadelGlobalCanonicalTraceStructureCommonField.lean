import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGenericSections
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureFieldIso

/-! # Every original local trace has the SAME whole original generic value

The actual local finite-free trace, actual generic-fiber isomorphism and
actual original section transport are combined. No value-match or trace
compatibility certificate is an input to the original chart theorem.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules FlatGlobalSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem fieldTrace_iso_top_over (K : CommRingCat.{u}) (hK : IsField K)
    {W Z : Scheme.{u}} (q : Z ⟶ Spec K) [IsFinite q]
    (q' : W ⟶ Spec K) [IsFinite q'] (e : W ≅ Z) (h : e.hom ≫ q = q') (b : Γ(Z, ⊤)) :
    (Scheme.ΓSpecIso K).hom ((fieldStructureTrace K hK q').app ⊤ (e.hom.appTop b)) =
      (Scheme.ΓSpecIso K).hom ((fieldStructureTrace K hK q).app ⊤ b) := by
  subst q'
  exact fieldStructureTrace_iso_top K hK q e b

variable {X Y : Scheme.{u}} [IsIntegral X] {π : Y ⟶ X} [IsFinite π] {D : ℕ}
    (C : WholeFreeChart π D) [Nonempty C.base.1]

/-- Every ACTUAL original local trace coefficient has the native trace
of its SAME original whole generic section under the original germ map. -/
theorem traceOnSpec_commonField_top
    (w : Γ((restrictFunctor C.base.2.fromSpec).obj
      ((pushforward π).obj (unitObj Y)), ⊤)) :
    let γ := X.fromSpecStalk (genericPoint X)
    let q := pullback.snd π γ
    let _ : Algebra X.functionField Γ(pullback π γ, ⊤) :=
      ((Scheme.ΓSpecIso X.functionField).inv ≫ q.appTop).hom.toAlgebra
    algebraMap Γ(X, C.base.1) X.functionField
      ((Scheme.ΓSpecIso Γ(X, C.base.1)).hom
        ((restrictUnitIso C.base.2.fromSpec).hom.app ⊤ (C.traceOnSpec.app ⊤ w))) =
      Algebra.trace X.functionField Γ(pullback π γ, ⊤) (C.genericOriginalSection w) := by
  let _ := C.algebra
  let : Module.Free Γ(X, C.base.1) C.coeff := Module.Free.of_basis C.basis
  let : Module.Finite Γ(X, C.base.1) C.coeff := Module.Finite.of_basis C.basis
  let : IsFinite C.scalarMap :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let γ := X.fromSpecStalk (genericPoint X)
  let q := pullback.snd π γ
  let ql := pullback.snd C.scalarMap C.genericBaseMap
  let b := (pullback.fst C.scalarMap C.genericBaseMap).appTop (C.pushforwardIso.hom.app ⊤ w)
  let _ : Algebra X.functionField Γ(pullback π γ, ⊤) :=
    ((Scheme.ΓSpecIso X.functionField).inv ≫ q.appTop).hom.toAlgebra
  have hK : IsField X.functionField :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by simp [irreducibleComponents_eq_singleton])
  have hl : (Scheme.ΓSpecIso X.functionField).hom ((fieldStructureTrace X.functionField hK ql).app ⊤ b) =
      algebraMap Γ(X, C.base.1) X.functionField
        ((Scheme.ΓSpecIso Γ(X, C.base.1)).hom
          ((restrictUnitIso C.base.2.fromSpec).hom.app ⊤ (C.traceOnSpec.app ⊤ w))) :=
    C.traceOnSpec_fieldBaseChange_top X.functionField hK w
  have hq : C.genericFiberIso.inv ≫ ql = q := by
    change C.genericFiberIso.inv ≫ pullback.snd C.scalarMap C.genericBaseMap =
      pullback.snd π (X.fromSpecStalk (genericPoint X))
    rw [← C.genericFiberIso_snd, Iso.inv_hom_id_assoc]
  have hi := fieldTrace_iso_top_over X.functionField hK ql q C.genericFiberIso.symm hq b
  have hs := C.genericFiberIso_originalSection w
  exact hl.symm.trans (hi.symm.trans
    ((congrArg (fun z => (Scheme.ΓSpecIso X.functionField).hom
      ((fieldStructureTrace X.functionField hK q).app ⊤ z)) hs).trans
      (fieldStructureTrace_top X.functionField hK q (C.genericOriginalSection w))))

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart
