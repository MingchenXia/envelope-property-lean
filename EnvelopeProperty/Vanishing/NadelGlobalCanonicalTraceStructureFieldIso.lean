import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureGenericFiber
import Mathlib.RingTheory.Trace.Basic

/-! # The actual whole finite-field trace respects original scheme isomorphisms

All scalar structures are the actual original coefficient maps. The
native section comparison and its complete coefficient compatibility
are proved from the original scheme isomorphism and composition law.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def actualSectionsIso (K : CommRingCat.{u}) {W Z : Scheme.{u}}
    (q : Z ⟶ Spec K) (e : W ≅ Z) :
    let _ : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso K).inv ≫ q.appTop).hom.toAlgebra
    let _ : Algebra K Γ(W, ⊤) :=
      ((Scheme.ΓSpecIso K).inv ≫ (e.hom ≫ q).appTop).hom.toAlgebra
    Γ(Z, ⊤) ≃ₐ[K] Γ(W, ⊤) := by
  let _ : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso K).inv ≫ q.appTop).hom.toAlgebra
  let _ : Algebra K Γ(W, ⊤) :=
    ((Scheme.ΓSpecIso K).inv ≫ (e.hom ≫ q).appTop).hom.toAlgebra
  let : IsIso e.hom.appTop := (Scheme.Γ.mapIso e.op).isIso_hom
  refine { (asIso e.hom.appTop).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro r
  change e.hom.appTop (q.appTop ((Scheme.ΓSpecIso K).inv r)) =
    (e.hom ≫ q).appTop ((Scheme.ΓSpecIso K).inv r)
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop e.hom q)
    ((Scheme.ΓSpecIso K).inv r)).symm

/-- The SAME actual finite-field sheaf trace preserves every original
section under the actual WHOLE scheme isomorphism and original composite. -/
theorem fieldStructureTrace_iso_top (K : CommRingCat.{u}) (hK : IsField K)
    {W Z : Scheme.{u}} (q : Z ⟶ Spec K) [IsFinite q] (e : W ≅ Z) (b : Γ(Z, ⊤)) :
    (Scheme.ΓSpecIso K).hom
        ((fieldStructureTrace K hK (e.hom ≫ q)).app ⊤ (e.hom.appTop b)) =
      (Scheme.ΓSpecIso K).hom ((fieldStructureTrace K hK q).app ⊤ b) := by
  let _ : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso K).inv ≫ q.appTop).hom.toAlgebra
  let _ : Algebra K Γ(W, ⊤) :=
    ((Scheme.ΓSpecIso K).inv ≫ (e.hom ≫ q).appTop).hom.toAlgebra
  have hi := Algebra.trace_eq_of_algEquiv (actualSectionsIso K q e) b
  exact (fieldStructureTrace_top K hK (e.hom ≫ q) (e.hom.appTop b)).trans
    (hi.trans (fieldStructureTrace_top K hK q b).symm)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
