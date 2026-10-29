import EnvelopeProperty.AffineGlobalSections
import EnvelopeProperty.Vanishing.NadelKummerTraceBaseChangeUniquenessCore
import Mathlib.RingTheory.Trace.Basic

/-! # Native trace on the actual whole affine scheme base change

Only the displayed original free chart is assumed free. Actual finiteness
provides its finite module structure internally. The section tensor
comparison retains the genuine original first projection on every element.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory
open FlatGlobalSections
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ Spec (.of R)) [IsFinite p]

/-- The actual first projection preserves native trace on EVERY original
section of a genuinely free chart, including all disconnected factors. -/
theorem affine_trace_baseChange
    (hfree : let _ := sectionsAlgebra p; Module.Free R Γ(Y, ⊤)) (b : Γ(Y, ⊤)) :
    let _ := sectionsAlgebra p
    let _ := sectionsAlgebra (structureMap (S := S) p)
    Algebra.trace S Γ(baseChange (S := S) p, ⊤)
        ((firstProjection (S := S) p).appTop b) =
      algebraMap R S (Algebra.trace R Γ(Y, ⊤) b) := by
  let _ := sectionsAlgebra p
  let _ := sectionsAlgebra (structureMap (S := S) p)
  let : Module.Free R Γ(Y, ⊤) := hfree
  let : Module.Finite R Γ(Y, ⊤) := p.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).surjective)
  let e := AffineGlobalSections.tensorEquiv (S := S) p
  have hi : e ((1 : S) ⊗ₜ[R] b) = (firstProjection (S := S) p).appTop b :=
    AffineGlobalSections.tensorEquiv_includeRight (S := S) p b
  have he := Algebra.trace_eq_of_algEquiv e ((1 : S) ⊗ₜ[R] b)
  have ht := NadelKummerTraceBaseChangeUniqueness.trace_one_tmul
    (A := R) (B := Γ(Y, ⊤)) (S := S) b
  exact (congrArg (Algebra.trace S Γ(baseChange (S := S) p, ⊤)) hi).symm.trans
    (he.trans ht)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
