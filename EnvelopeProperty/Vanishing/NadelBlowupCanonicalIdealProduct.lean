import EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductPullback
import EnvelopeProperty.AlgGeom.CartierAdmissibleModulePullback

/-! # The actual WHOLE tensor product of an arbitrary original Cartier ideal and ANY original ideal -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProduct
open NadelBlowupCanonicalIdealProductFrame NadelBlowupCanonicalIdealProductPullback
open NadelBlowupCanonicalGluingDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Original Cartier invertibility INTERNALLY constructs the actual
WHOLE tensor/product isomorphism with its ENTIRE SAME multiplication inclusion.
The second original geometric ideal is arbitrary; no expected comparison,
local frame, covering, domain or Noetherianity certificate is supplied. -/
theorem exists_tensorProductIso {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible)
    (J : X.IdealSheafData) :
    ∃ e : tensorObj I.toModules J.toModules ≅ (I * J).toModules,
      e.hom ≫ (I * J).toModulesInclusion = multiplicationIntoUnit I J := by
  classical
  have hCartier : I.IsInvertible := hI
  choose U hx a ha hgen using hCartier
  let Y (x : X) : Scheme.{u} := Spec Γ(X, U x)
  let q (x : X) : Y x ⟶ X := (U x).2.fromSpec
  let : ∀ x, IsOpenImmersion (q x) := fun x => inferInstanceAs (IsOpenImmersion (U x).2.fromSpec)
  have hcover : ∀ x : X, ∃ (i : X) (y : Y i), q i y = x := by
    intro x
    refine ⟨x, ?_⟩
    change x ∈ (q x).opensRange
    rw [show (q x).opensRange = (U x).1 from (U x).2.opensRange_fromSpec]
    exact hx x
  apply exists_iso_of_local_factors Y q hcover (I * J).toModulesInclusion (multiplicationIntoUnit I J)
  intro x
  let r : Γ(Y x, ⊤) := (Scheme.ΓSpecIso Γ(X, U x)).inv.hom (a x)
  have hIq : (I.comap (q x)).ideal ⟨⊤, isAffineOpen_top (Y x)⟩ = Ideal.span {r} := by
    rw [show q x = (U x).2.fromSpec from rfl, Scheme.IdealSheafData.comap_fromSpec,
      AlgebraicGeometry.ofIdealTop_ideal_top, hgen x, Ideal.map_span, Set.image_singleton]
  have hr : r ∈ nonZeroDivisors Γ(Y x, ⊤) :=
    (hI.comap_of_flat (q x)).generator_mem_nonZeroDivisors ⟨⊤, isAffineOpen_top (Y x)⟩ r hIq
  exact factor_pullback_of_local_factor (q x) I J
    (exists_affine_product_factor (I.comap (q x)) (J.comap (q x)) r hr hIq)

/-- The actual product isomorphism is chosen from its proved original
geometric producer, retaining the SAME original ideal product. -/
def tensorProductIso {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible)
    (J : X.IdealSheafData) : tensorObj I.toModules J.toModules ≅ (I * J).toModules :=
  Classical.choose (exists_tensorProductIso I hI J)

/-- This actual whole comparison retains the ENTIRE original product ideal inclusion. -/
theorem tensorProductIso_inclusion {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.IsInvertible)
    (J : X.IdealSheafData) :
    (tensorProductIso I hI J).hom ≫ (I * J).toModulesInclusion = multiplicationIntoUnit I J :=
  Classical.choose_spec (exists_tensorProductIso I hI J)

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProduct
