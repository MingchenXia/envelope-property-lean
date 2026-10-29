module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Topology.Sober

/-!
# The actual reduced closure of an original point

The ideal sheaf and its subscheme remain the native vanishing ideal of the
original singleton closure. The generic point is the original subtype point;
no selected integral component or comparison datum enters these producers.
-/

public section

universe u
open AlgebraicGeometry Topology

namespace EnvelopeProperty.SchemePointClosureIntegral

/-- The actual subscheme of a native vanishing ideal is reduced. -/
theorem isReduced_vanishingIdeal_subscheme {X : Scheme.{u}}
    (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  refine @IsReduced.of_openCover _ I.subschemeCover.openCover ?_
  intro U
  let V : X.affineOpens := U
  have hr : (I.ideal V).IsRadical := by
    dsimp only [I]
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  let : _root_.IsReduced (Γ(X, V.1) ⧸ I.ideal V) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hr
  change IsReduced (Spec (.of (Γ(X, V.1) ⧸ I.ideal V)))
  infer_instance

/-- The canonical original subtype point on the literal reduced point closure. -/
@[expose] noncomputable def pointClosureLift {X : Scheme.{u}} (eta : X) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme :=
  ⟨eta, by
    change eta ∈ (↑(Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change eta ∈ closure ({eta} : Set X)
    exact subset_closure (Set.mem_singleton eta)⟩

/-- The native inclusion sends the canonical lift to the same original point. -/
theorem pointClosureLift_image {X : Scheme.{u}} (eta : X) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subschemeι
        (pointClosureLift eta) = eta := rfl

/-- The same canonical lift is generic in the whole literal reduced point closure. -/
theorem isGenericPoint_pointClosureLift {X : Scheme.{u}} (eta : X) :
    IsGenericPoint (pointClosureLift eta)
      (Set.univ : Set (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme) := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
  let z : I.support := pointClosureLift eta
  have hz : IsGenericPoint z (Set.univ : Set I.support) := by
    change closure ({z} : Set I.support) = Set.univ
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
    apply Set.eq_univ_of_forall
    intro y
    change y.val ∈ closure ({eta} : Set X)
    have hs : (↑I.support : Set X) = closure ({eta} : Set X) :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal _
    have hy : y.val ∈ (↑I.support : Set X) := y.property
    exact Eq.mp (congrArg (fun S : Set X => y.val ∈ S) hs) hy
  exact hz

/-- The actual native reduced closure of any original point is integral. -/
theorem isIntegral_pointClosure {X : Scheme.{u}} (eta : X) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme := by
  let := isReduced_vanishingIdeal_subscheme
    (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)
  let : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).subscheme :=
    (irreducibleSpace_def _).mpr (isGenericPoint_pointClosureLift eta).isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end EnvelopeProperty.SchemePointClosureIntegral
