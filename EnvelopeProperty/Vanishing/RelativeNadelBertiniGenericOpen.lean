import EnvelopeProperty.AlgGeom.FinitePresentationGenericAvoidance
import EnvelopeProperty.Vanishing.NadelBertiniGenericOpen
import EnvelopeProperty.Vanishing.NadelBertiniFibreSmooth

/-! # Actual smooth Bertini parameter opens without field properness

The entire nonsmooth image is shrunk away by Chevalley's theorem.  The
parameter map need only be quasi-compact and locally of finite presentation;
the original total scheme need only be Noetherian and regular.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelBertiniGenericOpen
variable {X S : Scheme.{u}}

/-- The complement of the closure of the actual whole nonsmooth image. -/
def goodOpen (f : X ⟶ S) [LocallyOfFinitePresentation f] : S.Opens :=
  FinitePresentationGenericAvoidance.avoidingOpen f (f.smoothLocus : Set X)ᶜ

/-- Every point over the actual open belongs to the original smooth locus. -/
theorem goodOpen_preimage_le (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    f ⁻¹ᵁ goodOpen f ≤ f.smoothLocus := by
  intro x hx
  exact Classical.not_not.mp
    (FinitePresentationGenericAvoidance.preimage_avoidingOpen_le_compl f
      (f.smoothLocus : Set X)ᶜ hx)

/-- The whole actual restriction is smooth. -/
theorem goodOpen_smooth (f : X ⟶ S) [LocallyOfFinitePresentation f] :
    Smooth (f ∣_ goodOpen f) :=
  NadelBertiniGenericOpen.smooth_morphismRestrict_of_preimage_le_smoothLocus
    f _ (goodOpen_preimage_le f)

/-- Original regularity and characteristic zero place the generic point in
the actual Chevalley open; properness of the family is unnecessary. -/
theorem genericPoint_mem_goodOpen {k : Type u} [Field k] [CharZero k]
    [IsIntegral S] [IsAffine S] [NoetherianSpace X] [IsRegular X]
    (p : S ⟶ Spec (.of k)) (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] :
    genericPoint S ∈ goodOpen f := by
  let := NadelBertiniGenericSmooth.genericFiber_smooth p f
  apply FinitePresentationGenericAvoidance.genericPoint_mem_avoidingOpen f
    (f.smoothLocus : Set X)ᶜ
    (FinitePresentationGenericAvoidance.isLocallyConstructible_of_isClosed _
      f.smoothLocus.isOpen.isClosed_compl)
  rintro ⟨x, hx, hη⟩
  exact hx (NadelBertiniGenericOpen.genericFiber_le_smoothLocus f x hη)

/-- The original geometry produces the nonempty dense open and smoothness of
its entire preimage, with no supplied generic smoothness or chosen open. -/
theorem goodOpen_specification {k : Type u} [Field k] [CharZero k]
    [IsIntegral S] [IsAffine S] [NoetherianSpace X] [IsRegular X]
    (p : S ⟶ Spec (.of k)) (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] :
    genericPoint S ∈ goodOpen f ∧ Nonempty (goodOpen f) ∧
      Dense (goodOpen f : Set S) ∧ f ⁻¹ᵁ goodOpen f ≤ f.smoothLocus ∧
      Smooth (f ∣_ goodOpen f) := by
  have hη := genericPoint_mem_goodOpen p f
  exact ⟨hη, ⟨⟨genericPoint S, hη⟩⟩,
    (goodOpen f).isOpen.dense ⟨genericPoint S, hη⟩,
    goodOpen_preimage_le f, goodOpen_smooth f⟩

/-- Smoothness over the original field supplies the original regularity. -/
theorem goodOpen_specification_of_smooth {k : Type u} [Field k] [CharZero k]
    [IsIntegral S] [IsAffine S] [NoetherianSpace X]
    (p : S ⟶ Spec (.of k)) (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    (pX : X ⟶ Spec (.of k)) [Smooth pX] :
    genericPoint S ∈ goodOpen f ∧ Nonempty (goodOpen f) ∧
      Dense (goodOpen f : Set S) ∧ f ⁻¹ᵁ goodOpen f ≤ f.smoothLocus ∧
      Smooth (f ∣_ goodOpen f) := by
  let : IsRegular X := (Scheme.smooth_iff_isRegular pX).mp inferInstance
  exact goodOpen_specification p f

/-- Actual rational parameters in the open give smooth whole selected zero
schemes for any original line and section system. -/
theorem selected_smooth {k : Type u} [Field k] {m : ℕ}
    (p : X ⟶ Spec (.of k)) (a : Fin (m + 1) → k)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (s : Fin (m + 1) → Γ(L, ⊤))
    [LocallyOfFinitePresentation (NadelBertiniUniversal.toParameters p L hL s)]
    (ha : ∀ t, NadelBertiniRationalParameter.parameterMap a t ∈
      goodOpen (NadelBertiniUniversal.toParameters p L hL s)) :
    Smooth ((NadelBertiniFibreGeometry.selectedIdeal p a L hL s).subschemeι ≫ p) := by
  let := goodOpen_smooth (NadelBertiniUniversal.toParameters p L hL s)
  exact NadelBertiniFibreSmooth.selected_smooth_of_mapsTo_open p a L hL s _ ha

end EnvelopeProperty.Vanishing.RelativeNadelBertiniGenericOpen
