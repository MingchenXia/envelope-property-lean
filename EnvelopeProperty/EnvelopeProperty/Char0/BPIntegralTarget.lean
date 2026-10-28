import EnvelopeProperty.Char0.AffinePrincipalization
import EnvelopeProperty.AlgGeom.ProjectiveStrongResolution

/-! # The SAME original BP target is genuinely integral -/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EnvelopeProperty.Char0
universe u
variable {k R : Type u} [Field k] [CharZero k] [CommRing R] [IsDomain R]

/-- The SAME actual principalization target is nonempty, derived from its
actual isomorphism off the original nonzero ideal. -/
theorem affinePrincipalization_nonempty_last
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    Nonempty (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last := by
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let U := (specIdealSheaf I).support.compl
  let : IsIso (S.composite ∣_ U) := affinePrincipalization_isIso_restrict f n I hI
  have hU : Nonempty U := Set.nonempty_coe_sort.mpr
    (nonempty_compl_support_specIdealSheaf I hI)
  let : Nonempty (S.composite ⁻¹ᵁ U) := Nonempty.map (inv (S.composite ∣_ U)) hU
  exact Nonempty.map (S.composite ⁻¹ᵁ U).ι inferInstance

/-- Integral original affine geometry and actual blowup integrality give
integrality of the SAME original BP final scheme, with no supplied target premise. -/
theorem affinePrincipalization_isIntegral_last
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    IsIntegral (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last := by
  let : Nonempty (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last :=
    affinePrincipalization_nonempty_last f n I hI
  let : IsIntegral (affinePrincipalizationTriple f n I hI).X.left := by
    change IsIntegral (Spec (.of R))
    infer_instance
  exact ProjectiveStrongResolution.isIntegral_last _

end EnvelopeProperty.Char0
