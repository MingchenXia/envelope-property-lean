import EnvelopeProperty.Char0.BPIntegralTarget
import EnvelopeProperty.Char0.CanonicalDifferentialNonzero

/-! # The SAME original BP canonical differential is genuinely nonzero -/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EnvelopeProperty.Char0
universe u
variable {k R : Type u} [Field k] [CharZero k] [CommRing R] [IsDomain R]

private theorem originalBPCanonicalOpenChart
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
    ∃ (Z : Scheme.{u}) (h : Z ⟶ S.last),
      Nonempty Z ∧ IsOpenImmersion h ∧ IsOpenImmersion (h ≫ S.composite) := by
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  let U : (Spec (.of R)).Opens := (specIdealSheaf I).support.compl
  let : IsIso (S.composite ∣_ U) := affinePrincipalization_isIso_restrict f n I hI
  have hU : Nonempty U := Set.nonempty_coe_sort.mpr
    (nonempty_compl_support_specIdealSheaf I hI)
  have hZ : Nonempty (S.composite ⁻¹ᵁ U) := Nonempty.map (inv (S.composite ∣_ U)) hU
  have htriangle : (S.composite ⁻¹ᵁ U).ι ≫ S.composite = (S.composite ∣_ U) ≫ U.ι :=
    (morphismRestrict_ι S.composite U).symm
  refine ⟨(S.composite ⁻¹ᵁ U).toScheme, (S.composite ⁻¹ᵁ U).ι, hZ, inferInstance, ?_⟩
  rw [htriangle]
  exact @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso _)
    (inferInstanceAs (IsOpenImmersion ((Spec (.of R)).ofRestrict U.isOpenEmbedding)))

/-- The literal original BP exterior differential is nonzero, derived from
its actual original nonempty isomorphism open, with no extra map premise. -/
theorem affinePrincipalization_exteriorDifferential_ne_zero
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    CanonicalGeometry.exteriorCotangentSheafPullbackMap f
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n ≠ 0 := by
  obtain ⟨Z, h, hZ, hh, hg⟩ := originalBPCanonicalOpenChart f n I hI
  let : Nonempty Z := hZ
  let : IsOpenImmersion h := hh
  let : IsOpenImmersion (h ≫
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite) := hg
  exact @RoundedCanonicalModule.exteriorCotangentSheafPullbackMap_ne_zero_of_open
    k _ _ _ Z f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite h n
    _ hZ hh hg

/-- The actual global section of the SAME original BP relative canonical
line is nonzero; its true generic coefficient can therefore be normalized
without any additional main-paper assumption. -/
theorem affinePrincipalization_differentialGlobalSection_ne_zero
    (f : Spec (.of R) ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : Ideal R) (hI : I ≠ ⊥) :
    (RoundedCanonicalModule.differentialSection f
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite n).val.app
        (.op ⊤) (show Γ((Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).last, ⊤)
          from 1) ≠ 0 := by
  obtain ⟨Z, h, hZ, hh, hg⟩ := originalBPCanonicalOpenChart f n I hI
  let : Nonempty Z := hZ
  let : IsOpenImmersion h := hh
  let : IsOpenImmersion (h ≫
      (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite) := hg
  exact @RoundedCanonicalModule.differentialGlobalSection_ne_zero_of_open
    k _ _ _ Z f (Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)).composite h n
    _ hZ hh hg

end EnvelopeProperty.Char0
