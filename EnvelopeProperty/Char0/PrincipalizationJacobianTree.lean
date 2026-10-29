/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCJacobianCover
import EnvelopeProperty.Char0.ReesCoverRefinement
import EnvelopeProperty.Char0.AffinePrincipalization
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification

/-!
# Actual principalization trees subordinate to genuine Jacobian neighborhoods

The BP sequence itself, its SNC transform, the actual neighborhood cover and
the literal Rees inclusion triangles are produced together.
-/

noncomputable section

namespace EnvelopeProperty.Char0

open AlgebraicGeometry CategoryTheory
open scoped Classical

universe u

variable {k K : Type u} [Field k] [CharZero k] [Field K] [Algebra k K]

/-- Literal SNC, actual leaf-map, coverage, triangle and Jacobian-neighborhood data.
This existential proposition is an output of the actual producer, not an assumption class. -/
def SNCJacobianReesCover (C : Subalgebra k K) {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of C)) (n : ℕ) (J : (Spec (.of C)).IdealSheafData) : Prop :=
  ∃ (F : Scheme.DivisorFamily Y) (e : F.ι → ℕ), F.IsSnc ∧
    J.comap π = ∏ i, F.component i ^ e i ∧
        ∃ (T : ReesChartTree k K C)
          (φ : (i : T.LeafIndex) → Spec (.of (T.leafAlgebra i)) ⟶ Y),
          (∀ i, IsOpenImmersion (φ i)) ∧
          (∀ i, φ i ≫ π =
            subalgebraSpecMap (T.root_le_of_mem_leaves (T.leafAlgebra_mem_leaves i))) ∧
          (∀ y : Y, ∃ (i : T.LeafIndex) (x : Spec (.of (T.leafAlgebra i))), φ i x = y) ∧
          (∀ i : T.LeafIndex, ∃ (x : Y) (W : Y.affineOpens),
            IsClosed ({x} : Set Y) ∧ SNCJacobianNeighbourhood (k := k) π F n J x W ∧
            Set.range (φ i) ⊆ (W.1 : Set Y))

/-- Actual SNC total transform geometry and an actual blowup sequence produce the literal
finite leaf cover, subordinate to a genuine finite Jacobian neighborhood cover. -/
theorem exists_snc_jacobian_rees_cover (C : Subalgebra k K) (hC : C.FG)
    (S : Scheme.BlowUpSequence (Spec (.of C))) (n : ℕ) [CompactSpace S.last]
    [SmoothOfRelativeDimension n
      (S.composite ≫ Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (J : (Spec (.of C)).IdealSheafData) [IsIso (S.composite ∣_ J.support.compl)]
    (hJ : (J.comap S.composite).IsIdealOfSncDivisor)
    (hV : (J.support.compl : Set (Spec (.of C))).Nonempty)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    SNCJacobianReesCover C S.composite n J := by
  obtain ⟨F, e, hF, htotal⟩ := hJ
  obtain ⟨t, hcover, hcharts⟩ := @exists_finite_snc_jacobian_neighbourhood_cover
    k C _ _ _ S.last n _ _ S.composite inferInstance J inferInstance F hF e htotal z hz
  let U : t → S.last.Opens := fun W => W.1.1
  have hU : ∀ y : S.last, ∃ W, y ∈ U W := by
    intro y
    obtain ⟨W, hWt, hyW⟩ := hcover y
    exact ⟨⟨W, hWt⟩, hyW⟩
  obtain ⟨T, φ, hopen, htriangle, hφcover, hsub⟩ := @exists_actual_rees_cover_subordinate
    k K _ _ _ _ C hC S J.support.compl hV inferInstance _ U hU
  refine ⟨F, e, hF, htotal, T, φ, hopen, htriangle, hφcover, ?_⟩
  intro i
  obtain ⟨W, hW⟩ := hsub i
  obtain ⟨x, hx, hdata⟩ := hcharts W W.2
  exact ⟨x, W.1, hx, hdata, hW⟩

/-- The literal geometric data above is produced for the actual BP sequence itself, with
the nonempty isomorphism open and final compactness derived internally. -/
theorem exists_affinePrincipalization_jacobian_rees_cover
    (C : Subalgebra k K) (hC : C.FG) (n : ℕ)
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k C)))]
    (I : Ideal C) (hI : I ≠ ⊥)
    (z : Fin n → C) (hz : (MvPolynomial.aeval (R := k) z).toRingHom.Etale) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
    ∃ S : Scheme.BlowUpSequence (Spec (.of C)),
      S = Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI) ∧
      SmoothOfRelativeDimension n (S.composite ≫ f) ∧
      SNCJacobianReesCover C S.composite n (specIdealSheaf I) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k C))
  let S := Hironaka.Sequence.BP (affinePrincipalizationTriple f n I hI)
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hbase : IsNoetherian (Spec (.of C)) := f.isNoetherian_of_field
  have hfinal : IsNoetherian S.last := @Hironaka.Resolution.isNoetherian_stage
    (Spec (.of C)) hbase S (Fin.last _)
  have hsm : SmoothOfRelativeDimension n (S.composite ≫ f) :=
    affinePrincipalization_smoothOfRelativeDimension f n I hI
  have hiso : IsIso (S.composite ∣_ (specIdealSheaf I).support.compl) :=
    affinePrincipalization_isIso_restrict f n I hI
  exact ⟨S, rfl, hsm, @exists_snc_jacobian_rees_cover
    k K _ _ _ _ C hC S n hfinal.toCompactSpace hsm (specIdealSheaf I) hiso
      (affinePrincipalization_isIdealOfSncDivisor f n I hI)
      (nonempty_compl_support_specIdealSheaf I hI) z hz⟩

end EnvelopeProperty.Char0
