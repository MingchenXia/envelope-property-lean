/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Source.Unibranch
import EnvelopeProperty.AlgGeom.OriginalProjectiveFamilyChartAlgebras
import EnvelopeProperty.AlgGeom.ProjectiveNativeCoordinateChartSupport

/-!
# Unibranchness of a variety and of the model of a presentation

Let `X` be an integral scheme over a field `k` with a *presentation*: morphisms
`q_c : X → ℙ^{d_c}` over `p : X → Spec k`, `c = 0, …, r`, with `q_0` a closed immersion. Its
multiprojective model `𝒫 = FiniteProjectiveNativeFieldModels.model q p hp` (a
`MultiModel k K(X) (r + 1)`) has the chart algebras `A_j ⊆ K(X)`, `j = (j_0, …, j_r)`, and
`A_j ≅ Γ(X, U_j)` for the simultaneous coordinate chart `U_j = ⋂_c q_c⁻¹(D₊(x^{(c)}_{j_c}))`
whenever all `U_j` are nonempty (`OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv`).

The main result is `Variety.isUnibranch_iff_presentation` (`thm:var-unibranch-presentation`):
over an algebraically closed `k`, `X` is unibranch in the sense of FHX §1.1 (its normalization is
bijective, `Variety.IsUnibranch`) iff `𝒫` is unibranch in the sense of `def:gl-unibranch`
(`MultiModel.IsUnibranch`). This is the bridge between the source hypothesis "X unibranch" of FHX
`thm:intro-main` / `cor:intro-characterization` and the hypothesis of the model theorems
(`MultiModel.hasEnvelopeProperty_of_isUnibranch_of_forall_countable`,
`MultiModel.isUnibranch_of_exists_hasEnvelopeProperty`).

## Proof

Both sides are stalk-wise conditions:
* `X` is unibranch iff all stalks `𝒪_{X,x}` are unibranch
  (`Variety.isUnibranch_iff_isUnibranchLocalRing_stalk`), iff all localizations of `Γ(X, U)` at
  primes are unibranch for all nonempty affine `U` (`Variety.isUnibranch_iff_forall_affine`);
* `𝒫` is unibranch iff every localization of every chart algebra `A_j` with all coordinates
  `x^{(c)}_{j_c} ≠ 0` at a prime is unibranch (`MultiModel.isUnibranch_tfae`, `k` algebraically
  closed).

A coordinate `x^{(c)}_{j_c}` of `𝒫` is nonzero iff `q_c⁻¹(D₊(x^{(c)}_{j_c}))` is nonempty
(`ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty`). For such `j` the
chart `U_j` is affine (the preimage of a standard affine open under the closed immersion given by
the Segre embedding of the presentation), nonempty, and `A_j ≅ Γ(X, U_j)`; unibranchness of the
localizations transfers along this ring isomorphism. Conversely every point `x` of `X` lies in
some `U_j` (choose `j_c` with `q_c(x) ∈ D₊(x^{(c)}_{j_c})`), and `𝒪_{X,x}` is a localization of
`Γ(X, U_j)`.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open Alterations

universe u

noncomputable section

namespace EnvelopeProperty.Variety

/-! ### Unibranch localizations along ring isomorphisms -/

/-- If all localizations of `A` at primes are unibranch, so are those of any ring `B ≅ A`: the
localization of `B` at `𝔓` is that of `A` at the corresponding prime. -/
theorem forall_isUnibranchLocalRing_atPrime_of_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] (e : A ≃+* B)
    (h : ∀ P : PrimeSpectrum A, IsUnibranchLocalRing (Localization.AtPrime P.asIdeal))
    (P : PrimeSpectrum B) : IsUnibranchLocalRing (Localization.AtPrime P.asIdeal) := by
  let P' : PrimeSpectrum A := PrimeSpectrum.comap (e : A →+* B) P
  have H : P'.asIdeal.primeCompl.map e.toMonoidHom = P.asIdeal.primeCompl := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hb
      refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
      show e (e.symm b) ∉ P.asIdeal
      rwa [e.apply_symm_apply]
  have := h P'
  exact .of_ringEquiv (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P'.asIdeal)
    (Localization.AtPrime P.asIdeal) e H)

/-- Unibranchness of all localizations at primes is invariant under ring isomorphisms. -/
theorem forall_isUnibranchLocalRing_atPrime_iff_of_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] (e : A ≃+* B) :
    (∀ P : PrimeSpectrum A, IsUnibranchLocalRing (Localization.AtPrime P.asIdeal)) ↔
      ∀ P : PrimeSpectrum B, IsUnibranchLocalRing (Localization.AtPrime P.asIdeal) :=
  ⟨forall_isUnibranchLocalRing_atPrime_of_ringEquiv e,
    forall_isUnibranchLocalRing_atPrime_of_ringEquiv e.symm⟩

/-! ### The model of a presentation -/

section Presentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {r : ℕ} {d : Fin (r + 1) → ℕ}
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p) [IsClosedImmersion (q 0)]

/-- A coordinate `x^{(c)}_i` of the model of a presentation is nonzero iff the chart
`q_c⁻¹(D₊(x^{(c)}_i))` is nonempty (for any base `b` of the presentation). -/
theorem model_coord_ne_zero_iff (b : X ⟶ Spec (.of k))
    (hb : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b) (c : Fin (r + 1))
    (i : Fin (d c + 1)) :
    letI := b.stalkAlgebra (genericPoint X)
    (FiniteProjectiveNativeFieldModels.model q b hb).coord c i ≠ 0 ↔
      Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) i) := by
  let := b.stalkAlgebra (genericPoint X)
  let : Nonempty (q c ⁻¹ᵁ
      coordinateOpen (R := k) (FiniteProjectiveNativeFieldModels.pivot q c)) :=
    (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
  exact ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty (q c)
    (FiniteProjectiveNativeFieldModels.pivot q c) i

omit [IsIntegral X] [IsClosedImmersion (q 0)] in
/-- Every point of `X` lies in a simultaneous coordinate chart of the presentation. -/
theorem exists_chartIndex_mem (x : X) :
    ∃ j : ∀ c, Fin (d c + 1), ∀ c, q c x ∈ coordinateOpen (R := k) (j c) := by
  have hc : ∀ c, ∃ i : Fin (d c + 1), q c x ∈ coordinateOpen (R := k) i := fun c => by
    have hcover : q c x ∈ ⨆ i : Fin (d c + 1), coordinateOpen (R := k) i := by
      rw [iSup_coordinateOpen_eq_top]
      trivial
    exact Opens.mem_iSup.mp hcover
  exact ⟨fun c => (hc c).choose, fun c => (hc c).choose_spec⟩

/-- **Unibranch transfer, for the Segre base of a presentation** (`b` is the structure morphism
`X → ℙ^N → Spec k` through the Segre embedding of the presentation, which equals `p`). -/
theorem isUnibranch_iff_presentation_of_eq [IsAlgClosed k] (b : X ⟶ Spec (.of k))
    (hb : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = b)
    (hbp : FiniteSegreOriginalProjectiveMaps.morphism d q p hp ≫
      projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d) = b) :
    letI := b.stalkAlgebra (genericPoint X)
    IsUnibranch X ↔ (FiniteProjectiveNativeFieldModels.model q b hb).IsUnibranch := by
  subst hbp
  let := (FiniteSegreOriginalProjectiveMaps.morphism d q p hp ≫
    projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)).stalkAlgebra
      (genericPoint X)
  have : IsClosedImmersion (FiniteSegreOriginalProjectiveMaps.morphism d q p hp) :=
    FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  have key :=
    (MultiModel.isUnibranch_tfae (X := FiniteProjectiveNativeFieldModels.model q _ hb)).out 0 1
  refine Iff.trans ?_ key.symm
  constructor
  · intro hX j hj
    have hJ : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := fun c =>
      (model_coord_ne_zero_iff q _ hb c (j c)).mp (hj c)
    have hU : IsAffineOpen (FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
        coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)) :=
      (coordinateOpen_isAffineOpen _).preimage _
    have := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
    let := (FiniteSegreOriginalProjectiveMaps.morphism d q p hp ≫
      projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)).sectionsAlgebra
        (FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
          coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
    exact forall_isUnibranchLocalRing_atPrime_of_ringEquiv
      (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hJ).toRingEquiv
      (isUnibranch_iff_forall_affine.mp hX _ hU)
  · intro h
    refine isUnibranch_iff_isUnibranchLocalRing_stalk.mpr fun x => ?_
    obtain ⟨j, hj⟩ := exists_chartIndex_mem q x
    have hJ : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := fun c => ⟨⟨x, hj c⟩⟩
    have hx : x ∈ FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
        coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j) := by
      rw [OriginalProjectiveFamilyChartAlgebras.morphism_preimage_coordinateOpen d q p hp j]
      have hmem : x ∈ ((⨅ c, q c ⁻¹ᵁ coordinateOpen (R := k) (j c) : X.Opens) : Set X) := by
        rw [Opens.coe_iInf]
        exact Set.mem_iInter.mpr fun c => hj c
      exact hmem
    have hU : IsAffineOpen (FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
        coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)) :=
      (coordinateOpen_isAffineOpen _).preimage _
    have := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
    let := (FiniteSegreOriginalProjectiveMaps.morphism d q p hp ≫
      projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)).sectionsAlgebra
        (FiniteSegreOriginalProjectiveMaps.morphism d q p hp ⁻¹ᵁ
          coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j))
    have hloc := forall_isUnibranchLocalRing_atPrime_of_ringEquiv
      (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hJ).toRingEquiv.symm
      (h j fun c => (model_coord_ne_zero_iff q _ hb c (j c)).mpr (hJ c))
    obtain ⟨P, rfl⟩ : ∃ P : PrimeSpectrum Γ(X, FiniteSegreOriginalProjectiveMaps.morphism d q p hp
        ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)),
        hU.fromSpec P = x :=
      ⟨_, hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩
    exact (isUnibranchLocalRing_stalk_fromSpec_iff hU P).mpr (hloc P)

/-- **Unibranch transfer to the model of a presentation** (`thm:var-unibranch-presentation`).
Let `k` be algebraically closed and `q_c : X → ℙ^{d_c}` (`c = 0, …, r`) morphisms over
`p : X → Spec k` with `q_0` a closed immersion. Then `X` is unibranch (its normalization is
bijective, FHX §1.1) iff the multiprojective model `𝒫` of the presentation is unibranch
(`def:gl-unibranch`). -/
theorem isUnibranch_iff_presentation [IsAlgClosed k] :
    letI := p.stalkAlgebra (genericPoint X)
    IsUnibranch X ↔ (FiniteProjectiveNativeFieldModels.model q p hp).IsUnibranch :=
  isUnibranch_iff_presentation_of_eq q p hp p hp
    (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp)

end Presentation

end EnvelopeProperty.Variety
