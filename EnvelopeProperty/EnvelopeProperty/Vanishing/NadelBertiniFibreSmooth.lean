import EnvelopeProperty.Vanishing.NadelBertiniFibreGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import EnvelopeProperty.Vanishing.NadelBertiniGlobalSmooth
import EnvelopeProperty.Vanishing.NadelBertiniRationalParameterIncidence
/-! # Actual good parameters produce smooth entire selected hypersurface subschemes -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniFibreSmooth
open NadelBertiniUniversal NadelBertiniFibreGeometry NadelBertiniRationalParameter

theorem fibre_smooth_of_mapsTo_open {Y V S : Scheme.{u}} (f : Y ⟶ V) (g : S ⟶ V)
    (U : V.Opens) (hg : ∀ x, g x ∈ U) [Smooth (f ∣_ U)] :
    Smooth (pullback.snd f g) := by
  let VY := f ⁻¹ᵁ U
  have hgRange : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hg x
  let h := IsOpenImmersion.lift U.ι g hgRange
  have hh : h ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hfRange : Set.range (pullback.fst f g) ⊆ Set.range VY.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change f ((pullback.fst f g) x) ∈ U
    have he := congrArg (fun z => z x) (pullback.condition (f := f) (g := g))
    exact he.symm ▸ hg ((pullback.snd f g) x)
  let l := IsOpenImmersion.lift VY.ι (pullback.fst f g) hfRange
  have hl : l ≫ VY.ι = pullback.fst f g := IsOpenImmersion.lift_fac _ _ _
  have hw : l ≫ f ∣_ U = pullback.snd f g ≫ h := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl,
      Category.assoc, hh]
    exact pullback.condition
  have H : IsPullback (l ≫ VY.ι) (pullback.snd f g) f (h ≫ U.ι) := by
    rw [hl, hh]
    exact IsPullback.of_hasPullback f g
  have H' := H.of_right hw (isPullback_morphismRestrict f U).flip
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback H' (inferInstanceAs (Smooth (f ∣_ U)))

theorem selected_smooth_of_mapsTo_open {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (a : Fin (m + 1) → k) (L : X.Modules) (hL : IsInvertible L)
    (s : Fin (m + 1) → Γ(L, ⊤)) (U : (Spec (.of (parameterRing k m))).Opens)
    (ha : ∀ x, parameterMap a x ∈ U) [Smooth ((toParameters p L hL s) ∣_ U)] :
    Smooth ((selectedIdeal p a L hL s).subschemeι ≫ p) := by
  have := fibre_smooth_of_mapsTo_open (toParameters p L hL s) (parameterMap a) U ha
  rw [← selectedFibreIso_base p a L hL s]
  infer_instance
abbrev projectiveSelectedIdeal {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) (a : Fin (m + 1) → k) : X.IdealSheafData :=
  selectedIdeal (j ≫ DeJongAlterations.projectiveSpaceStructure k m) a (projectiveLine j)
    ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) 1).pullback j)
    (projectiveSections j)

theorem projective_selected_smooth {k : Type u} [Field k] [CharZero k] {m : ℕ} {X : Scheme.{u}}
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m)] (a : Fin (m + 1) → k)
    (ha : ∀ x, parameterMap a x ∈ NadelBertiniGenericIncidence.projectiveGoodOpen j) :
    Smooth ((projectiveSelectedIdeal j a).subschemeι ≫ j ≫ DeJongAlterations.projectiveSpaceStructure k m) := by
  have := NadelBertiniGlobalSmooth.projectiveTotal_smooth j
  obtain ⟨_, _, _, _, hs⟩ := NadelBertiniGenericIncidence.projectiveGoodOpen_specification j
  have : Smooth ((toParameters (j ≫ DeJongAlterations.projectiveSpaceStructure k m)
      (projectiveLine j) ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) 1).pullback j)
      (projectiveSections j)) ∣_ NadelBertiniGenericIncidence.projectiveGoodOpen j) := hs
  exact selected_smooth_of_mapsTo_open (j ≫ DeJongAlterations.projectiveSpaceStructure k m) a
    (projectiveLine j) ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := k) (0 : Fin (m + 1)) 1).pullback j)
    (projectiveSections j) (NadelBertiniGenericIncidence.projectiveGoodOpen j) ha

theorem exists_projective_smooth_selected {k : Type u} [Field k] [CharZero k] {m : ℕ} {X : Scheme.{u}}
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure k m)] :
    ∃ a : Fin (m + 1) → k, a 0 ≠ 0 ∧
      Smooth ((projectiveSelectedIdeal j a).subschemeι ≫ j ≫ DeJongAlterations.projectiveSpaceStructure k m) := by
  have := NadelBertiniGlobalSmooth.projectiveTotal_smooth j
  obtain ⟨a, ha0, _, ha⟩ := NadelBertiniRationalParameterIncidence.exists_projective_good_parameter j
  exact ⟨a, ha0, projective_selected_smooth j a ha⟩

end EnvelopeProperty.Vanishing.NadelBertiniFibreSmooth
