import EnvelopeProperty.Vanishing.AmpleScalarBaseChange

/-! # The actual ample line across a surjective coefficient map

The closed projective coefficient immersion and the actual hyperplane
pullback comparison preserve the original line and its positive exponent.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.RelativeFiniteAmpleClosedBase
open ProjBerk

/-- The same original very ample line remains very ample when its coefficient
base is composed with the closed immersion of a surjective ring map. -/
theorem isVeryAmple_comp_of_surjective {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (φ : R →+* A) (hφ : Function.Surjective φ)
    (q : X ⟶ Spec (.of A)) (L : X.Modules)
    (hL : SchemeLineAmpleness.IsVeryAmple q L) :
    SchemeLineAmpleness.IsVeryAmple (q ≫ Spec.map (CommRingCat.ofHom φ)) L := by
  change (∃ (n : ℕ) (j : X ⟶ NativeProjectiveScheme A n),
    IsClosedImmersion j ∧ j ≫ nativeStructureMap = q ∧
      Nonempty ((Scheme.Modules.pullback j).obj
        (coordinateHyperplaneTwist (R := A) (0 : Fin (n + 1)) 1) ≅ L)) at hL
  change ∃ (n : ℕ) (j : X ⟶ NativeProjectiveScheme R n),
    IsClosedImmersion j ∧ j ≫ nativeStructureMap = q ≫ Spec.map (CommRingCat.ofHom φ) ∧
      Nonempty ((Scheme.Modules.pullback j).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≅ L)
  obtain ⟨n, j, hj, hjq, ⟨eL⟩⟩ := hL
  let c : NativeProjectiveScheme A n ⟶ NativeProjectiveScheme R n := nativeCoefficientMap φ
  let aA : NativeProjectiveScheme A n ⟶ Spec (.of A) := nativeStructureMap
  let aR : NativeProjectiveScheme R n ⟶ Spec (.of R) := nativeStructureMap
  let : IsClosedImmersion j := hj
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  let : IsClosedImmersion c :=
    MorphismProperty.of_isPullback (isPullback_nativeCoefficientBaseChange (n := n) φ).flip
      inferInstance
  have hcb : c ≫ aR = aA ≫ Spec.map (CommRingCat.ofHom φ) := nativeCoefficientMap_over_base φ
  have hjAq : j ≫ aA = q := hjq
  refine ⟨n, j ≫ c, inferInstance, ?_, ?_⟩
  · change (j ≫ c) ≫ aR = _
    calc
      (j ≫ c) ≫ aR = j ≫ (c ≫ aR) := Category.assoc j c aR
      _ = j ≫ (aA ≫ Spec.map (CommRingCat.ofHom φ)) := congrArg (fun t => j ≫ t) hcb
      _ = (j ≫ aA) ≫ Spec.map (CommRingCat.ofHom φ) := (Category.assoc _ _ _).symm
      _ = q ≫ Spec.map (CommRingCat.ofHom φ) :=
        congrArg (fun t => t ≫ Spec.map (CommRingCat.ofHom φ)) hjAq
  · let eC : (Scheme.Modules.pullback c).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≅
          coordinateHyperplaneTwist (R := A) (0 : Fin (n + 1)) 1 :=
      ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso φ (0 : Fin (n + 1)) 1
    exact ⟨((Scheme.Modules.pullbackComp j c).app _).symm ≪≫
      (Scheme.Modules.pullback j).mapIso eC ≪≫ eL⟩

/-- The same positive tensor power proves ampleness over the original
coefficient ring after composing a surjective coefficient morphism. -/
theorem isAmple_comp_of_surjective {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (φ : R →+* A) (hφ : Function.Surjective φ)
    (q : X ⟶ Spec (.of A)) (L : X.Modules)
    (hL : SchemeLineAmpleness.IsAmple q L) :
    SchemeLineAmpleness.IsAmple (q ≫ Spec.map (CommRingCat.ofHom φ)) L := by
  refine ⟨hL.isInvertible, ?_⟩
  obtain ⟨r, hr, hV⟩ := hL.2
  exact ⟨r, hr, isVeryAmple_comp_of_surjective φ hφ q _ hV⟩

/-- A literal factorization through a closed coefficient immersion retains
very ampleness on the original scheme and the original line in both directions. -/
theorem isVeryAmple_closedBase_iff {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (φ : R →+* A) (hφ : Function.Surjective φ)
    (p : X ⟶ Spec (.of R)) (q : X ⟶ Spec (.of A))
    (hqp : q ≫ Spec.map (CommRingCat.ofHom φ) = p) (L : X.Modules) :
    SchemeLineAmpleness.IsVeryAmple q L ↔ SchemeLineAmpleness.IsVeryAmple p L := by
  constructor
  · intro hL
    rw [← hqp]
    exact isVeryAmple_comp_of_surjective φ hφ q L hL
  · intro hL
    let : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
      IsClosedImmersion.spec_of_surjective _ hφ
    have H : IsPullback (𝟙 X) q p (Spec.map (CommRingCat.ofHom φ)) :=
      IsPullback.of_horiz_isIso_mono ⟨by simpa using hqp.symm⟩
    exact SchemeAmpleClosedRestriction.veryAmple_of_iso
      (AmpleScalarBaseChange.isVeryAmple_of_isPullback (𝟙 X) p q φ H L hL)
      ((pullbackId X).app L)

/-- Closed coefficient-base change preserves the same original ample line
in both directions, with no hypothesis on either coefficient ring. -/
theorem isAmple_closedBase_iff {R A : Type u} [CommRing R] [CommRing A]
    {X : Scheme.{u}} (φ : R →+* A) (hφ : Function.Surjective φ)
    (p : X ⟶ Spec (.of R)) (q : X ⟶ Spec (.of A))
    (hqp : q ≫ Spec.map (CommRingCat.ofHom φ) = p) (L : X.Modules) :
    SchemeLineAmpleness.IsAmple q L ↔ SchemeLineAmpleness.IsAmple p L := by
  constructor
  · intro hL
    rw [← hqp]
    exact isAmple_comp_of_surjective φ hφ q L hL
  · intro hL
    refine ⟨hL.isInvertible, ?_⟩
    obtain ⟨r, hr, hV⟩ := hL.2
    exact ⟨r, hr, (isVeryAmple_closedBase_iff φ hφ p q hqp _).mpr hV⟩

end EnvelopeProperty.Vanishing.RelativeFiniteAmpleClosedBase
