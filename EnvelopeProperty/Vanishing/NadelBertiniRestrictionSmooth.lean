import EnvelopeProperty.Vanishing.NadelBertiniRestrictionAlgebra
import EnvelopeProperty.Vanishing.NadelBertiniRestrictionIdeal
/-! # The same original whole incidence restricted to its actual source open is smooth -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniRestrictionSmooth
open NadelBertiniUniversal NadelBertiniRestrictionAlgebra NadelBertiniRestrictionIdeal
  NadelBertiniLinearSmooth SchemeLineSectionEvaluation
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}

theorem restricted_toSource_smooth (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : IsInvertible L)
    (W : X.affineOpens) (e : (Scheme.Modules.pullback W.1.ι).obj L ≅ unitObj W.1.toScheme)
    (s : Fin (m + 1) → Γ(L, ⊤)) (j : Fin (m + 1))
    (hj : (show Γ(W.1.toScheme, ⊤) from e.hom.app ⊤ (affinePullbackUnitTop W.1.ι L (s j))) = 1) :
    let f := FlatGlobalSections.firstProjection (S := parameterRing R m) p
    let V := f ⁻¹ᵁ W.1
    let J := (incidenceIdeal p L hL s).comap V.ι
    Smooth (J.subschemeι ≫ f ∣_ W.1) := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing R m) p
  let V := f ⁻¹ᵁ W.1
  let g := f ∣_ W.1
  let q := V.ι ≫ FlatGlobalSections.structureMap (S := parameterRing R m) p
  let I := incidenceIdeal p L hL s
  let J := I.comap V.ι
  let c : Fin (m + 1) → Γ(W.1.toScheme, ⊤) := fun a => e.hom.app ⊤ (affinePullbackUnitTop W.1.ι L (s a))
  let E := localPullbackFrame f W.1 e
  let : IsAffine W.1.toScheme := W.2
  let φ := Spec.map (CommRingCat.ofHom (algebraMap R (parameterRing R m)))
  let : IsAffineHom φ := inferInstance
  have H := (isPullback_morphismRestrict f W.1).paste_vert
    (CategoryTheory.IsPullback.of_hasPullback p (Spec.map (CommRingCat.ofHom (algebraMap R (parameterRing R m)))))
  let : IsAffine V.toScheme := IsAffine.of_isPullback H
  have hV : IsAffineOpen V := (inferInstanceAs (IsAffine V.toScheme))
  let : Algebra Γ(W.1.toScheme, ⊤) Γ(V.toScheme, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(W.1.toScheme, ⊤) Γ(J.subscheme, ⊤) := (J.subschemeι ≫ g).appTop.hom.toAlgebra
  let A := squareSectionsAlgEquiv (W.1.ι ≫ p) g q H
  have hc : (show Γ(V.toScheme, ⊤) from sectionAtOne
      (pullbackSectionHom V.ι (SchemeModuleGlobalSections.sectionHom (productLine (m := m) p L) (universalSection p L s)) ≫ E.hom)) =
      A (linearForm c) := by
    change E.hom.app ⊤ (sectionAtOne (pullbackSectionHom V.ι
      (topSectionHom (productLine (m := m) p L) (universalSection p L s)))) = _
    rw [← Berkovich.SchemeFramedSectionPullback.affinePullbackUnitTop_eq_sectionAtOne]
    exact (restricted_universal_frame p L W.1 e s).trans
      (squareSectionsEquiv_linearForm (W.1.ι ≫ p) g q H c).symm
  have hI : J.ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ = Ideal.map A.toRingHom (linearIdeal c) := by
    have ht := comap_zeroIdeal_top (productLine (m := m) p L) (hL.pullback f)
      (SchemeModuleGlobalSections.sectionHom (productLine (m := m) p L) (universalSection p L s)) ⟨V, hV⟩ E
    apply ht.trans
    rw [hc, linearIdeal, Ideal.map_span, Set.image_singleton]
    rfl
  let eQ := Ideal.quotientEquivAlg (linearIdeal c) (J.ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) A hI
  have := linear_smooth c j hj
  have : Algebra.Smooth Γ(W.1.toScheme, ⊤) (Γ(V.toScheme, ⊤) ⧸ J.ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) :=
    Algebra.Smooth.of_equiv eQ
  have : Algebra.Smooth Γ(W.1.toScheme, ⊤) Γ(J.subscheme, ⊤) :=
    Algebra.Smooth.of_equiv (NadelBertiniSubschemeSections.quotientAlgEquivSections J g)
  have : IsAffine J.subscheme := (IsClosedImmersion.isAffine_surjective_of_isAffine J.subschemeι).1
  change Smooth (J.subschemeι ≫ g)
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance
end EnvelopeProperty.Vanishing.NadelBertiniRestrictionSmooth
