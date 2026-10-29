import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutOpenDifferential

/-! # Equality transport for the same arithmetic whole differential -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

open ArithmeticCanonicalGlobal

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}

theorem exteriorPullbackMap_congr
    (φ φ' : CommRingCat.of R ⟶ CommRingCat.of S)
    (f : X ⟶ Spec (.of R)) (h : Y ⟶ Spec (.of S)) (g g' : Y ⟶ X)
    (w : CoefficientSquare φ f h g) (w' : CoefficientSquare φ' f h g')
    (hφ : φ = φ') (hg : g = g') (q : ℕ) :
    (Scheme.Modules.pullbackCongr hg).hom.app (relativeExteriorSheaf f q) ≫
        exteriorPullbackMap φ' f h g' w' q = exteriorPullbackMap φ f h g w q := by
  subst φ'
  subst g'
  simp [Scheme.Modules.pullbackCongr]

theorem exteriorPullbackMap_openImmersion_of_structure
    (f : X ⟶ Spec (.of R)) (h : Y ⟶ Spec (.of R))
    (g : Y ⟶ X) [IsOpenImmersion g]
    (w : CoefficientSquare (𝟙 (CommRingCat.of R)) f h g) (he : g ≫ f = h) (q : ℕ) :
    exteriorPullbackMap (𝟙 _) f h g w q =
      (ArithmeticCanonicalGlobalRestriction.exteriorPullbackIso f g q).hom ≫
        eqToHom (congrArg (fun h => relativeExteriorSheaf h q) he) := by
  subst h
  simpa only [eqToHom_refl, Category.comp_id] using exteriorPullbackMap_openImmersion f g q

theorem exteriorPullbackMap_openImmersion_isIso
    (f : X ⟶ Spec (.of R)) (h : Y ⟶ Spec (.of R))
    (g : Y ⟶ X) [IsOpenImmersion g]
    (w : CoefficientSquare (𝟙 (CommRingCat.of R)) f h g) (he : g ≫ f = h) (q : ℕ) :
    IsIso (exteriorPullbackMap (𝟙 _) f h g w q) := by
  rw [exteriorPullbackMap_openImmersion_of_structure f h g w he q]
  infer_instance

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential
