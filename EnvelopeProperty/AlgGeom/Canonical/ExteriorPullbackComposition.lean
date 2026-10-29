import EnvelopeProperty.AlgGeom.Canonical.CotangentMorphismFunctoriality
import EnvelopeProperty.AlgGeom.Canonical.OpenImmersionDifferential

/-! # Genuine composition of the original pullback exterior differentials -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace EnvelopeProperty.CanonicalGeometry

universe u v w z
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem originalAdjunctionMateComparison
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (A₁ : L₁ ⊣ R₁) (A₂ : L₂ ⊣ R₂)
    (a : L₂ ⟶ L₁) (b : R₁ ⟶ R₂) (hab : conjugateEquiv A₁ A₂ a = b)
    (M : C) (N : D) (ψ : L₁.obj M ⟶ N) :
    A₂.homEquiv M N (a.app M ≫ ψ) = A₁.homEquiv M N ψ ≫ b.app N := by
  have hu := unit_conjugateEquiv A₁ A₂ a M
  rw [hab] at hu
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hu,
    Category.assoc, ← b.naturality ψ, ← Category.assoc, ← Adjunction.homEquiv_unit]

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X) (h : Z ⟶ Y)

/-- The ENTIRE original pullback exterior differential genuinely composes
under the SAME actual native pullback-composition comparison and original
structural-map associativity transport, in EVERY exterior degree. -/
theorem exteriorCotangentSheafPullbackMap_comp (n : ℕ) :
    exteriorCotangentSheafPullbackMap f (h ≫ g) n =
      (Scheme.Modules.pullbackComp h g).inv.app (exteriorCotangentSheaf f n) ≫
        (Scheme.Modules.pullback h).map (exteriorCotangentSheafPullbackMap f g n) ≫
        exteriorCotangentSheafPullbackMap (g ≫ f) h n ≫
        eqToHom (congrArg (fun q ↦ exteriorCotangentSheaf q n) (Category.assoc h g f).symm) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction g
  let B := Scheme.Modules.pullbackPushforwardAdjunction h
  let D := Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)
  let T := eqToHom (congrArg (fun q ↦ exteriorCotangentSheaf q n) (Category.assoc h g f).symm)
  apply (D.homEquiv _ _).injective
  change D.homEquiv _ _ ((D.homEquiv _ _).symm (exteriorCotangentSheafMorphism f (h ≫ g) n)) = _
  rw [Equiv.apply_symm_apply]
  rw [originalAdjunctionMateComparison (A.comp B) D
    (Scheme.Modules.pullbackComp h g).inv (Scheme.Modules.pushforwardComp h g).hom
    (Scheme.Modules.conjugateEquiv_pullbackComp_inv h g)]
  change exteriorCotangentSheafMorphism f (h ≫ g) n =
    A.homEquiv _ _ (B.homEquiv _ _
      ((Scheme.Modules.pullback h).map (exteriorCotangentSheafPullbackMap f g n) ≫
        exteriorCotangentSheafPullbackMap (g ≫ f) h n ≫ T)) ≫
      (Scheme.Modules.pushforwardComp h g).hom.app _
  rw [B.homEquiv_naturality_left, B.homEquiv_naturality_right]
  change exteriorCotangentSheafMorphism f (h ≫ g) n =
    A.homEquiv _ _ (exteriorCotangentSheafPullbackMap f g n ≫
      (B.homEquiv _ _ ((B.homEquiv _ _).symm
        (exteriorCotangentSheafMorphism (g ≫ f) h n))) ≫ (Scheme.Modules.pushforward h).map T) ≫ _
  rw [Equiv.apply_symm_apply, A.homEquiv_naturality_right]
  change exteriorCotangentSheafMorphism f (h ≫ g) n =
    ((A.homEquiv _ _ ((A.homEquiv _ _).symm (exteriorCotangentSheafMorphism f g n))) ≫
      (Scheme.Modules.pushforward g).map
        (exteriorCotangentSheafMorphism (g ≫ f) h n ≫ (Scheme.Modules.pushforward h).map T)) ≫
          (Scheme.Modules.pushforwardComp h g).hom.app (exteriorCotangentSheaf ((h ≫ g) ≫ f) n)
  rw [Equiv.apply_symm_apply, Functor.map_comp]
  simpa only [Category.assoc] using exteriorCotangentSheafMorphism_comp f g h n

end
end EnvelopeProperty.CanonicalGeometry
