import EnvelopeProperty.Vanishing.ArithmeticOriginalLineHom

/-! # Detection on an actual original Cartesian coefficient fibre -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence

private theorem map_eq_of_natIso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {A B : C} (a b : A ⟶ B)
    (h : F.map a = F.map b) : G.map a = G.map b := by
  apply (cancel_epi (e.hom.app A)).mp
  exact (e.hom.naturality a).symm.trans
    ((congrArg (fun φ => φ ≫ e.hom.app B) h).trans (e.hom.naturality b))

/-- Equality on the actual Cartesian coefficient fibre detects whole maps
into the same original invertible target. -/
theorem pullback_map_injective_of_isPullback
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Y W : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [Flat p]
    (hi : Function.Injective (algebraMap R S))
    (w : W ⟶ Y) (q : W ⟶ Spec (.of S))
    (H : IsPullback w q p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (N : Y.Modules) (hN : IsInvertible N) {M : Y.Modules} :
    Function.Injective (fun φ : M ⟶ N => (Scheme.Modules.pullback w).map φ) := by
  intro a b hab
  apply ArithmeticOriginalLineHom.pullback_map_injective (S := S) p hi N hN
  let e := pullbackComp H.isoPullback.inv w ≪≫ pullbackCongr H.isoPullback_inv_fst
  apply map_eq_of_natIso e a b
  exact congrArg (fun φ => (Scheme.Modules.pullback H.isoPullback.inv).map φ) hab

/-- Actual forward and reverse model maps that are inverse on the actual
Cartesian coefficient fibre determine the original model isomorphism. -/
def isoOfPulledInverse_of_isPullback
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Y W : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [Flat p]
    (hi : Function.Injective (algebraMap R S))
    (w : W ⟶ Y) (q : W ⟶ Spec (.of S))
    (H : IsPullback w q p (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (A : Y.Modules) (hA : IsInvertible A) (B : Y.Modules) (hB : IsInvertible B)
    (a : A ⟶ B) (b : B ⟶ A)
    (h₁ : (Scheme.Modules.pullback w).map a ≫ (Scheme.Modules.pullback w).map b = 𝟙 _)
    (h₂ : (Scheme.Modules.pullback w).map b ≫ (Scheme.Modules.pullback w).map a = 𝟙 _) :
    A ≅ B where
  hom := a
  inv := b
  hom_inv_id := by
    apply pullback_map_injective_of_isPullback p hi w q H A hA
    exact ((Scheme.Modules.pullback w).map_comp a b).trans
      (h₁.trans ((Scheme.Modules.pullback w).map_id A).symm)
  inv_hom_id := by
    apply pullback_map_injective_of_isPullback p hi w q H B hB
    exact ((Scheme.Modules.pullback w).map_comp b a).trans
      (h₂.trans ((Scheme.Modules.pullback w).map_id B).symm)

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineHomCoherence
