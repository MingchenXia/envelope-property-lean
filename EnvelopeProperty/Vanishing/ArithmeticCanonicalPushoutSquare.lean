import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutTransport

/-! # The whole universal differential on an actual arithmetic square -/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential

open ArithmeticCanonicalGlobal

set_option backward.isDefEq.respectTransparency false

private theorem square_of_composites {C : Type*} [Category* C]
    {A B C₀ D E : C} (α : A ≅ B) (γ : B ≅ C₀) (δ : D ≅ C₀)
    (l : A ⟶ E) (r : D ⟶ E) (s : B ⟶ E) (t : C₀ ⟶ E)
    (hl : α.hom ≫ s = l) (hr : δ.hom ≫ t = r) (hc : γ.hom ≫ t = s) :
    l = α.hom ≫ γ.hom ≫ δ.inv ≫ r := by
  rw [← hl, ← hr]
  simp only [δ.inv_hom_id_assoc, hc]

/-- The actual universal square maps commute through the native source
composition and equality comparisons, in every exterior degree. -/
theorem exteriorPullbackMap_square
    {R S : Type u} [CommRing R] [CommRing S] {X Y V W : Scheme.{u}}
    (φ : CommRingCat.of R ⟶ CommRingCat.of S)
    (f : X ⟶ Spec (.of R)) (h : Y ⟶ Spec (.of S))
    (fV : V ⟶ Spec (.of R)) (hW : W ⟶ Spec (.of S))
    (a : Y ⟶ X) (b : W ⟶ Y) (c : V ⟶ X) (d : W ⟶ V)
    (wa : CoefficientSquare φ f h a) (wb : CoefficientSquare (𝟙 _) h hW b)
    (wc : CoefficientSquare (𝟙 _) f fV c) (wd : CoefficientSquare φ fV hW d)
    (he : b ≫ a = d ≫ c) (q : ℕ) :
    (Scheme.Modules.pullback b).map (exteriorPullbackMap φ f h a wa q) ≫
        exteriorPullbackMap (𝟙 _) h hW b wb q =
      (Scheme.Modules.pullbackComp b a).hom.app (relativeExteriorSheaf f q) ≫
        (Scheme.Modules.pullbackCongr he).hom.app (relativeExteriorSheaf f q) ≫
        (Scheme.Modules.pullbackComp d c).inv.app (relativeExteriorSheaf f q) ≫
        (Scheme.Modules.pullback d).map (exteriorPullbackMap (𝟙 _) f fV c wc q) ≫
        exteriorPullbackMap φ fV hW d wd q := by
  let w₁ := coefficientSquare_comp φ (𝟙 _) f h hW a b wa wb
  let w₂ := coefficientSquare_comp (𝟙 _) φ f fV hW c d wc wd
  let D₁ := exteriorPullbackMap (φ ≫ 𝟙 _) f hW (b ≫ a) w₁ q
  let D₂ := exteriorPullbackMap (𝟙 _ ≫ φ) f hW (d ≫ c) w₂ q
  let α := (Scheme.Modules.pullbackComp b a).app (relativeExteriorSheaf f q)
  let γ := (Scheme.Modules.pullbackCongr he).app (relativeExteriorSheaf f q)
  let δ := (Scheme.Modules.pullbackComp d c).app (relativeExteriorSheaf f q)
  exact square_of_composites α γ δ _ _ D₁ D₂
    (exteriorPullbackMap_comp φ (𝟙 _) f h hW a b wa wb q)
    (exteriorPullbackMap_comp (𝟙 _) φ f fV hW c d wc wd q)
    (exteriorPullbackMap_congr (φ ≫ 𝟙 _) (𝟙 _ ≫ φ) f hW (b ≫ a) (d ≫ c)
      w₁ w₂ (by simp) he q)

/-- Invertibility transports across the same whole square. Both open
maps are proved invertible from their actual structural equations. -/
theorem isIso_pullback_exteriorPullbackMap_of_local
    {R S : Type u} [CommRing R] [CommRing S] {X Y V W : Scheme.{u}}
    (φ : CommRingCat.of R ⟶ CommRingCat.of S)
    (f : X ⟶ Spec (.of R)) (h : Y ⟶ Spec (.of S))
    (fV : V ⟶ Spec (.of R)) (hW : W ⟶ Spec (.of S))
    (a : Y ⟶ X) (b : W ⟶ Y) (c : V ⟶ X) (d : W ⟶ V)
    [IsOpenImmersion b] [IsOpenImmersion c]
    (wa : CoefficientSquare φ f h a) (wb : CoefficientSquare (𝟙 _) h hW b)
    (wc : CoefficientSquare (𝟙 _) f fV c) (wd : CoefficientSquare φ fV hW d)
    (he : b ≫ a = d ≫ c) (hb : b ≫ h = hW) (hc : c ≫ f = fV) (q : ℕ)
    [IsIso (exteriorPullbackMap φ fV hW d wd q)] :
    IsIso ((Scheme.Modules.pullback b).map (exteriorPullbackMap φ f h a wa q)) := by
  have : IsIso (exteriorPullbackMap (𝟙 _) h hW b wb q) :=
    exteriorPullbackMap_openImmersion_isIso h hW b wb hb q
  have : IsIso (exteriorPullbackMap (𝟙 _) f fV c wc q) :=
    exteriorPullbackMap_openImmersion_isIso f fV c wc hc q
  have H := exteriorPullbackMap_square φ f h fV hW a b c d wa wb wc wd he q
  have : IsIso ((Scheme.Modules.pullback b).map (exteriorPullbackMap φ f h a wa q) ≫
      exteriorPullbackMap (𝟙 _) h hW b wb q) := by
    rw [H]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (exteriorPullbackMap (𝟙 _) h hW b wb q)

theorem isIso_of_eq {C : Type*} [Category* C] {A B : C}
    {a b : A ⟶ B} (he : a = b) [IsIso a] : IsIso b := he ▸ inferInstance

end EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutDifferential
