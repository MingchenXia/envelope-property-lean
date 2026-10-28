import EnvelopeProperty.Vanishing.NadelBlowupCanonicalBaseChangeFamily

/-! # The whole native forward canonical differential square, before any inversion -/

open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareForward
open CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem differential_congr {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {g h : Y ⟶ X} (w : g = h) (n : ℕ) :
    (pullbackCongr w).hom.app (exteriorCotangentSheaf f n) ≫
        exteriorCotangentSheafPullbackMap f h n =
      exteriorCotangentSheafPullbackMap f g n ≫
        eqToHom (congrArg (fun a => exteriorCotangentSheaf (a ≫ f) n) w) := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, eqToHom_refl, Category.comp_id]

private theorem forward_word {C : Type*} [Category C]
    {L₀ L₁ L₂ L₃ A B T₀ T₁ T₂ T₃ : C}
    (s : L₀ ⟶ L₁) (s' : L₁ ⟶ L₀) (e : L₁ ⟶ L₂) (t' : L₂ ⟶ L₃)
    (a : L₀ ⟶ A) (D : L₃ ⟶ B) (V : B ⟶ T₃) (P : A ⟶ T₀)
    (l : T₀ ⟶ T₁) (r : T₃ ⟶ T₂) (z : T₁ ⟶ T₂)
    (U₁ : L₁ ⟶ T₁) (U₂ : L₂ ⟶ T₂)
    (hs : s ≫ s' = 𝟙 L₀) (h₁ : U₁ = s' ≫ a ≫ P ≫ l)
    (h₂ : U₂ = t' ≫ D ≫ V ≫ r) (hw : e ≫ U₂ = U₁ ≫ z) :
    (s ≫ e ≫ t') ≫ D ≫ V ≫ r = a ≫ P ≫ l ≫ z := by
  have hc := (congrArg (fun q => e ≫ q) h₂.symm).trans (hw.trans (congrArg (fun q => q ≫ z) h₁))
  have h := congrArg (fun q => s ≫ q) hc
  simpa only [Category.assoc, reassoc_of% hs, Category.id_comp] using h

/-- The ENTIRE original canonical differentials commute on the SAME
original scheme square, before inversion or any chosen canonical iso. -/
theorem whole_forward_square {k : Type u} [Field k] {X₀ X B₀ B : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k)) (g : X ⟶ X₀) (π : B₀ ⟶ X₀)
    (p : B ⟶ X) (v : B ⟶ B₀) (w : p ≫ g = v ≫ π) (n : ℕ) :
    ((pullbackComp p g).hom.app (exteriorCotangentSheaf f n) ≫
      (pullbackCongr w).hom.app (exteriorCotangentSheaf f n) ≫
      (pullbackComp v π).inv.app (exteriorCotangentSheaf f n)) ≫
        (pullback v).map (exteriorCotangentSheafPullbackMap f π n) ≫
          exteriorCotangentSheafPullbackMap (π ≫ f) v n ≫
            eqToHom (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc v π f).symm) =
      (pullback p).map (exteriorCotangentSheafPullbackMap f g n) ≫
        exteriorCotangentSheafPullbackMap (g ≫ f) p n ≫
          eqToHom (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc p g f).symm) ≫
            eqToHom (congrArg (fun a => exteriorCotangentSheaf (a ≫ f) n) w) := by
  exact forward_word
    ((pullbackComp p g).hom.app (exteriorCotangentSheaf f n))
    ((pullbackComp p g).inv.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w).hom.app (exteriorCotangentSheaf f n))
    ((pullbackComp v π).inv.app (exteriorCotangentSheaf f n))
    ((pullback p).map (exteriorCotangentSheafPullbackMap f g n))
    ((pullback v).map (exteriorCotangentSheafPullbackMap f π n))
    (exteriorCotangentSheafPullbackMap (π ≫ f) v n)
    (exteriorCotangentSheafPullbackMap (g ≫ f) p n)
    (eqToHom (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc p g f).symm))
    (eqToHom (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc v π f).symm))
    (eqToHom (congrArg (fun a => exteriorCotangentSheaf (a ≫ f) n) w))
    (exteriorCotangentSheafPullbackMap f (p ≫ g) n)
    (exteriorCotangentSheafPullbackMap f (v ≫ π) n)
    (Iso.hom_inv_id_app (pullbackComp p g) (exteriorCotangentSheaf f n))
    (exteriorCotangentSheafPullbackMap_comp f g p n)
    (exteriorCotangentSheafPullbackMap_comp f π v n)
    (differential_congr f w n)

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareForward
