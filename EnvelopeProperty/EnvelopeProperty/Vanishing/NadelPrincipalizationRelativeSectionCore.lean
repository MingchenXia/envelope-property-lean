import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareForward

/-! # Original whole differential-compatible line comparisons

The comparisons are PRODUCED from the original native forward square,
actual open differentials and actual pullback/equality coherence. No
canonical-line isomorphism or whole-square assertion is an input.
-/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSectionCore
open CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exists_compatible_lines {C : Type*} [Category C]
    {L₀ L₁ L₂ A A' B B' T T₁ T₂ : C}
    (s₀ : L₀ ≅ L₁) (s₁ : L₁ ≅ L₂) (s₂ : A ≅ L₂)
    (a : L₀ ≅ A') (D : A ⟶ B) (V : B ≅ T) (P : A' ⟶ B')
    (r : T ≅ T₂) (l : B' ≅ T₁) (z : T₁ ≅ T₂)
    (hforward : (s₀.hom ≫ s₁.hom ≫ s₂.inv) ≫ D ≫ V.hom ≫ r.hom =
      a.hom ≫ P ≫ l.hom ≫ z.hom) :
    ∃ eA : A ≅ A', ∃ eB : B ≅ B', D ≫ eB.hom = eA.hom ≫ P := by
  let s := s₀ ≪≫ s₁ ≪≫ s₂.symm
  have hf : s.hom ≫ D ≫ V.hom ≫ r.hom = a.hom ≫ P ≫ l.hom ≫ z.hom := by
    simpa only [s, Iso.trans_hom, Iso.symm_hom, Category.assoc] using hforward
  refine ⟨s.symm ≪≫ a, V ≪≫ r ≪≫ z.symm ≪≫ l.symm, ?_⟩
  have hc := congrArg (fun q => s.inv ≫ q ≫ z.inv ≫ l.inv) hf
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hc

private theorem exists_compatible_raw {C : Type*} [Category C]
    {L₀ L₁ L₂ A A' B B' T T₁ T₂ : C}
    (s₀ : L₀ ⟶ L₁) (s₁ : L₁ ⟶ L₂) (s₂ : L₂ ⟶ A)
    (a : L₀ ⟶ A') (D : A ⟶ B) (V : B ⟶ T) (P : A' ⟶ B')
    (r : T ⟶ T₂) (l : B' ⟶ T₁) (z : T₁ ⟶ T₂)
    [IsIso s₀] [IsIso s₁] [IsIso s₂] [IsIso a] [IsIso V]
    [IsIso r] [IsIso l] [IsIso z]
    (hforward : (s₀ ≫ s₁ ≫ s₂) ≫ D ≫ V ≫ r = a ≫ P ≫ l ≫ z) :
    ∃ eA : A ≅ A', ∃ eB : B ≅ B', D ≫ eB.hom = eA.hom ≫ P := by
  exact exists_compatible_lines (asIso s₀) (asIso s₁) (asIso s₂).symm
    (asIso a) D (asIso V) P (asIso r) (asIso l) (asIso z) hforward

variable {k : Type u} [Field k] {X₀ X B₀ B : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k)) (g : X ⟶ X₀) (π : B₀ ⟶ X₀)
    (p : B ⟶ X) (v : B ⟶ B₀) (w : p ≫ g = v ≫ π) (n : ℕ)

include w in
/-- Actual original open maps and the original whole native forward square
PRODUCE genuine comparisons of the original canonical modules, retaining
the ENTIRE original vertical differential triangle. -/
theorem existsCompatibleLines [IsOpenImmersion g] [IsOpenImmersion v] :
    ∃ eA : (pullback v).obj ((pullback π).obj (exteriorCotangentSheaf f n)) ≅
        (pullback p).obj (exteriorCotangentSheaf (g ≫ f) n),
    ∃ eB : (pullback v).obj (exteriorCotangentSheaf (π ≫ f) n) ≅
        exteriorCotangentSheaf (p ≫ (g ≫ f)) n,
      (pullback v).map (exteriorCotangentSheafPullbackMap f π n) ≫ eB.hom =
        eA.hom ≫ exteriorCotangentSheafPullbackMap (g ≫ f) p n := by
  let : IsIso (exteriorCotangentSheafPullbackMap f g n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f g n
  let : IsIso (exteriorCotangentSheafPullbackMap (π ≫ f) v n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion (π ≫ f) v n
  exact exists_compatible_raw (C := B.Modules)
    ((pullbackComp p g).hom.app (exteriorCotangentSheaf f n))
    ((pullbackCongr w).hom.app (exteriorCotangentSheaf f n))
    ((pullbackComp v π).inv.app (exteriorCotangentSheaf f n))
    ((pullback p).map (exteriorCotangentSheafPullbackMap f g n))
    ((pullback v).map (exteriorCotangentSheafPullbackMap f π n))
    (exteriorCotangentSheafPullbackMap (π ≫ f) v n)
    (exteriorCotangentSheafPullbackMap (g ≫ f) p n)
    (eqToHom (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc v π f).symm))
    (eqToHom (congrArg (fun a => exteriorCotangentSheaf a n) (Category.assoc p g f).symm))
    (eqToHom (congrArg (fun a => exteriorCotangentSheaf (a ≫ f) n) w))
    (NadelBlowupCanonicalSquareForward.whole_forward_square f g π p v w n)


end EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSectionCore
