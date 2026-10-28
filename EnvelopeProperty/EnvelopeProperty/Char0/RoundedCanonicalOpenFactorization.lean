import EnvelopeProperty.Char0.RoundedCanonicalOpenPullback
import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverFactorization

/-! # SAME whole original scalar differential under genuine open factorizations -/

open CategoryTheory AlgebraicGeometry Opposite
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem originalFactorizationIso {C : Type u} [Category.{v} C]
    {A A' B B' I I' : C} (eA : A' ≅ A) (eB : B ≅ B') (eI : I ≅ I')
    (inc : I ⟶ B) (inc' : I' ⟶ B') (hs : eI.hom ≫ inc' = inc ≫ eB.hom)
    (δ : A ⟶ B) :
    (∃ θ : A ⟶ I, θ ≫ inc = δ) ↔
      ∃ θ : A' ⟶ I', θ ≫ inc' = eA.hom ≫ δ ≫ eB.hom := by
  constructor
  · rintro ⟨θ, hθ⟩
    refine ⟨eA.hom ≫ θ ≫ eI.hom, ?_⟩
    simp only [Category.assoc]
    rw [hs, ← Category.assoc θ inc, hθ]
  · rintro ⟨θ, hθ⟩
    refine ⟨eA.inv ≫ θ ≫ eI.inv, ?_⟩
    apply (cancel_mono eB.hom).mp
    have hi : eI.inv ≫ inc ≫ eB.hom = inc' := by
      rw [← hs, Iso.inv_hom_id_assoc]
    simp only [Category.assoc]
    rw [hi, hθ, Iso.inv_hom_id_assoc]

private theorem originalCompositeSquare {C : Type u} [Category.{v} C]
    {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (e₀ : A₀ ⟶ A₁) (e₁ : A₁ ⟶ A₂) (i₀ : A₀ ⟶ B₀)
    (i₁ : A₁ ⟶ B₁) (i₂ : A₂ ⟶ B₂) (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂)
    (h₀ : e₀ ≫ i₁ = i₀ ≫ b₀) (h₁ : e₁ ≫ i₂ = i₁ ≫ b₁) :
    (e₀ ≫ e₁) ≫ i₂ = i₀ ≫ b₀ ≫ b₁ := by
  rw [Category.assoc, h₁, ← Category.assoc, h₀, Category.assoc]

private theorem originalScalarComposite {C : Type u} [Category.{v} C]
    {A' A B B' : C} (e : A' ⟶ A) (s : A ⟶ A) (s' : A' ⟶ A')
    (d : A ⟶ B) (b : B ⟶ B') (d' : A' ⟶ B')
    (hs : s' ≫ e = e ≫ s) (hd : e ≫ d ≫ b = d') :
    e ≫ (s ≫ d) ≫ b = s' ≫ d' := by
  simp only [Category.assoc]
  rw [← Category.assoc e s, ← hs]
  simpa only [Category.assoc] using congrArg (fun t => s' ≫ t) hd

private theorem originalScalarNaturality {W : Scheme.{u}} {A B : W.Modules}
    (a : Γ(W, ⊤)) (ψ : A ⟶ B) :
    SchemeUnitScalarAction.globalScalarAction A a ≫ ψ =
      ψ ≫ SchemeUnitScalarAction.globalScalarAction B a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change ψ.val.app (.op U) ((SchemeUnitScalarAction.globalScalarAction A a).val.app (.op U) m) =
    (SchemeUnitScalarAction.globalScalarAction B a).val.app (.op U) (ψ.val.app (.op U) m)
  rw [SchemeUnitScalarAction.globalScalarAction_apply,
    SchemeUnitScalarAction.globalScalarAction_apply]
  exact (ψ.val.app (.op U)).hom.map_smul _ _

private theorem originalAbsoluteEqInclusion {k : Type u} [Field k] {W : Scheme.{u}}
    (f₁ f₂ : W ⟶ Spec (.of k)) (e : f₁ = f₂) (n : ℕ)
    (J : W.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (eqToIso (congrArg (fun t => absolute t n J hJ q) e)).hom ≫
      absoluteRoundedInclusion f₂ n J hJ q =
      absoluteRoundedInclusion f₁ n J hJ q ≫
        (eqToIso (congrArg (fun t => CanonicalGeometry.canonicalLineSheaf t n) e)).hom := by
  cases e
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

variable {k : Type u} [Field k] [CharZero k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) [Smooth (g ≫ f)]
    (h : Z ⟶ Y) [IsOpenImmersion h]

/-- SAME actual whole pulled original scalar canonical map factorization
is equivalent to SAME original open-composite scalar map factorization. -/
theorem openScalarFactorization_iff (n : ℕ)
    (J : Y.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (a : Γ(Y, ⊤)) :
    (∃ θ : (Scheme.Modules.pullback h).obj
          ((Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)) ⟶
        (Scheme.Modules.pullback h).obj (absolute (g ≫ f) n J hJ q),
      θ ≫ (Scheme.Modules.pullback h).map (absoluteRoundedInclusion (g ≫ f) n J hJ q) =
        (Scheme.Modules.pullback h).map
          (SchemeUnitScalarAction.globalScalarAction _ a ≫
            CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)) ↔
    (∃ θ : (Scheme.Modules.pullback (h ≫ g)).obj (CanonicalGeometry.canonicalLineSheaf f n) ⟶
        absolute ((h ≫ g) ≫ f) n (J.comap h) (hJ.comap_of_smooth (g ≫ f) h) q,
      θ ≫ absoluteRoundedInclusion ((h ≫ g) ≫ f) n (J.comap h)
        (hJ.comap_of_smooth (g ≫ f) h) q =
        SchemeUnitScalarAction.globalScalarAction _ (h.appTop a) ≫
          CanonicalGeometry.exteriorCotangentSheafPullbackMap f (h ≫ g) n) := by
  let F := Scheme.Modules.pullback h
  let A := (Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n)
  let B := CanonicalGeometry.canonicalLineSheaf (g ≫ f) n
  let d := CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n
  let I := absolute (g ≫ f) n J hJ q
  let inc := absoluteRoundedInclusion (g ≫ f) n J hJ q
  let JL := J.comap h
  let hJL := hJ.comap_of_smooth (g ≫ f) h
  let eA := (Scheme.Modules.pullbackComp h g).symm.app (CanonicalGeometry.canonicalLineSheaf f n)
  let eS := (Category.assoc h g f).symm
  let δh := CanonicalGeometry.exteriorCotangentSheafPullbackMap (g ≫ f) h n
  let : IsIso δh := CanonicalGeometry.isIso_exteriorCotangentSheafPullbackMap_openImmersion
    (g ≫ f) h n
  let eB := asIso δh ≪≫ eqToIso (congrArg (fun t => CanonicalGeometry.canonicalLineSheaf t n) eS)
  let eI := absoluteOpenPullbackIso (g ≫ f) h n J hJ q ≪≫
    eqToIso (congrArg (fun t => absolute t n JL hJL q) eS)
  have hs : eI.hom ≫ absoluteRoundedInclusion ((h ≫ g) ≫ f) n JL hJL q =
      F.map inc ≫ eB.hom := by
    have he := originalAbsoluteEqInclusion (h ≫ (g ≫ f)) ((h ≫ g) ≫ f) eS n JL hJL q
    have ho := absoluteOpenPullbackIso_inclusion (g ≫ f) h n J hJ q
    exact originalCompositeSquare _ _ _ _ _ _ _ ho he
  have hd : eA.hom ≫ F.map d ≫ eB.hom =
      CanonicalGeometry.exteriorCotangentSheafPullbackMap f (h ≫ g) n :=
    (CanonicalGeometry.exteriorCotangentSheafPullbackMap_comp f g h n).symm
  have ha := originalScalarNaturality (h.appTop a) eA.hom
  have hδ : eA.hom ≫ F.map (SchemeUnitScalarAction.globalScalarAction A a ≫ d) ≫ eB.hom =
      SchemeUnitScalarAction.globalScalarAction _ (h.appTop a) ≫
        CanonicalGeometry.exteriorCotangentSheafPullbackMap f (h ≫ g) n := by
    rw [F.map_comp, SchemeUnitScalarActionBaseChange.globalScalarAction_pullback]
    exact originalScalarComposite _ _ _ _ _ _ ha hd
  have hf := originalFactorizationIso eA eB eI (F.map inc)
    (absoluteRoundedInclusion ((h ≫ g) ≫ f) n JL hJL q) hs
    (F.map (SchemeUnitScalarAction.globalScalarAction A a ≫ d))
  rw [hδ] at hf
  exact hf

end
end EnvelopeProperty.Char0.RoundedCanonicalModule
