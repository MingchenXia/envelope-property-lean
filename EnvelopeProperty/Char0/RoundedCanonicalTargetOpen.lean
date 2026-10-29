import EnvelopeProperty.Char0.GlobalRoundedQuotientOpenPullback

/-! # Original rounded quotient vanishing under an actual open target factor -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem targetFactorizationIso {W : Scheme.{u}}
    {A A' B B' I I' : W.Modules} (eA : A' ≅ A) (eB : B ≅ B') (eI : I ≅ I')
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

private theorem targetScalarNaturality {W : Scheme.{u}} {A B : W.Modules}
    (b : Γ(W, ⊤)) (ψ : A ⟶ B) :
    SchemeUnitScalarAction.globalScalarAction A b ≫ ψ =
      ψ ≫ SchemeUnitScalarAction.globalScalarAction B b := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change ψ.val.app (.op U) ((SchemeUnitScalarAction.globalScalarAction A b).val.app (.op U) m) =
    (SchemeUnitScalarAction.globalScalarAction B b).val.app (.op U) (ψ.val.app (.op U) m)
  rw [SchemeUnitScalarAction.globalScalarAction_apply,
    SchemeUnitScalarAction.globalScalarAction_apply]
  exact (ψ.val.app (.op U)).hom.map_smul _ _

private theorem targetAbsoluteInclusionCongr {k : Type u} [Field k] {W : Scheme.{u}}
    (f₁ f₂ : W ⟶ Spec (.of k)) (e : f₁ = f₂) (n : ℕ)
    (J : W.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (eqToIso (congrArg (fun t => absolute t n J hJ q) e)).hom ≫
      absoluteRoundedInclusion f₂ n J hJ q =
      absoluteRoundedInclusion f₁ n J hJ q ≫
        (eqToIso (congrArg (fun t => CanonicalGeometry.canonicalLineSheaf t n) e)).hom := by
  cases e
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Every entire original function has the same actual quotient vanishing
criterion before and after factoring through an actual open target. -/
theorem quotientDifferentialSection_apply_eq_zero_iff_targetOpen
    {k : Type u} [Field k] {X X' Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (e : X' ⟶ X) [IsOpenImmersion e]
    (γ : Z ⟶ X') (n : ℕ) [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension n (e ≫ f)]
    [SmoothOfRelativeDimension n ((γ ≫ e) ≫ f)]
    [SmoothOfRelativeDimension n (γ ≫ (e ≫ f))]
    (J : Z.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) (b : Γ(Z, ⊤)) :
    (quotientDifferentialSection f (γ ≫ e) n J hJ q).val.app (.op ⊤) b = 0 ↔
      (quotientDifferentialSection (e ≫ f) γ n J hJ q).val.app (.op ⊤) b = 0 := by
  let F := Scheme.Modules.pullback γ
  let δe := CanonicalGeometry.exteriorCotangentSheafPullbackMap f e n
  let : IsIso δe := CanonicalGeometry.isIso_exteriorCotangentSheafPullbackMap_openImmersion f e n
  let eA := (Scheme.Modules.pullbackComp γ e).symm.app
      (CanonicalGeometry.canonicalLineSheaf f n) ≪≫ F.mapIso (asIso δe)
  let es := Category.assoc γ e f
  let eB := eqToIso (congrArg (fun t => CanonicalGeometry.canonicalLineSheaf t n) es)
  let eI := eqToIso (congrArg (fun t => absolute t n J hJ q) es)
  let d := CanonicalGeometry.exteriorCotangentSheafPullbackMap f (γ ≫ e) n
  let d' := CanonicalGeometry.exteriorCotangentSheafPullbackMap (e ≫ f) γ n
  have hd : eA.hom ≫ d' ≫ eB.inv = d := by
    change (Scheme.Modules.pullbackComp γ e).inv.app
      (CanonicalGeometry.exteriorCotangentSheaf f n) ≫
        (Scheme.Modules.pullback γ).map δe ≫ d' ≫
          eqToHom (congrArg (fun t => CanonicalGeometry.exteriorCotangentSheaf t n) es.symm) = d
    exact (CanonicalGeometry.exteriorCotangentSheafPullbackMap_comp f e γ n).symm
  have hs := targetAbsoluteInclusionCongr ((γ ≫ e) ≫ f) (γ ≫ (e ≫ f)) es n J hJ q
  have hδ : eA.inv ≫ (SchemeUnitScalarAction.globalScalarAction _ b ≫ d) ≫ eB.hom =
      SchemeUnitScalarAction.globalScalarAction _ b ≫ d' := by
    rw [← hd, ← Category.assoc (SchemeUnitScalarAction.globalScalarAction _ b) eA.hom,
      targetScalarNaturality b eA.hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hf := targetFactorizationIso eA.symm eB eI
    (absoluteRoundedInclusion ((γ ≫ e) ≫ f) n J hJ q)
    (absoluteRoundedInclusion (γ ≫ (e ≫ f)) n J hJ q) hs
    (SchemeUnitScalarAction.globalScalarAction _ b ≫ d)
  rw [Iso.symm_hom, hδ] at hf
  exact (quotientDifferentialSection_apply_eq_zero_iff_factorization f (γ ≫ e) n J hJ q b).trans
    (hf.trans (quotientDifferentialSection_apply_eq_zero_iff_factorization (e ≫ f) γ n J hJ q b).symm)

end EnvelopeProperty.Char0.RoundedCanonicalModule
