/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeResidueCompletion
import EnvelopeProperty.Berkovich.ValuationCompletionEquiv

/-! # Actual native/affine completed residue comparisons with whole coefficients -/
open scoped NNReal
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {A : Type u} [CommRing A]

private abbrev valuedCompletion (v : ValuedPoint A) : Type u :=
  (EnvelopeProperty.Valuation.toRealAbs v.residueVal).Completion

private def valuedResidueToCompletion (v : ValuedPoint A) :
    v.prime.asIdeal.ResidueField →+* valuedCompletion v :=
  UniformSpace.Completion.coeRingHom.comp
    (WithAbs.equiv (EnvelopeProperty.Valuation.toRealAbs v.residueVal)).symm.toRingHom

private theorem exists_valuedCompletionSpectrumEquiv (v : ValuedPoint A) :
    ∃ E : valuedCompletion v ≃+* Spectrum.H v.toSpectrum,
      (∀ z, ‖E z‖ = ‖z‖) ∧ ∀ a : A,
        E (valuedResidueToCompletion v (algebraMap A v.prime.asIdeal.ResidueField a)) =
          v.toSpectrum.toH a := by
  obtain ⟨a, rfl⟩ : ∃ a : Spectrum A, ValuedPoint.ofSpectrum a = v :=
    ⟨v.toSpectrum, ValuedPoint.ofSpectrum_toSpectrum v⟩
  change ∃ E : Spectrum.H a ≃+* Spectrum.H (ValuedPoint.toSpectrum (ValuedPoint.ofSpectrum a)),
    (∀ z, ‖E z‖ = ‖z‖) ∧ ∀ b : A,
      E (a.toH b) = (ValuedPoint.toSpectrum (ValuedPoint.ofSpectrum a)).toH b
  rw [ValuedPoint.toSpectrum_ofSpectrum]
  exact ⟨RingEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

/-- Actual Spec stalk residue isomorphisms and true completion of field equivalences
construct a genuine isometric whole-field comparison, preserving EVERY original coefficient. -/
theorem exists_spectrumCompletionEquiv
    (y : SchemeValuedPoint (Spec (CommRingCat.of A))) :
    ∃ E : H y ≃+* Spectrum.H (spectrumHomeomorph y),
      (∀ z, ‖E z‖ = ‖z‖) ∧ ∀ a : A,
        E (sectionToH y ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
          (spectrumHomeomorph y).toH a := by
  let v := toValuedPoint y
  let e := (Scheme.Spec.residueFieldIso (CommRingCat.of A) y.point).commRingCatIsoToRingEquiv
  have hv : ∀ z, v.residueVal (e z) = y.residueVal z := by
    intro z
    change y.residueVal ((Scheme.Spec.residueFieldIso (CommRingCat.of A) y.point).inv
      ((Scheme.Spec.residueFieldIso (CommRingCat.of A) y.point).hom z)) = y.residueVal z
    simp
  let E₁ := EnvelopeProperty.Valuation.completionCongr y.residueVal v.residueVal e hv
  obtain ⟨E₂, hnorm₂, hcoeff₂⟩ := exists_valuedCompletionSpectrumEquiv v
  change ∃ E : H y ≃+* Spectrum.H v.toSpectrum,
    (∀ z, ‖E z‖ = ‖z‖) ∧ ∀ a : A,
      E (sectionToH y ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = v.toSpectrum.toH a
  have hE₁ (z : (Spec (CommRingCat.of A)).residueField y.point) :
      E₁ (y.residueToH z) = valuedResidueToCompletion v (e z) :=
    EnvelopeProperty.Valuation.completionCongr_coe y.residueVal v.residueVal e hv z
  have hres (a : A) :
      e ((Spec (CommRingCat.of A)).evaluation ⊤ y.point trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) =
      algebraMap A v.prime.asIdeal.ResidueField a := by
    have hh := congrArg (fun f => f a)
      (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of A) y.point)
    change e.symm (algebraMap A v.prime.asIdeal.ResidueField a) =
      (Spec (CommRingCat.of A)).evaluation ⊤ y.point trivial
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) at hh
    apply e.symm.injective
    rw [RingEquiv.symm_apply_apply]
    exact hh.symm
  refine ⟨E₁.trans E₂, fun z => (hnorm₂ (E₁ z)).trans
    (EnvelopeProperty.Valuation.norm_completionCongr y.residueVal v.residueVal e hv z), ?_⟩
  intro a
  change E₂ (E₁ (y.residueToH ((Spec (CommRingCat.of A)).evaluation ⊤ y.point trivial
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) = _
  rw [hE₁, hres, hcoeff₂]

variable {X Y : Scheme.{u}}

/-- Original section restriction preserves the actual element in the same completed residue field. -/
theorem sectionToH_restrict (x : SchemeValuedPoint X) (U V : X.Opens) (i : V ≤ U)
    (hx : x.point ∈ V) (s : Γ(X, U)) :
    sectionToH x V hx (X.presheaf.map (homOfLE i).op s) = sectionToH x U (i hx) s := by
  exact congrArg (fun a => x.residueToH (X.residue x.point a))
    (X.presheaf.germ_res_apply (homOfLE i) x.point hx s)

/-- A genuine open immersion induces an isometric completed residue equivalence,
retaining every original residue element and every original section. -/
theorem exists_openImmersionCompletionEquiv (g : X ⟶ Y) [IsOpenImmersion g]
    (x : SchemeValuedPoint X) :
    ∃ E : H (map g x) ≃+* H x,
      (∀ z, ‖E z‖ = ‖z‖) ∧
      (∀ a, E ((map g x).residueToH a) =
        x.residueToH (g.residueFieldMap x.point a)) ∧
      ∀ (U : Y.Opens) (hx : g x.point ∈ U) (s : Γ(Y, U)),
        E (sectionToH (map g x) U hx s) =
          sectionToH x (g ⁻¹ᵁ U) hx (g.app U s) := by
  let e := (asIso (g.residueFieldMap x.point)).commRingCatIsoToRingEquiv
  have he : ∀ a, x.residueVal (e a) = (map g x).residueVal a := fun _ => rfl
  let E := EnvelopeProperty.Valuation.completionCongr (map g x).residueVal
    x.residueVal e he
  have hE (a) : E ((map g x).residueToH a) = x.residueToH (e a) :=
    EnvelopeProperty.Valuation.completionCongr_coe _ _ e he a
  refine ⟨E, EnvelopeProperty.Valuation.norm_completionCongr _ _ e he, hE, ?_⟩
  intro U hx s
  exact (hE _).trans (congrArg x.residueToH
    (Scheme.evaluation_naturality_apply g x.point hx s))


private def completionPointCongr {x z : SchemeValuedPoint X} (h : x = z) : H x ≃+* H z := by
  subst z
  exact RingEquiv.refl _

private theorem norm_completionPointCongr {x z : SchemeValuedPoint X} (h : x = z) (a : H x) :
    ‖completionPointCongr h a‖ = ‖a‖ := by
  subst z
  rfl

private theorem completionPointCongr_section {x z : SchemeValuedPoint X} (h : x = z)
    (U : X.Opens) (hx : x.point ∈ U) (hz : z.point ∈ U) (s : Γ(X, U)) :
    completionPointCongr h (sectionToH x U hx s) = sectionToH z U hz s := by
  subst z
  rfl

/-- Every actual affine neighborhood identifies the whole original completed residue field,
retaining every section in the original coefficient action. -/
theorem exists_affineCompletionEquiv (x : SchemeValuedPoint X) {U : X.Opens}
    (hU : IsAffineOpen U) (hx : x.point ∈ U) :
    ∃ E : H x ≃+* Spectrum.H (affineOpenSpectrumHomeomorph hU ⟨x, hx⟩),
      (∀ z, ‖E z‖ = ‖z‖) ∧ ∀ s : Γ(X, U),
        E (sectionToH x U hx s) = (affineOpenSpectrumHomeomorph hU ⟨x, hx⟩).toH s := by
  let a := affineOpenSpectrumHomeomorph hU ⟨x, hx⟩
  let y := spectrumHomeomorph.symm a
  have hmap : map hU.fromSpec y = x := by
    have he := congrArg Subtype.val
      ((affineOpenSpectrumHomeomorph hU).symm_apply_apply ⟨x, hx⟩)
    rw [affineOpenSpectrumHomeomorph_symm_coe] at he
    change map U.ι (map hU.isoSpec.inv y) = x at he
    simpa only [IsAffineOpen.fromSpec, map_comp] using he
  obtain ⟨E₁, hn₁, _, hs₁⟩ := exists_openImmersionCompletionEquiv hU.fromSpec y
  have hspec : ∃ E₂ : H y ≃+* Spectrum.H a,
      (∀ z, ‖E₂ z‖ = ‖z‖) ∧ ∀ s : Γ(X, U),
        E₂ (sectionToH y ⊤ trivial ((Scheme.ΓSpecIso Γ(X, U)).inv s)) = a.toH s := by
    have hh := exists_spectrumCompletionEquiv y
    have he : spectrumHomeomorph y = a := Homeomorph.apply_symm_apply spectrumHomeomorph a
    rw [he] at hh
    exact hh
  obtain ⟨E₂, hn₂, hs₂⟩ := hspec
  let E₀ := completionPointCongr hmap.symm
  change ∃ E : H x ≃+* Spectrum.H a, (∀ z, ‖E z‖ = ‖z‖) ∧ ∀ s : Γ(X, U),
    E (sectionToH x U hx s) = a.toH s
  have hy : hU.fromSpec y.point ∈ U := by
    change (map hU.fromSpec y).point ∈ U
    exact (congrArg point hmap).symm ▸ hx
  have hs₁' (s : Γ(X, U)) : E₁ (E₀ (sectionToH x U hx s)) =
      sectionToH y ⊤ trivial ((Scheme.ΓSpecIso Γ(X, U)).inv s) := by
    rw [show E₀ (sectionToH x U hx s) = sectionToH (map hU.fromSpec y) U hy s from
      completionPointCongr_section hmap.symm U hx hy s]
    have hh := hs₁ U hy s
    rw [hU.fromSpec_app_self] at hh
    exact hh.trans (sectionToH_restrict y ⊤ (hU.fromSpec ⁻¹ᵁ U) le_top hy
      ((Scheme.ΓSpecIso Γ(X, U)).inv s))
  exact ⟨E₀.trans (E₁.trans E₂), fun z =>
    (hn₂ (E₁ (E₀ z))).trans ((hn₁ (E₀ z)).trans (norm_completionPointCongr hmap.symm z)), fun s => by
    change E₂ (E₁ (E₀ (sectionToH x U hx s))) = _
    rw [hs₁', hs₂]⟩

/-- The actual isometric affine comparison also retains the WHOLE original field-valued scheme map. -/
theorem exists_affineCompletionEquiv_fieldPoint (x : SchemeValuedPoint X) {U : X.Opens}
    (hU : IsAffineOpen U) (hx : x.point ∈ U) :
    ∃ E : H x ≃+* Spectrum.H (affineOpenSpectrumHomeomorph hU ⟨x, hx⟩),
      (∀ z, ‖E z‖ = ‖z‖) ∧
      (∀ s : Γ(X, U), E (sectionToH x U hx s) =
        (affineOpenSpectrumHomeomorph hU ⟨x, hx⟩).toH s) ∧
      Spec.map (CommRingCat.ofHom E.toRingHom) ≫ fieldPoint x =
        Spec.map (CommRingCat.ofHom (affineOpenSpectrumHomeomorph hU ⟨x, hx⟩).toH) ≫
          hU.fromSpec := by
  obtain ⟨E, hn, hs⟩ := exists_affineCompletionEquiv x hU hx
  refine ⟨E, hn, hs, ?_⟩
  have he : E.toRingHom.comp (sectionToH x U hx) =
      (affineOpenSpectrumHomeomorph hU ⟨x, hx⟩).toH := RingHom.ext hs
  rw [fieldPoint_eq_affine x hU hx, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (E.toRingHom.comp (sectionToH x U hx))) ≫ _ = _
  rw [he]

end EnvelopeProperty.Berkovich.SchemeValuedPoint
