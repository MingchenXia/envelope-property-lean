import EnvelopeProperty.Vanishing.NadelPrincipalizationPushedSection
import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeKernel
import EnvelopeProperty.AlgGeom.IdealModuleOpenRestriction

/-! # The SAME entire native rounded-kernel map under actual open base change -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationKernelMapRestriction
open Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem factor_square_isIso {C : Type*} [Category C]
    {A B C₀ D A' B' C' D' : C}
    (a : A ≅ A') (b : B ≅ B') (c : C₀ ≅ C') (u : D ≅ D')
    (κ : A ⟶ B) (κ' : A' ⟶ B') (β : B ⟶ C₀) (β' : B' ⟶ C')
    (i : A ⟶ D) (i' : A' ⟶ D') (δ : D ⟶ C₀) (δ' : D' ⟶ C')
    [Mono β'] [IsIso κ']
    (hk : κ ≫ β = i ≫ δ) (hk' : κ' ≫ β' = i' ≫ δ')
    (hi : a.hom ≫ i' = i ≫ u.hom)
    (hβ : b.hom ≫ β' = β ≫ c.hom)
    (hδ : u.inv ≫ δ ≫ c.hom = δ') : IsIso κ := by
  have hd : δ ≫ c.hom = u.hom ≫ δ' := by
    apply (cancel_epi u.inv).mp
    simpa only [Iso.inv_hom_id_assoc] using hδ
  have he : κ ≫ b.hom = a.hom ≫ κ' := by
    apply (cancel_mono β').mp
    calc
      (κ ≫ b.hom) ≫ β' = κ ≫ β ≫ c.hom := by rw [Category.assoc, hβ]
      _ = i ≫ δ ≫ c.hom := by rw [← Category.assoc, hk, Category.assoc]
      _ = i ≫ u.hom ≫ δ' := by rw [hd]
      _ = a.hom ≫ i' ≫ δ' := by rw [← Category.assoc, ← hi, Category.assoc]
      _ = (a.hom ≫ κ') ≫ β' := by rw [Category.assoc, hk']
  have : IsIso (κ ≫ b.hom) := he.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right κ b.hom

private theorem exists_ideal_openIso {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (g : X ⟶ Y) [IsOpenImmersion g] (J : X.IdealSheafData) (hJ : I.comap g = J) :
    ∃ e : (pullback g).obj I.toModules ≅ J.toModules,
      e.hom ≫ J.toModulesInclusion =
        (pullback g).map I.toModulesInclusion ≫ (pullbackUnitIso g).hom := by
  subst J
  exact ⟨I.openPullbackModuleIso g, I.toModulesComapPullbackMap_inclusion g⟩

private theorem smooth_open_transport {A B S : Scheme.{u}}
    (s : A ⟶ S) (j : B ⟶ A) [IsOpenImmersion j] (t : B ⟶ S)
    (e : j ≫ s = t) (n : ℕ) [SmoothOfRelativeDimension n s] :
    SmoothOfRelativeDimension n t :=
  e ▸ ((Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := j) (n := 0) (m := n) s))

variable {k : Type u} [Field k] [CharZero k] {X₀ X B₀ B : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k)) (g : X ⟶ X₀) (π : B₀ ⟶ X₀)
    (p : B ⟶ X) (v : B ⟶ B₀) (H : IsPullback p v g π) (n : ℕ)
    [IsOpenImmersion g] [QuasiCompact π] [SmoothOfRelativeDimension n f]
    [SmoothOfRelativeDimension n (π ≫ f)]
    (J : B₀.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

omit [CharZero k] in
private theorem base_smooth : SmoothOfRelativeDimension n (g ≫ f) :=
  (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := g) (n := 0) (m := n) f)

include H in
omit [CharZero k] [IsOpenImmersion g] [QuasiCompact π] [SmoothOfRelativeDimension n f] in
private theorem local_smooth [IsOpenImmersion v] :
    SmoothOfRelativeDimension n (p ≫ (g ≫ f)) :=
  smooth_open_transport (π ≫ f) v (p ≫ (g ≫ f))
    ((Category.assoc v π f).symm.trans
      ((congrArg (fun a => a ≫ f) H.w.symm).trans (Category.assoc p g f))) n

/-- Actual local invertibility of the SAME native kernel map implies that
its actual pulled original global map is invertible. Every ideal/module/whole
inclusion/differential comparison is proved from the original open square. -/
theorem isIso_pullback_kernelMap
    (hlocal :
      letI : IsOpenImmersion v := MorphismProperty.of_isPullback H inferInstance
      letI : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
      letI : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
      letI := base_smooth f g n
      letI := local_smooth f g π p v H n
      IsIso (kernelToPushforwardRounded (g ≫ f) p n (J.comap v)
        (hJ.comap_of_smooth (π ≫ f) v) q)) :
    IsIso ((pullback g).map (kernelToPushforwardRounded f π n J hJ q)) := by
  let : IsOpenImmersion v := MorphismProperty.of_isPullback H inferInstance
  let : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
  let : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
  let := base_smooth f g n
  let := local_smooth f g π p v H n
  let : IsIso (kernelToPushforwardRounded (g ≫ f) p n (J.comap v)
    (hJ.comap_of_smooth (π ≫ f) v) q) := hlocal
  obtain ⟨eK, heK⟩ := exists_ideal_openIso (roundedCanonicalKernelIdeal f π n J hJ q) g _
    (NadelPrincipalizationRelativeKernel.kernel_comap f g π p v H n J hJ q)
  let eB := NadelPrincipalizationPushedSection.roundedIso π p v g H f n J hJ q
  let eC := NadelPrincipalizationPushedSection.relativeIso π p v g H f n
  let β' := (pushforward p).map (relativeRoundedInclusion (g ≫ f) p n (J.comap v)
    (hJ.comap_of_smooth (π ≫ f) v) q)
  let : Mono (relativeRoundedInclusion (g ≫ f) p n (J.comap v)
    (hJ.comap_of_smooth (π ≫ f) v) q) := mono_relativeRoundedInclusion _ _ _ _ _ _
  let : Mono β' := inferInstance
  have hk := congrArg (fun z => (pullback g).map z)
    (kernelToPushforwardRounded_inclusion f π n J hJ q)
  simp only [Functor.map_comp] at hk
  exact factor_square_isIso eK eB eC (pullbackUnitIso g)
    ((pullback g).map (kernelToPushforwardRounded f π n J hJ q))
    (kernelToPushforwardRounded (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q)
    ((pullback g).map ((pushforward π).map (relativeRoundedInclusion f π n J hJ q))) β'
    ((pullback g).map (roundedCanonicalKernelIdeal f π n J hJ q).toModulesInclusion)
    (roundedCanonicalKernelIdeal (g ≫ f) p n (J.comap v)
      (hJ.comap_of_smooth (π ≫ f) v) q).toModulesInclusion
    ((pullback g).map (pushedDifferentialSection f π n))
    (pushedDifferentialSection (g ≫ f) p n) hk
    (kernelToPushforwardRounded_inclusion (g ≫ f) p n _ _ q) heK
    (NadelPrincipalizationPushedSection.roundedIso_inclusion π p v g H f n J hJ q)
    (NadelPrincipalizationPushedSection.relativeIso_section π p v g H f n)

end EnvelopeProperty.Vanishing.NadelPrincipalizationKernelMapRestriction
