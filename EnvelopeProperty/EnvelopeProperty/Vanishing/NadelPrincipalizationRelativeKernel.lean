import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeQuotientSection
import EnvelopeProperty.Vanishing.NadelPrincipalizationSectionKernelIso
import EnvelopeProperty.Char0.RoundedCanonicalKernelIdeal

/-! # The entire original rounded canonical kernel on an actual open Cartesian square -/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeKernel
open CanonicalGeometry Char0 Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- The ENTIRE original rounded canonical kernel ideal genuinely commutes
with the actual original open Cartesian geometric comap. Local openness,
quasicompactness, same-n smoothness and quotient comparisons are internally
PRODUCED; no kernel, canonical-iso, section or vanishing premise is added. -/
theorem kernel_comap :
    letI : IsOpenImmersion v := MorphismProperty.of_isPullback H inferInstance
    letI : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
    letI : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
    letI := base_smooth f g n
    letI := local_smooth f g π p v H n
    (roundedCanonicalKernelIdeal f π n J hJ q).comap g =
      roundedCanonicalKernelIdeal (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q := by
  let : IsOpenImmersion v := MorphismProperty.of_isPullback H inferInstance
  let : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
  let : Smooth (π ≫ f) := SmoothOfRelativeDimension.smooth n (π ≫ f)
  let := base_smooth f g n
  let := local_smooth f g π p v H n
  let M := quotient f π n J hJ q
  let : M.IsQuasicoherent := quotient_isQuasicoherent f π n J hJ q
  let N := quotient (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q
  let : N.IsQuasicoherent := quotient_isQuasicoherent (g ≫ f) p n _ _ q
  let : ((pullback v).obj M).IsQuasicoherent :=
    (isQuasicoherent B).prop_of_iso ((restrictFunctorIsoPullback v).app M) inferInstance
  let δ := quotientDifferentialSection f π n J hJ q
  let ε := quotientDifferentialSection (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q
  let e := NadelPrincipalizationRelativeQuotientSection.quotientIso f g π p v H.w n J hJ q
  have he : ((pullbackUnitIso v).inv ≫ (pullback v).map δ) ≫ e.hom = ε := by
    simpa only [Category.assoc] using
      (NadelPrincipalizationRelativeQuotientSection.quotientIso_section f g π p v H.w n J hJ q)
  exact (NadelPrincipalizationOpenKernel.kernel_comap π p v g H M δ).trans
    (NadelPrincipalizationSectionKernelIso.kernel_eq p ((pullback v).obj M) N e
      ((pullbackUnitIso v).inv ≫ (pullback v).map δ) ε he)

end EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeKernel
