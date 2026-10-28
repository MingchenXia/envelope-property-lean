import EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreBasis
import EnvelopeProperty.Cartier.SmoothEtaleAffineBasis

/-! # Genuine original lifted affine etale-coordinate basis on the ACTUAL special fibre -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreEtaleBasis
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
private abbrev X := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev g : X p k f ⟶ Spec (CommRingCat.of k) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev U₀ (U : Y.Opens) := WittTwoSpecialFibreOpens.residueOpen p k f U
variable (n : ℕ) [SmoothOfRelativeDimension n f]

/-- Actual original smooth relative dimension survives the genuine categorical special-fibre base change. -/
theorem smoothOfRelativeDimension : SmoothOfRelativeDimension n (g p k f) := by
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f).flip inferInstance

/-- EVERY original neighborhood has ACTUAL etale coordinates on a genuine original affine lifted refinement. -/
theorem exists_etale_affine_refinement {V : Y.Opens} {W : (X p k f).Opens}
    (x : X p k f) (hxV : x ∈ U₀ p k f V) (hxW : x ∈ W) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ U ≤ V ∧ x ∈ U₀ p k f U ∧ U₀ p k f U ≤ W ∧
      letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
      ∃ v : Fin n → Γ(X p k f,U₀ p k f U), (MvPolynomial.aeval (R := k) v).toRingHom.Etale := by
  let := smoothOfRelativeDimension p k f n
  obtain ⟨T,⟨hT,v,hv⟩,hxT,hTW⟩ := Cartier.SmoothEtaleAffineBasis.exists_subchart (g p k f) n x hxW
  obtain ⟨U,hU,hUV,hxU,hUT⟩ := WittTwoSpecialFibreBasis.exists_affine_refinement_below p k f x hxV hxT
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) T
  let := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
  let i : U₀ p k f U ⟶ T := homOfLE hUT
  let := (Cartier.EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) i).toAlgebra
  let : IsScalarTower k Γ(X p k f,T) Γ(X p k f,U₀ p k f U) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      ((Cartier.EtaleSchemeSectionDifferential.restrictionAlgebraHom (g p k f) i).commutes a).symm
  have he : (algebraMap Γ(X p k f,T) Γ(X p k f,U₀ p k f U)).Etale :=
    WittTwoSchemeAffineRestrictions.restriction_etale
      (WittTwoSpecialFibreOpens.residueOpen_affine p k f hU) hT i
  refine ⟨U,hU,hUV,hxU,hUT.trans hTW,fun j => (X p k f).presheaf.map i.op (v j),?_⟩
  exact Char0.etale_aeval_algebraMap v hv he

/-- The ACTUAL original lifted affine opens whose original inverse images have genuine native coordinates. -/
def coordinateOpens : Set Y.Opens :=
  {U | IsAffineOpen U ∧ letI := CanonicalGeometry.cotangentOpenAlgebra (g p k f) (U₀ p k f U)
    ∃ v : Fin n → Γ(X p k f,U₀ p k f U), (MvPolynomial.aeval (R := k) v).toRingHom.Etale}

/-- The indexed SAME original special-fibre opens, retaining their original affine lifts. -/
def basisOpens (U : coordinateOpens p k f n) : (X p k f).Opens := U₀ p k f U.val

/-- This genuine original lifted etale-coordinate family is an ACTUAL whole special-fibre basis. -/
theorem isBasis_basisOpens : Opens.IsBasis (Set.range (basisOpens p k f n)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨U,hU,_,hxU,hUW,v,hv⟩ := exists_etale_affine_refinement p k f n
    (V := ⊤) x (show x ∈ U₀ p k f ⊤ by trivial) hx
  exact ⟨U₀ p k f U,⟨⟨U,hU,v,hv⟩,rfl⟩,hxU,hUW⟩

end EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreEtaleBasis
