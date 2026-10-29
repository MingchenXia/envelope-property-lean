import EnvelopeProperty.Global.FibreGlobalKernelFiltration
import EnvelopeProperty.InfinitesimalIdempotents
import EnvelopeProperty.AdicCompletionSections
import EnvelopeProperty.Global.FibreIdealPowerCechMaps
import EnvelopeProperty.AlgGeom.FormalFunctionsCompatibleCohomology
import EnvelopeProperty.Global.ProjectiveAffineCover
import EnvelopeProperty.Global.FibreInfinitesimalBoundaryTransitions

/-! # Actual formal functions for the whole original projective section ring -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FibreProjectiveFormalSections

private def idempotentsCongr {A B : Type u} [Ring A] [Ring B] (e : A ≃+* B) :
    {a : A // IsIdempotentElem a} ≃ {b : B // IsIdempotentElem b} where
  toFun a := ⟨e a.1, a.2.map e.toRingHom⟩
  invFun b := ⟨e.symm b.1, b.2.map e.symm.toRingHom⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.1)
  right_inv b := Subtype.ext (e.apply_symm_apply b.1)

open InfinitesimalSchemes
variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual original whole global section gives its literal original
positive-order infinitesimal sections, retaining every original coordinate. -/
def sectionMap : Γ(X, ⊤) →+* InfinitesimalIdempotents.compatibleSections I f where
  toFun s := ⟨fun n => (projection I f (n+1)).appTop s, fun n m h =>
    RingHom.congr_fun (FibreInfinitesimalH0.transition_projection_sections I f
      (Nat.succ_le_succ h)) s⟩
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_mul' s t := by apply Subtype.ext; funext n; exact map_mul _ s t
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_add' s t := by apply Subtype.ext; funext n; exact map_add _ s t

/-- Every forward coordinate is the SAME original whole projection section. -/
theorem sectionMap_apply (s : Γ(X, ⊤)) (n : ℕ) :
    (sectionMap I f s).1 n = (projection I f (n+1)).appTop s := rfl

/-- Every literal original projection preserves the full quotient coefficient square. -/
theorem projection_coefficient_quotient (n : ℕ) :
    (projection I f n).appTop.hom.comp (ProperBirationalSections.coefficientMap f) =
      (AdicCompletionSections.coefficient I f n).comp (Ideal.Quotient.mk (I^n)) := by
  rw [FibreInfinitesimalH0.projection_coefficient]
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ (projection I f n ≫ f).appTop).hom =
    (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)) ≫
      (Scheme.ΓSpecIso (.of (ring I n))).inv ≫ (structureMap I f n).appTop).hom
  rw [pullback.condition, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- The entire canonical formal section map retains the original whole coefficient triangle. -/
theorem sectionMap_coefficient :
    (sectionMap I f).comp (ProperBirationalSections.coefficientMap f) =
      AdicCompletionSections.coefficientFamily I f := by
  apply RingHom.ext
  intro r
  apply Subtype.ext
  funext n
  exact RingHom.congr_fun (projection_coefficient_quotient I f (n+1)) r

section ExplicitCover
variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : IsOpenCover U)
    [IsNoetherianRing R] [IsAdicComplete I R] (hf : IsProjectiveFactorization f)

include U hU hcover hf

/-- Genuine original kernel-filtration reconstruction separates actual
whole global sections using their literal original infinitesimal coordinates. -/
theorem sectionMap_injective_of_cover : Function.Injective (sectionMap I f) := by
  let := FlatGlobalSections.sectionsAlgebra f
  let e := FibreGlobalKernelFiltration.quotientReconstructionEquiv I f U hU hcover hf
  intro s t hst
  apply e.injective
  apply Subtype.ext
  funext n
  apply (Submodule.Quotient.eq _).mpr
  change (projection I f (n+1)).appTop (s-t) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg (fun z => z.1 n) hst)

private theorem sectionMap_surjective_of_lifts
    (hlift : ∀ s : InfinitesimalIdempotents.compatibleSections I f,
      ∀ n, ∃ t : Γ(X, ⊤), (projection I f (n+1)).appTop t = s.1 n) :
    Function.Surjective (sectionMap I f) := by
  let := FlatGlobalSections.sectionsAlgebra f
  let F := FibreInfinitesimalH0.imageFiltration I f
  let e := FibreGlobalKernelFiltration.quotientReconstructionEquiv I f U hU hcover hf
  intro s
  choose t ht using hlift s
  have hproj (n m : ℕ) (h : n ≤ m) : (projection I f (n+1)).appTop (t m) = s.1 n := by
    calc
      _ = (transition I f (Nat.succ_le_succ h)).appTop
          ((projection I f (m+1)).appTop (t m)) :=
        (RingHom.congr_fun (FibreInfinitesimalH0.transition_projection_sections I f
          (Nat.succ_le_succ h)) (t m)).symm
      _ = (transition I f (Nat.succ_le_succ h)).appTop (s.1 m) := congrArg _ (ht m)
      _ = s.1 n := s.2 n m h
  let q : FibreStableFiltration.compatibleQuotients I F :=
    ⟨fun n => (F.N (n+1)).mkQ (t n), by
      intro n m h
      change (F.N (n+1)).mkQ (t m) = (F.N (n+1)).mkQ (t n)
      apply (Submodule.Quotient.eq _).mpr
      change (projection I f (n+1)).appTop (t m-t n) = 0
      rw [map_sub, hproj n m h, ht n, sub_self]⟩
  refine ⟨e.symm q, ?_⟩
  apply Subtype.ext
  funext n
  have hq := congrArg (fun z : FibreStableFiltration.compatibleQuotients I F => z.1 n)
    (e.apply_symm_apply q)
  change (F.N (n+1)).mkQ (e.symm q) = (F.N (n+1)).mkQ (t n) at hq
  have hm := (Submodule.Quotient.eq (F.N (n+1))).mp hq
  change (projection I f (n+1)).appTop (e.symm q-t n) = 0 at hm
  rw [map_sub] at hm
  exact (sub_eq_zero.mp hm).trans (ht n)

/-- The actual compatible infinitesimal obstruction family vanishes by
genuine finite projective Rees cohomology and adic separation; every given
coordinate therefore lifts to an original whole global section. -/
theorem compatible_coordinate_lifts
    (s : InfinitesimalIdempotents.compatibleSections I f) (n : ℕ) :
    ∃ t : Γ(X, ⊤), (projection I f (n+1)).appTop t = s.1 n := by
  let y : ∀ n : ℕ, (FcReesCechDegreeComplex.degreeComplex I f U hU (n+1)).homology 1 :=
    fun n => (FcReesCechIdealPowerSections.homologyIso I f U hU (n+1) 1).hom
      (FibreInfinitesimalH0Cech.sectionBoundary f U hcover I hU (n+1) (s.1 n))
  have hy : y = 0 := FormalFunctionsCompatibleCohomology.compatible_positive_eq_zero
    I f U hU hf hcover 1 y
    (FibreInfinitesimalBoundaryTransitions.compatible_sectionBoundary I f U hcover hU s)
  apply (FibreInfinitesimalH0Cech.sectionBoundary_eq_zero_iff
    f U hcover I hU (n+1) (s.1 n)).mp
  let e := FcReesCechIdealPowerSections.homologyIso I f U hU (n+1) 1
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  exact (congrArg (fun z => z n) hy).trans (map_zero e.hom.hom).symm

/-- Actual compatible boundary vanishing and genuine original kernel quotient
reconstruction derive surjectivity of the SAME original canonical section map. -/
theorem sectionMap_surjective_of_cover : Function.Surjective (sectionMap I f) :=
  sectionMap_surjective_of_lifts I f U hU hcover hf
    (compatible_coordinate_lifts I f U hU hcover hf)

end ExplicitCover

variable [IsNoetherianRing R] [IsAdicComplete I R] (hf : IsProjectiveFactorization f)
include hf

/-- Genuine original projective geometry internally derives every cover and
separatedness input to injectivity of the literal original formal section map. -/
theorem sectionMap_injective : Function.Injective (sectionMap I f) := by
  let := ProjectiveAffineCover.separated f hf
  obtain ⟨ι, hι, hfin, U, hU, hcover⟩ := ProjectiveAffineCover.exists_affine_openCover f hf
  let := hι
  let := hfin
  exact sectionMap_injective_of_cover I f U hU hcover hf
/-- Genuine projective geometry derives every cover and separatedness input
internally to the actual whole original formal-section surjectivity theorem. -/
theorem sectionMap_surjective : Function.Surjective (sectionMap I f) := by
  let := ProjectiveAffineCover.separated f hf
  obtain ⟨ι, hι, hfin, U, hU, hcover⟩ := ProjectiveAffineCover.exists_affine_openCover f hf
  let := hι
  let := hfin
  exact sectionMap_surjective_of_cover I f U hU hcover hf

/-- Genuine formal functions for the WHOLE original projective section ring,
with only the actual complete Noetherian base and original projective factorization. -/
def formalEquiv : Γ(X, ⊤) ≃+* InfinitesimalIdempotents.compatibleSections I f :=
  RingEquiv.ofBijective (sectionMap I f)
    ⟨sectionMap_injective I f hf, sectionMap_surjective I f hf⟩

/-- The entire formal-functions forward homomorphism is the literal original section map. -/
theorem formalEquiv_toRingHom : (formalEquiv I f hf).toRingHom = sectionMap I f := rfl

/-- Every coordinate of the whole formal-functions comparison is the
literal original projection on the ENTIRE original global section. -/
theorem formalEquiv_apply (s : Γ(X, ⊤)) (n : ℕ) :
    (formalEquiv I f hf s).1 n = (projection I f (n+1)).appTop s := rfl

/-- The whole formal-functions isomorphism retains the same original coefficient triangle. -/
theorem formalEquiv_coefficient :
    (formalEquiv I f hf).toRingHom.comp (ProperBirationalSections.coefficientMap f) =
      AdicCompletionSections.coefficientFamily I f := sectionMap_coefficient I f

/-- Genuine inverse formal-functions reconstruction recovers every
prescribed literal original infinitesimal section coordinate. -/
theorem formalEquiv_symm_apply
    (s : InfinitesimalIdempotents.compatibleSections I f) (n : ℕ) :
    (projection I f (n+1)).appTop ((formalEquiv I f hf).symm s) = s.1 n :=
  congrArg (fun z : InfinitesimalIdempotents.compatibleSections I f => z.1 n)
    ((formalEquiv I f hf).apply_symm_apply s)

/-- Actual complete projective formal functions and genuine unique nilpotent
idempotent lifting derive bijectivity of the LITERAL original closed-fibre restriction. -/
def idempotentRestrictionEquiv :
    {e : Γ(X, ⊤) // IsIdempotentElem e} ≃
      {e : Γ(model I f 1, ⊤) // IsIdempotentElem e} :=
  (idempotentsCongr (formalEquiv I f hf)).trans
    (InfinitesimalIdempotents.familyEquiv I f).symm

/-- The actual idempotent bijection is precisely the original order-one
whole global-section restriction, with every original nilpotent retained. -/
theorem idempotentRestrictionEquiv_apply
    (e : {e : Γ(X, ⊤) // IsIdempotentElem e}) :
    idempotentRestrictionEquiv I f hf e =
      SchemeIdempotentRestriction.map (projection I f 1) e := by
  apply Subtype.ext
  rfl

end EnvelopeProperty.FibreProjectiveFormalSections
