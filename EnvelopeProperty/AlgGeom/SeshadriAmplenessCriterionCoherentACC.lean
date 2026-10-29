import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCoherentDevissage
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual coherent-subobject ACC from original finite affine modules

Ascending chains are tested on the original affine section images inside
the original finite section modules of F. No NoetherianObject instance for
the whole sheaf-module category is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

private def originalSectionMap {X : Scheme.{u}} {F : X.Modules}
    (A : Subobject F) (U : X.Opens) :
    Γ((A : X.Modules), U) →ₗ[Γ(X, U)] Γ(F, U) :=
  (A.arrow.val.app (op U)).hom

private def originalSectionImage {X : Scheme.{u}} {F : X.Modules}
    (A : Subobject F) (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) :=
  LinearMap.range (originalSectionMap A U)

private theorem originalSectionImage_mono {X : Scheme.{u}} {F : X.Modules}
    {A B : Subobject F} (h : A ≤ B) (U : X.Opens) :
    originalSectionImage A U ≤ originalSectionImage B U := by
  intro t ht
  change ∃ s, originalSectionMap A U s = t at ht
  obtain ⟨s, rfl⟩ := ht
  change ∃ b, originalSectionMap B U b = originalSectionMap A U s
  refine ⟨(Subobject.ofLE A B h).val.app (op U) s, ?_⟩
  exact congrArg (fun q : (A : X.Modules) ⟶ F => q.val.app (op U) s)
    (Subobject.ofLE_arrow h)

private theorem originalSectionImage_eq_surjective
    {X : Scheme.{u}} {F : X.Modules} {A B : Subobject F}
    (h : A ≤ B) (U : X.Opens)
    (hrange : originalSectionImage A U = originalSectionImage B U) :
    Function.Surjective ((Subobject.ofLE A B h).val.app (op U)) := by
  intro b
  have hb : B.arrow.val.app (op U) b ∈ originalSectionImage A U := by
    rw [hrange]
    change ∃ b', originalSectionMap B U b' = B.arrow.val.app (op U) b
    exact ⟨b, rfl⟩
  change ∃ a, originalSectionMap A U a = B.arrow.val.app (op U) b at hb
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  let E : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U)
  let : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := X.ringCatSheaf) (op U)
  have hi : Function.Injective (B.arrow.val.app (op U)) := by
    have hB : Mono B.arrow := Subobject.arrow_mono B
    have hmap : Mono (E.map B.arrow) :=
      @CategoryTheory.preserves_mono_of_preservesLimit X.Modules (ModuleCat Γ(X, U))
        inferInstance inferInstance E _ _ B.arrow inferInstance hB
    exact (ModuleCat.mono_iff_injective (E.map B.arrow)).mp hmap
  apply hi
  have hw := congrArg (fun q : (A : X.Modules) ⟶ F => q.val.app (op U) a)
    (Subobject.ofLE_arrow h)
  exact hw.trans ha

private theorem originalSectionImage_chain_stabilizes
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (c : ℕ →o Subobject F) (U : X.affineOpens) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → originalSectionImage (c N) U.1 =
      originalSectionImage (c n) U.1 := by
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
    Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen F U
  let v : ℕ →o Submodule Γ(X, U.1) Γ(F, U.1) :=
    ⟨fun n => originalSectionImage (c n) U.1,
      fun i j hij => originalSectionImage_mono (c.monotone hij) U.1⟩
  exact monotone_stabilizes_iff_noetherian.mpr inferInstance v

private theorem isIso_of_affineCover_restrictions
    {X : Scheme.{u}} {A B : X.Modules} (v : A ⟶ B)
    {ι : Type u} (U : ι → X.affineOpens)
    (hcover : ∀ x : X, ∃ i, x ∈ (U i).1)
    (hlocal : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).1.ι).map v)) :
    IsIso v := by
  have hxIso (x : X) : IsIso ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map v) := by
    obtain ⟨i, hxi⟩ := hcover x
    let y : (U i).1.toScheme := ⟨x, hxi⟩
    let e := Scheme.Modules.restrictStalkNatIso (U i).1.ι y
    let F := Scheme.Modules.restrictFunctor (U i).1.ι ⋙
      Scheme.Modules.toPresheaf (U i).1.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    let G := Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    let : IsIso ((Scheme.Modules.restrictFunctor (U i).1.ι).map v) := hlocal i
    have hf : IsIso (F.map v) := by
      dsimp only [F, Functor.comp_map]
      infer_instance
    have hc : IsIso (e.hom.app A ≫ G.map v) := by
      erw [← e.hom.naturality]
      change IsIso (F.map v ≫ e.hom.app B)
      infer_instance
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (e.hom.app A) (G.map v)
      inferInstance hc
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app (φ := v)).mpr
  intro V
  let : ∀ x : V, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map v).hom) := fun x => hxIso x.1
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
    ((SheafOfModules.toSheaf X.ringCatSheaf).map v) V

private theorem subobject_eq_of_affineCover_images
    {X : Scheme.{u}} {F : X.Modules} {A B : Subobject F}
    [(A : X.Modules).IsQuasicoherent] [(B : X.Modules).IsQuasicoherent]
    (h : A ≤ B) {ι : Type u} (U : ι → X.affineOpens)
    (hcover : ∀ x : X, ∃ i, x ∈ (U i).1)
    (himages : ∀ i, originalSectionImage A (U i).1 = originalSectionImage B (U i).1) :
    A = B := by
  let v := Subobject.ofLE A B h
  let : Mono v := by dsimp only [v]; infer_instance
  have hlocal (i : ι) : IsIso ((Scheme.Modules.restrictFunctor (U i).1.ι).map v) := by
    let V := (U i).1
    let : IsAffine V.toScheme := (U i).2
    apply Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (v.val.app (op (V.ι ''ᵁ ⊤)))
    rw [V.ι_image_top]
    refine ⟨?_, originalSectionImage_eq_surjective h V (himages i)⟩
    let E : X.Modules ⥤ ModuleCat.{u} Γ(X, V) :=
      SheafOfModules.evaluation X.ringCatSheaf (op V)
    let : PreservesFiniteLimits E :=
      SheafOfModules.Finite.evaluationPreservesFiniteLimits (R := X.ringCatSheaf) (op V)
    have hv : Mono v := by dsimp only [v]; infer_instance
    have hmap : Mono (E.map v) :=
      @CategoryTheory.preserves_mono_of_preservesLimit X.Modules (ModuleCat Γ(X, V))
        inferInstance inferInstance E _ _ v inferInstance hv
    exact (ModuleCat.mono_iff_injective (E.map v)).mp hmap
  let : IsIso v := isIso_of_affineCover_restrictions v U hcover hlocal
  exact Subobject.eq_of_comm (asIso v) (Subobject.ofLE_arrow h)

/-- Actual ascending QC subobjects stabilize by original Noetherian section modules. -/
theorem coherent_subobject_chain_stabilizes
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (c : ℕ →o Subobject F) (hqc : ∀ n, (c n : X.Modules).IsQuasicoherent) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c N = c n := by
  classical
  obtain ⟨s, hs, hfin, htop⟩ := X.isBasis_affineOpens.exists_finite_of_isCompact
    (U := ⊤) isCompact_univ
  let : Finite s := hfin
  let : Fintype s := Fintype.ofFinite s
  let U : s → X.affineOpens := fun i => ⟨i.val, hs i.property⟩
  have hcover : ∀ x : X, ∃ i, x ∈ (U i).1 := by
    intro x
    have hx : x ∈ sSup s := htop ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hx
    exact ⟨⟨V, hV⟩, hxV⟩
  have hstab (i : s) : ∃ N : ℕ, ∀ n, N ≤ n →
      originalSectionImage (c N) (U i).1 = originalSectionImage (c n) (U i).1 :=
    originalSectionImage_chain_stabilizes F c (U i)
  choose N hN using hstab
  let M := Finset.univ.sup N
  have hi (i : s) : N i ≤ M := Finset.le_sup (Finset.mem_univ i)
  refine ⟨M, ?_⟩
  intro n hn
  let : (c M : X.Modules).IsQuasicoherent := hqc M
  let : (c n : X.Modules).IsQuasicoherent := hqc n
  apply subobject_eq_of_affineCover_images (c.monotone hn) U hcover
  intro i
  exact (hN i M (hi i)).symm.trans (hN i n ((hi i).trans hn))

#check @coherent_subobject_chain_stabilizes
#print axioms coherent_subobject_chain_stabilizes

end EnvelopeProperty.SeshadriAmplenessCriterion
