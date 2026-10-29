/-
Copyright (c) 2026 Chris Birkbeck and the EnvelopeProperty contributors.
Released under Apache 2.0 license as described in the file LICENSE.

The coordinatewise ordered-product exactness argument below adapts the
actual AINTLIB SchemeModuleOrderedBaseCechExact proof, replacing its
quasicoherent exactness premises by the derived original infinitesimal
section sequence on every affine intersection.
-/
import EnvelopeProperty.Global.FibreInfinitesimalModules
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechExact
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import Mathlib.Algebra.Homology.HomologySequence

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FibreInfinitesimalCech

private noncomputable def orderedBaseCechFunctorXIsoPi
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    ((orderedBaseCechComplexFunctor π U).obj M).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : OrderedCechIndex ι n,
          ((baseModulePresheafFunctor π).obj M).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k)))) :=
  orderedBaseCechObjectIsoPi π M U n

@[simp]
private theorem orderedBaseCechFunctorXIsoPi_hom_apply
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : ((orderedBaseCechComplexFunctor π U).obj M).X n)
    (i : OrderedCechIndex ι n) :
    (orderedBaseCechFunctorXIsoPi π M U n).hom x i =
      Pi.π (fun j : OrderedCechIndex ι n ↦
        ((baseModulePresheafFunctor π).obj M).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j.1 k)))) i x :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply _ i x

private theorem orderedBaseCechFunctorXIsoPi_hom_map_apply
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    (x : ((orderedBaseCechComplexFunctor π U).obj M).X n)
    (i : OrderedCechIndex ι n) :
    (orderedBaseCechFunctorXIsoPi π N U n).hom
        (((orderedBaseCechComplexFunctor π U).map f).f n x) i =
      (((baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))))
        ((orderedBaseCechFunctorXIsoPi π M U n).hom x i) := by
  rw [orderedBaseCechFunctorXIsoPi_hom_apply,
    orderedBaseCechFunctorXIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : OrderedCechIndex ι n ↦
      ((baseModulePresheafFunctor π).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) ↦ U (j.1 k)))) i) x

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [X.IsSeparated]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The actual infinitesimal short complex on the SAME original ordered
Cech family, with all original maps and unchanged original base scalars. -/
def complexSequence (d : ℕ) :
    ShortComplex (CochainComplex (ModuleCat Γ(Spec (.of R), ⊤)) ℕ) :=
  (FibreInfinitesimalModules.sequence I f d).map (orderedBaseCechComplexFunctor f U)

/-- The third complex is the WHOLE original literal infinitesimal
structure-module complex on the genuine original inverse-image family. -/
def modelComplexIso (d : ℕ) :
    orderedBaseCechComplex (InfinitesimalSchemes.projection I f d ≫ f)
        (SheafOfModules.unit (InfinitesimalSchemes.model I f d).ringCatSheaf)
        (fun i => InfinitesimalSchemes.projection I f d ⁻¹ᵁ U i) ≅
      (complexSequence I f U d).X₃ :=
  orderedBaseCechComplexPushforwardIso (InfinitesimalSchemes.projection I f d) f
    (SheafOfModules.unit (InfinitesimalSchemes.model I f d).ringCatSheaf) U

/-- In EVERY degree the third cohomology is the genuine whole original
literal infinitesimal structure-module cohomology on its original cover. -/
def modelHomologyIso (d p : ℕ) :
    (orderedBaseCechComplex (InfinitesimalSchemes.projection I f d ≫ f)
        (SheafOfModules.unit (InfinitesimalSchemes.model I f d).ringCatSheaf)
        (fun i => InfinitesimalSchemes.projection I f d ⁻¹ᵁ U i)).homology p ≅
      (complexSequence I f U d).X₃.homology p :=
  (HomologicalComplex.homologyFunctor _ _ p).mapIso (modelComplexIso I f U d)

/-- The genuine original infinitesimal ordered Cech sequence is short exact
on EVERY original affine family, with no finiteness or covering premise. -/
theorem complexSequence_shortExact (hU : ∀ i, IsAffineOpen (U i)) (d : ℕ) :
    (complexSequence I f U d).ShortExact := by
  let T := FibreInfinitesimalModules.sequence I f d
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (T.map (orderedBaseCechComplexFunctor f U)).map
    (HomologicalComplex.eval _ _ n)
  change A.ShortExact
  have hlocal (i : OrderedCechIndex ι n) :
      (T.map (baseModulePresheafFunctor f ⋙
        (CategoryTheory.evaluation X.Opensᵒᵖ
          (ModuleCat Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)))).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))))).ShortExact := by
    exact ModuleCat.shortComplex_shortExact _
      (FibreInfinitesimalModules.section_exact I f d _)
      (FibreInfinitesimalModules.section_injective I f d _)
      (FibreInfinitesimalSections.affine_projection_surjective I f d
        ⟨_, IsAffineOpen.cechIntersection U hU n i.1⟩)
  have : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (((orderedBaseCechComplexFunctor f U).map T.f).f n)
    intro x y hxy
    apply (ModuleCat.mono_iff_injective
      (orderedBaseCechFunctorXIsoPi f T.X₁ U n).hom).mp inferInstance
    funext i
    have hi := congrArg
      (fun z ↦ (orderedBaseCechFunctorXIsoPi f T.X₂ U n).hom z i) hxy
    rw [orderedBaseCechFunctorXIsoPi_hom_map_apply,
      orderedBaseCechFunctorXIsoPi_hom_map_apply] at hi
    exact (hlocal i).moduleCat_injective_f hi
  have : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (((orderedBaseCechComplexFunctor f U).map T.g).f n)
    intro y
    have preimage (i : OrderedCechIndex ι n) :
        ∃ x : ((baseModulePresheafFunctor f).obj T.X₂).obj
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))),
          ((baseModulePresheafFunctor f).map T.g).app
              (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))) x =
            (orderedBaseCechFunctorXIsoPi f T.X₃ U n).hom y i :=
      (hlocal i).moduleCat_surjective_g _
    choose x hx using preimage
    let x' := (orderedBaseCechFunctorXIsoPi f T.X₂ U n).inv x
    refine ⟨x', ?_⟩
    apply (ModuleCat.mono_iff_injective
      (orderedBaseCechFunctorXIsoPi f T.X₃ U n).hom).mp inferInstance
    funext i
    rw [orderedBaseCechFunctorXIsoPi_hom_map_apply]
    have hx'i : (orderedBaseCechFunctorXIsoPi f T.X₂ U n).hom x' i = x i :=
      congrFun (Iso.inv_hom_id_apply
        (orderedBaseCechFunctorXIsoPi f T.X₂ U n) x) i
    rw [hx'i]
    exact hx i
  refine ShortComplex.ShortExact.mk ?_
  change ((T.map (orderedBaseCechComplexFunctor f U)).map
    (HomologicalComplex.eval _ _ n)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  change ((orderedBaseCechComplexFunctor f U).obj T.X₂).X n at y
  change (((orderedBaseCechComplexFunctor f U).map T.g).f n) y = 0 at hy
  have preimage (i : OrderedCechIndex ι n) :
      ∃ x : ((baseModulePresheafFunctor f).obj T.X₁).obj
          (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))),
        ((baseModulePresheafFunctor f).map T.f).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k))) x =
          (orderedBaseCechFunctorXIsoPi f T.X₂ U n).hom y i := by
    have hyi :
        ((baseModulePresheafFunctor f).map T.g).app
            (op (∏ᶜ fun k : Fin (n + 1) ↦ U (i.1 k)))
              ((orderedBaseCechFunctorXIsoPi f T.X₂ U n).hom y i) = 0 := by
      calc
        _ = (orderedBaseCechFunctorXIsoPi f T.X₃ U n).hom
            (((orderedBaseCechComplexFunctor f U).map T.g).f n y) i :=
          (orderedBaseCechFunctorXIsoPi_hom_map_apply f T.g U n y i).symm
        _ = 0 := by rw [hy, map_zero]; rfl
    exact ((ShortComplex.moduleCat_exact_iff _).mp (hlocal i).exact) _ hyi
  choose x hx using preimage
  let x' := (orderedBaseCechFunctorXIsoPi f T.X₁ U n).inv x
  refine ⟨x', ?_⟩
  change (((orderedBaseCechComplexFunctor f U).map T.f).f n) x' = y
  apply (ModuleCat.mono_iff_injective
    (orderedBaseCechFunctorXIsoPi f T.X₂ U n).hom).mp inferInstance
  funext i
  rw [orderedBaseCechFunctorXIsoPi_hom_map_apply]
  have hx'i : (orderedBaseCechFunctorXIsoPi f T.X₁ U n).hom x' i = x i :=
    congrFun (Iso.inv_hom_id_apply
      (orderedBaseCechFunctorXIsoPi f T.X₁ U n) x) i
  rw [hx'i]
  exact hx i



/-- The genuine connecting morphism from the original infinitesimal
cohomology to the SAME original ideal-power cohomology in the next degree. -/
def connecting (hU : ∀ i, IsAffineOpen (U i)) (d p : ℕ) :
    ((complexSequence I f U d).X₃.homology p) ⟶
      ((complexSequence I f U d).X₁.homology (p+1)) :=
  (complexSequence_shortExact I f U hU d).δ p (p+1) rfl

/-- The genuine long exact sequence is exact at every original
ideal-power cohomology term in a positive degree. -/
theorem homology_exact_left (hU : ∀ i, IsAffineOpen (U i)) (d p : ℕ) :
    Function.Exact (connecting I f U hU d p)
      (HomologicalComplex.homologyMap (complexSequence I f U d).f (p+1)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((complexSequence_shortExact I f U hU d).homology_exact₁ p (p+1) rfl)

/-- The genuine long exact sequence is exact at every original
structure-module cohomology term, including degree zero. -/
theorem homology_exact_middle (hU : ∀ i, IsAffineOpen (U i)) (d p : ℕ) :
    Function.Exact (HomologicalComplex.homologyMap (complexSequence I f U d).f p)
      (HomologicalComplex.homologyMap (complexSequence I f U d).g p) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((complexSequence_shortExact I f U hU d).homology_exact₂ p)

/-- The genuine long exact sequence is exact at every original literal
infinitesimal pushforward cohomology term, including degree zero. -/
theorem homology_exact_right (hU : ∀ i, IsAffineOpen (U i)) (d p : ℕ) :
    Function.Exact (HomologicalComplex.homologyMap (complexSequence I f U d).g p)
      (connecting I f U hU d p) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((complexSequence_shortExact I f U hU d).homology_exact₃ p (p+1) rfl)

end EnvelopeProperty.FibreInfinitesimalCech
