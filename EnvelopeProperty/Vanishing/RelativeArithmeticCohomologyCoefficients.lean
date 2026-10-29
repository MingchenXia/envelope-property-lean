import EnvelopeProperty.Vanishing.GeometricCechBaseChange
import EnvelopeProperty.Vanishing.SpecializationDerivedScalarCoefficients

/-! # The same relative Čech complex over both coefficient rings

For a family over a relative affine base B over A, the original A-linear
section complex is compared to coefficient restriction of the B-linear one.
The section carriers and every restriction map remain the actual originals.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyCoefficients

open GeometricCechBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B)
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of B)) (M : Y.Modules)

/-- The literal A-action on every original open section is restriction of its
literal B-action along the given original coefficient map. -/
def openSectionsIso (U : Y.Opens) :
    (ModuleCat.restrictScalars α).obj (SchemeScalarModulePresheaf.openSections g M U) ≅
      SchemeScalarModulePresheaf.openSections (g ≫ Spec.map (CommRingCat.ofHom α)) M U := by
  refine (ModuleCat.restrictScalars α).mapIso
    (SchemeScalarModuleOpenRestriction.nativeSectionsIso g M U) ≪≫ ?_ ≪≫
      (SchemeScalarModuleOpenRestriction.nativeSectionsIso
        (g ≫ Spec.map (CommRingCat.ofHom α)) M U).symm
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro a
  ext (m : Γ(M, U))
  change (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    ((g ≫ Spec.map (CommRingCat.ofHom α)).appTop ((Scheme.ΓSpecIso (.of A)).inv a))) • m =
      (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (g.appTop ((Scheme.ΓSpecIso (.of B)).inv (α a)))) • m
  apply congrArg (fun b => (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op b) • m)
  rw [Scheme.Hom.comp_appTop]
  exact congrArg g.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α)) a).symm

variable {ι : Type u} [LinearOrder ι] (U : ι → Y.Opens)

/-- The actual relative-base complex, with its coefficients restricted to A. -/
def restrictComplex : CochainComplex (ModuleCat.{u} A) ℕ :=
  ((ModuleCat.restrictScalars α).mapHomologicalComplex (.up ℕ)).obj
    (scalarComplex g M U)

/-- The original relative and arithmetic complexes have the same original
open-section coordinates in each ordered degree. -/
def termEquiv (n : ℕ) :
    (restrictComplex α g M U).X n ≃ₗ[A]
      (scalarComplex (g ≫ Spec.map (CommRingCat.ofHom α)) M U).X n := by
  let : Module B ((restrictComplex α g M U).X n) :=
    ((scalarComplex g M U).X n).isModule
  let e : (restrictComplex α g M U).X n ≃ₗ[A]
      (∀ i : AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι n,
        SchemeScalarModulePresheaf.openSections (g ≫ Spec.map (CommRingCat.ofHom α)) M
          (intersection U n i)) :=
    { toFun := fun x i => (openSectionsIso α g M (intersection U n i)).hom
          (objectEquiv g M U n x i)
      invFun := fun x => (objectEquiv g M U n).symm
          (fun i => (openSectionsIso α g M (intersection U n i)).inv (x i))
      left_inv := fun x => by
        have h : (fun i => (openSectionsIso α g M (intersection U n i)).inv
            ((openSectionsIso α g M (intersection U n i)).hom
              (objectEquiv g M U n x i))) = objectEquiv g M U n x := by
          funext i
          exact ConcreteCategory.congr_hom
            (openSectionsIso α g M (intersection U n i)).hom_inv_id
            (objectEquiv g M U n x i)
        exact (congrArg (objectEquiv g M U n).symm h).trans
          ((objectEquiv g M U n).symm_apply_apply x)
      right_inv := fun x => by
        funext i
        let s : ∀ j : AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι n,
            SchemeScalarModulePresheaf.openSections g M (intersection U n j) :=
          fun j => (openSectionsIso α g M (intersection U n j)).inv (x j)
        have h := congrFun ((objectEquiv g M U n).apply_symm_apply s) i
        exact (congrArg (openSectionsIso α g M (intersection U n i)).hom h).trans
          (ConcreteCategory.congr_hom
            (openSectionsIso α g M (intersection U n i)).inv_hom_id (x i))
      map_add' := fun x y => by
        funext i
        exact (congrArg (openSectionsIso α g M (intersection U n i)).hom
          (congrFun ((objectEquiv g M U n).map_add x y) i)).trans
            ((openSectionsIso α g M (intersection U n i)).hom.hom.map_add _ _)
      map_smul' := fun a x => by
        funext i
        change (openSectionsIso α g M (intersection U n i)).hom
          (objectEquiv g M U n ((α a) • x) i) = _
        exact (congrArg (openSectionsIso α g M (intersection U n i)).hom
          (congrFun ((objectEquiv g M U n).map_smul (α a) x) i)).trans
            ((openSectionsIso α g M (intersection U n i)).hom.hom.map_smul a
              (objectEquiv g M U n x i)) }
  exact e.trans (objectEquiv (g ≫ Spec.map (CommRingCat.ofHom α)) M U n).symm

/-- The coefficient comparison leaves every actual original section unchanged. -/
theorem termEquiv_coordinate (n : ℕ) (x : (restrictComplex α g M U).X n)
    (i : AlgebraicGeometry.Scheme.Modules.OrderedCechIndex ι n) :
    objectEquiv (g ≫ Spec.map (CommRingCat.ofHom α)) M U n (termEquiv α g M U n x) i =
      objectEquiv g M U n x i := by
  simp only [termEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

/-- Both coefficient actions retain the same entire alternating differential. -/
theorem termEquiv_differential (n : ℕ) :
    (termEquiv α g M U n).toModuleIso.hom ≫
        (scalarComplex (g ≫ Spec.map (CommRingCat.ofHom α)) M U).d n (n + 1) =
      (restrictComplex α g M U).d n (n + 1) ≫
        (termEquiv α g M U (n + 1)).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (objectEquiv (g ≫ Spec.map (CommRingCat.ofHom α)) M U (n + 1)).injective
  funext i
  change objectEquiv (g ≫ Spec.map (CommRingCat.ofHom α)) M U (n + 1)
    ((scalarComplex (g ≫ Spec.map (CommRingCat.ofHom α)) M U).d n (n + 1)
      (termEquiv α g M U n x)) i =
    objectEquiv (g ≫ Spec.map (CommRingCat.ofHom α)) M U (n + 1)
      (termEquiv α g M U (n + 1) ((restrictComplex α g M U).d n (n + 1) x)) i
  let xB : (scalarComplex g M U).X n := x
  have hsum :
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (SchemeScalarModulePresheaf.presheaf (g ≫ Spec.map (CommRingCat.ofHom α)) M).map
          (face U n k i).op
          (objectEquiv (g ≫ Spec.map (CommRingCat.ofHom α)) M U n
            (termEquiv α g M U n x) (i.delete k))) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (SchemeScalarModulePresheaf.presheaf g M).map (face U n k i).op
          (objectEquiv g M U n xB (i.delete k)) := by
    apply Finset.sum_congr rfl
    intro k _hk
    have hcoord :
        (show Γ(M, intersection U n (i.delete k)) from
          objectEquiv (g ≫ Spec.map (CommRingCat.ofHom α)) M U n
            (termEquiv α g M U n x) (i.delete k)) =
        (show Γ(M, intersection U n (i.delete k)) from
          objectEquiv g M U n xB (i.delete k)) :=
      termEquiv_coordinate α g M U n x (i.delete k)
    exact congrArg (fun s : Γ(M, intersection U n (i.delete k)) =>
      (-1 : ℤ) ^ (k : ℕ) • M.presheaf.map (face U n k i).op s) hcoord
  have hA := differential_apply (g ≫ Spec.map (CommRingCat.ofHom α)) M U n
    (termEquiv α g M U n x) i
  have hB := differential_apply g M U n xB i
  have htarget := termEquiv_coordinate α g M U (n + 1)
    ((restrictComplex α g M U).d n (n + 1) x) i
  exact hA.trans (hsum.trans (hB.symm.trans htarget.symm))

/-- The whole actual A-linear complex is coefficient restriction of the
actual B-linear complex; all ordered maps are the original section restrictions. -/
def complexIso : restrictComplex α g M U ≅
    scalarComplex (g ≫ Spec.map (CommRingCat.ofHom α)) M U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (termEquiv α g M U n).toModuleIso)
    (fun n m hnm => by
      obtain rfl : n + 1 = m := hnm
      exact termEquiv_differential α g M U n)

/-- Original homology has exactly the arithmetic action restricted from B. -/
def homologyIso (n : ℕ) :
    (scalarComplex (g ≫ Spec.map (CommRingCat.ofHom α)) M U).homology n ≅
      (ModuleCat.restrictScalars α).obj ((scalarComplex g M U).homology n) :=
  (HomologicalComplex.homologyMapIso (complexIso α g M U) n).symm ≪≫
    ((scalarComplex g M U).sc n).mapHomologyIso (ModuleCat.restrictScalars α)

end EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyCoefficients
