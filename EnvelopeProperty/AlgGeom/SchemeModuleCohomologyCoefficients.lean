import EnvelopeProperty.AlgGeom.SchemeUnitScalarAction
import EnvelopeProperty.AlgGeom.SchemeScalarModulePresheaf
import ModularCurves.ForMathlib.SchemeModuleSheaf
import ModularCurves.ForMathlib.SheafDerivedGlobalSections
import Mathlib.Algebra.Module.ULift

/-! # Original coefficients on genuine native sheaf cohomology

The action is induced by the original whole module scalar endomorphism,
before any Cech comparison. Small and larger native Ext models are kept
explicit, with a canonical universe-lift bridge.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe w v u

namespace EnvelopeProperty.SchemeModuleCohomologyCoefficients

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

private theorem moduleHom_ext {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ (U : X.Opens) (m : Γ(M, U)), f.val.app (op U) m = g.val.app (op U) m) :
    f = g := by
  apply SheafOfModules.hom_ext
  ext U m
  exact h U.unop m

/-- The original whole scalar endomorphism, before taking cohomology. -/
def scalarEndo (p : X ⟶ Spec (.of R)) (M : X.Modules) (r : R) : M ⟶ M :=
  SchemeUnitScalarAction.globalScalarAction M (ProperBirationalSections.coefficientMap p r)

/-- Every original section is multiplied by the actual restricted coefficient of `p`. -/
theorem scalarEndo_apply (p : X ⟶ Spec (.of R)) (M : X.Modules) (r : R)
    (U : X.Opens) (m : Γ(M, U)) :
    (scalarEndo p M r).val.app (op U) m =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (ProperBirationalSections.coefficientMap p r)) • m :=
  SchemeUnitScalarAction.globalScalarAction_apply M _ U m

private theorem scalarEndo_one (p : X ⟶ Spec (.of R)) (M : X.Modules) :
    scalarEndo p M 1 = 𝟙 M := by
  apply moduleHom_ext
  intro U m
  change (scalarEndo p M 1).val.app (op U) m = m
  simp only [scalarEndo_apply, map_one, one_smul]

private theorem scalarEndo_zero (p : X ⟶ Spec (.of R)) (M : X.Modules) :
    scalarEndo p M 0 = 0 := by
  apply moduleHom_ext
  intro U m
  change (scalarEndo p M 0).val.app (op U) m = 0
  simp only [scalarEndo_apply, map_zero, zero_smul]

private theorem scalarEndo_add (p : X ⟶ Spec (.of R)) (M : X.Modules) (r s : R) :
    scalarEndo p M (r + s) = scalarEndo p M r + scalarEndo p M s := by
  apply moduleHom_ext
  intro U m
  change (scalarEndo p M (r + s)).val.app (op U) m =
    (scalarEndo p M r).val.app (op U) m + (scalarEndo p M s).val.app (op U) m
  simp only [scalarEndo_apply, map_add, add_smul]

private theorem scalarEndo_mul (p : X ⟶ Spec (.of R)) (M : X.Modules) (r s : R) :
    scalarEndo p M (r * s) = scalarEndo p M s ≫ scalarEndo p M r := by
  apply moduleHom_ext
  intro U m
  change (scalarEndo p M (r * s)).val.app (op U) m =
    (scalarEndo p M r).val.app (op U) ((scalarEndo p M s).val.app (op U) m)
  simp only [scalarEndo_apply, map_mul, mul_smul]

/-- The original coefficient action is an actual ring homomorphism into module endomorphisms. -/
def scalarEndoRingHom (p : X ⟶ Spec (.of R)) (M : X.Modules) : R →+* CategoryTheory.End M where
  toFun := scalarEndo p M
  map_one' := scalarEndo_one p M
  map_zero' := scalarEndo_zero p M
  map_add' := scalarEndo_add p M
  map_mul' := scalarEndo_mul p M

/-- Every original module map commutes with the entire original scalar action. -/
theorem scalarEndo_naturality (p : X ⟶ Spec (.of R)) {M N : X.Modules}
    (f : M ⟶ N) (r : R) : scalarEndo p M r ≫ f = f ≫ scalarEndo p N r := by
  apply moduleHom_ext
  intro U m
  change f.val.app (op U) ((scalarEndo p M r).val.app (op U) m) =
    (scalarEndo p N r).val.app (op U) (f.val.app (op U) m)
  rw [scalarEndo_apply, scalarEndo_apply]
  exact (f.val.app (op U)).hom.map_smul _ _

@[instance_reducible]
private def moduleOfFunctor (p : X ⟶ Spec (.of R))
    (F : X.Modules ⥤ AddCommGrpCat.{v}) [F.Additive] (M : X.Modules) :
    Module R (F.obj M) where
  smul r x := F.map (scalarEndo p M r) x
  one_smul x := by
    change F.map (scalarEndo p M 1) x = x
    rw [scalarEndo_one, F.map_id]; rfl
  mul_smul r s x := by
    change F.map (scalarEndo p M (r * s)) x =
      F.map (scalarEndo p M r) (F.map (scalarEndo p M s) x)
    rw [scalarEndo_mul, F.map_comp]; rfl
  smul_zero r := (F.map (scalarEndo p M r)).hom.map_zero
  smul_add r x y := (F.map (scalarEndo p M r)).hom.map_add x y
  zero_smul x := by
    change F.map (scalarEndo p M 0) x = 0
    rw [scalarEndo_zero, F.map_zero]; rfl
  add_smul r s x := by
    change F.map (scalarEndo p M (r + s)) x =
      F.map (scalarEndo p M r) x + F.map (scalarEndo p M s) x
    rw [scalarEndo_add, F.map_add]; rfl

private def linearMapOfFunctor (p : X ⟶ Spec (.of R))
    (F : X.Modules ⥤ AddCommGrpCat.{v}) [F.Additive] {M N : X.Modules} (f : M ⟶ N) :
    letI := moduleOfFunctor p F M
    letI := moduleOfFunctor p F N
    F.obj M →ₗ[R] F.obj N := by
  letI := moduleOfFunctor p F M
  letI := moduleOfFunctor p F N
  exact
    { toFun := F.map f
      map_add' := (F.map f).hom.map_add
      map_smul' := fun r x => by
        have h := congrArg F.map (scalarEndo_naturality p f r)
        rw [F.map_comp, F.map_comp] at h
        exact ConcreteCategory.congr_hom h x }

private theorem largerHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

attribute [local instance] largerHasExt

/-- The genuine larger native `Sheaf.H`, with its universe stated explicitly. -/
abbrev nativeH (M : X.Modules) (q : ℕ) : Type (u + 1) :=
  CategoryTheory.Sheaf.H.{u + 1} M.sheaf q

private abbrev smallFunctor (X : Scheme.{u}) (q : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toSheaf X ⋙
    CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) q

private abbrev nativeFunctor (X : Scheme.{u}) (q : ℕ) :
    X.Modules ⥤ AddCommGrpCat.{u + 1} :=
  Scheme.Modules.toSheaf X ⋙
    CategoryTheory.Sheaf.functorH.{u + 1} (Opens.grothendieckTopology X) q

private theorem smallFunctor_additive (X : Scheme.{u}) (q : ℕ) :
    (smallFunctor X q).Additive := by
  constructor
  intro M N f g
  change (CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) q).map
    ((Scheme.Modules.toSheaf X).map (f + g)) = _
  rw [Functor.map_add, Functor.map_add]
  rfl

private theorem nativeFunctor_additive (X : Scheme.{u}) (q : ℕ) :
    (nativeFunctor X q).Additive := by
  constructor
  intro M N f g
  change (CategoryTheory.Sheaf.functorH.{u + 1} (Opens.grothendieckTopology X) q).map
    ((Scheme.Modules.toSheaf X).map (f + g)) = _
  rw [Functor.map_add, Functor.map_add]
  rfl

attribute [local instance] smallFunctor_additive nativeFunctor_additive

/-- The actual small native Ext group with the original coefficient action. -/
def smallModule (p : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) : ModuleCat.{u} R := by
  letI := moduleOfFunctor p (smallFunctor X q) M
  exact ModuleCat.of R ((smallFunctor X q).obj M)

/-- The actual larger native Ext group with the independently constructed original action. -/
def nativeModule (p : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) : ModuleCat.{u + 1} R := by
  letI := moduleOfFunctor p (nativeFunctor X q) M
  exact ModuleCat.of R ((nativeFunctor X q).obj M)

/-- The action on the larger native group is exactly the genuine cohomology scalar map. -/
theorem nativeModule_smul (p : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ)
    (r : R) (x : nativeModule p M q) :
    r • x = CategoryTheory.Sheaf.H.map.{u + 1}
      ((Scheme.Modules.toSheaf X).map (scalarEndo p M r)) q x := rfl

/-- Original module maps act linearly on the actual small native group. -/
def smallMap (p : X ⟶ Spec (.of R)) {M N : X.Modules} (f : M ⟶ N) (q : ℕ) :
    smallModule p M q →ₗ[R] smallModule p N q :=
  linearMapOfFunctor p (smallFunctor X q) f

/-- Original module maps act linearly on the genuine larger native group. -/
def nativeMap (p : X ⟶ Spec (.of R)) {M N : X.Modules} (f : M ⟶ N) (q : ℕ) :
    nativeModule p M q →ₗ[R] nativeModule p N q :=
  linearMapOfFunctor p (nativeFunctor X q) f

/-- The entire linear map retains the original native cohomology map. -/
theorem nativeMap_apply (p : X ⟶ Spec (.of R)) {M N : X.Modules} (f : M ⟶ N)
    (q : ℕ) (x : nativeModule p M q) :
    nativeMap p f q x = CategoryTheory.Sheaf.H.map.{u + 1}
      ((Scheme.Modules.toSheaf X).map f) q x := rfl

private theorem changeUniverse_add {C : Type v} [Category.{w} C] [Abelian C]
    [HasExt.{u} C] [HasExt.{u + 1} C] {A B : C} {q : ℕ}
    (x y : Abelian.Ext.{u} A B q) :
    Abelian.Ext.chgUniv.{u + 1, u} (x + y) =
      Abelian.Ext.chgUniv.{u + 1, u} x + Abelian.Ext.chgUniv.{u + 1, u} y := by
  let := HasDerivedCategory.standard C
  apply (Abelian.Ext.homEquiv).injective
  rw [Abelian.Ext.homEquiv_chgUniv]
  change (x + y).hom = (Abelian.Ext.chgUniv x + Abelian.Ext.chgUniv y).hom
  rw [Abelian.Ext.add_hom, Abelian.Ext.add_hom]
  exact congrArg₂ (fun a b => a + b)
    (Abelian.Ext.homEquiv_chgUniv x).symm (Abelian.Ext.homEquiv_chgUniv y).symm

private theorem changeUniverse_postcomp {C : Type v} [Category.{w} C] [Abelian C]
    [HasExt.{u} C] [HasExt.{u + 1} C] {A B D : C} {q : ℕ}
    (f : B ⟶ D) (x : Abelian.Ext.{u} A B q) :
    Abelian.Ext.chgUniv.{u + 1, u} (x.comp (Abelian.Ext.mk₀ f) (add_zero q)) =
      (Abelian.Ext.chgUniv.{u + 1, u} x).comp (Abelian.Ext.mk₀ f) (add_zero q) := by
  let := HasDerivedCategory.standard C
  apply (Abelian.Ext.homEquiv).injective
  rw [Abelian.Ext.homEquiv_chgUniv]
  change (x.comp (Abelian.Ext.mk₀ f) (add_zero q)).hom =
    ((Abelian.Ext.chgUniv x).comp (Abelian.Ext.mk₀ f) (add_zero q)).hom
  rw [Abelian.Ext.comp_hom, Abelian.Ext.comp_hom,
    Abelian.Ext.mk₀_hom, Abelian.Ext.mk₀_hom]
  congr 1
  exact (Abelian.Ext.homEquiv_chgUniv x).symm

/-- Canonical native Ext universe change, retaining the original cohomology classes. -/
def universeAddEquiv (M : X.Modules) (q : ℕ) :
    CategoryTheory.Sheaf.H.{u} M.sheaf q ≃+ nativeH M q where
  toEquiv := Abelian.Ext.chgUniv.{u + 1, u}
  map_add' x y := changeUniverse_add
    (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) x y

/-- Native universe change commutes with every original module cohomology map. -/
theorem universeAddEquiv_naturality {M N : X.Modules} (f : M ⟶ N) (q : ℕ)
    (x : CategoryTheory.Sheaf.H.{u} M.sheaf q) :
    universeAddEquiv N q (CategoryTheory.Sheaf.H.map.{u}
      ((Scheme.Modules.toSheaf X).map f) q x) =
      CategoryTheory.Sheaf.H.map.{u + 1} ((Scheme.Modules.toSheaf X).map f) q
        (universeAddEquiv M q x) :=
  changeUniverse_postcomp
    (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((Scheme.Modules.toSheaf X).map f) x

/-- Universe change is linear for the independently constructed original actions. -/
def universeLinearEquiv (p : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    smallModule p M q ≃ₗ[R] nativeModule p M q where
  toAddEquiv := universeAddEquiv M q
  map_smul' r x := universeAddEquiv_naturality (scalarEndo p M r) q x

/-- The actual larger native group is linearly equivalent to the lifted small group. -/
def liftedUniverseLinearEquiv (p : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ) :
    ULift.{u + 1} (smallModule p M q) ≃ₗ[R] nativeModule p M q :=
  ULift.moduleEquiv.trans (universeLinearEquiv p M q)

/-- A lifted original class is sent to its canonical native change-of-universe class. -/
theorem liftedUniverseLinearEquiv_apply (p : X ⟶ Spec (.of R)) (M : X.Modules) (q : ℕ)
    (x : ULift.{u + 1} (smallModule p M q)) :
    liftedUniverseLinearEquiv p M q x = Abelian.Ext.chgUniv.{u + 1, u} x.down := rfl

/-- The entire universe-change linear square commutes for every original module map. -/
theorem universeLinearEquiv_naturality (p : X ⟶ Spec (.of R)) {M N : X.Modules}
    (f : M ⟶ N) (q : ℕ) :
    (universeLinearEquiv p N q).toLinearMap.comp (smallMap p f q) =
      (nativeMap p f q).comp (universeLinearEquiv p M q).toLinearMap := by
  ext x
  exact universeAddEquiv_naturality f q x

end EnvelopeProperty.SchemeModuleCohomologyCoefficients
