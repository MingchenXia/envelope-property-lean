/-
Mathlib-only proof port. Original source: EnvelopeProperty/ComplexGeometry/Schemes/CotangentAffineComparison.lean
Upstream SHA256: afb504247603e7c7ccbd07a222b1e577d2d0078fdabee776936552e2d0ab376f
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import EnvelopeProperty.AlgGeom.Canonical.CotangentSheaf
import EnvelopeProperty.AlgGeom.Canonical.SmoothCanonicalCharts
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Affine comparison for the actual cotangent sheaf

Compare canonical localized differential modules on principal opens, extend
along this dense basis, and use the genuine sheafification universal property.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite PrimeSpectrum
open TensorProduct

namespace EnvelopeProperty.CanonicalGeometry

universe u

variable (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]

/-- The coordinate-algebra structure map. -/
def affineBaseRingMap : CommRingCat.of K ⟶ A := CommRingCat.ofHom (algebraMap K A)

/-- The actual structural morphism of the affine scheme. -/
noncomputable def affineStructuralMap : Spec A ⟶ Spec (.of K) :=
  Spec.map (affineBaseRingMap K A)

/-- The actual relative Kähler module of the coordinate-algebra map. -/
noncomputable def affineCotangentModule : ModuleCat A :=
  CommRingCat.KaehlerDifferential (affineBaseRingMap K A)

/-- Its associated sheaf on the affine scheme. -/
noncomputable def affineCotangentTilde : (Spec A).Modules :=
  AlgebraicGeometry.tilde (affineCotangentModule K A)

/-- The actual coordinate-algebra constants on an arbitrary open set. -/
noncomputable def affineCoordinateMap (U : (Spec A).Opensᵒᵖ) :
    A ⟶ (Spec A).presheaf.obj U :=
  (Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.map U.unop.leTop.op

/-- Coordinate constants commute with restriction. -/
theorem affineCoordinateMap_naturality {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V) :
    affineCoordinateMap A U ≫ (Spec A).presheaf.map i = affineCoordinateMap A V := by
  simp only [affineCoordinateMap, Category.assoc, ← Functor.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- A presheaf of structure modules viewed directly as coordinate-algebra
modules, using the genuine coordinate constants at each open. -/
noncomputable def specPresheafToAModules (P : (Spec A).PresheafOfModules) :
    TopCat.Presheaf (ModuleCat A) (Spec A) where
  obj U := (ModuleCat.restrictScalars (affineCoordinateMap A U).hom).obj (P.obj U)
  map {U V} i := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (affineCoordinateMap A U).hom).obj (P.obj U))
    (Y := (ModuleCat.restrictScalars (affineCoordinateMap A V).hom).obj (P.obj V))
    { toFun := fun x ↦ P.map i x
      map_add' := (P.map i).hom.map_add
      map_smul' a x := by
        change P.map i ((affineCoordinateMap A U a) • x) =
          (affineCoordinateMap A V a) • P.map i x
        rw [P.map_smul]
        congr 1
        }
  map_id U := by ext x; simp
  map_comp i j := by ext x; exact P.map_comp_apply i j x

/-- The actual cotangent presheaf with its direct affine scalar action. -/
noncomputable def affineCotangentAPresheaf :
    TopCat.Presheaf (ModuleCat A) (Spec A) :=
  specPresheafToAModules A (cotangentPresheaf (affineStructuralMap K A))

/-- The actual structural constant square commutes on each open set. -/
theorem affineBaseRingMap_coordinateMap (U : (Spec A).Opensᵒᵖ) :
    affineBaseRingMap K A ≫ affineCoordinateMap A U =
      (schemeConstantPresheafMap (affineStructuralMap K A)).app U := by
  simp only [schemeConstantPresheafMap, affineStructuralMap, affineCoordinateMap]
  rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical relative differential map from the affine coordinate
algebra into the actual cotangent presheaf on each open set. -/
noncomputable def affineCotangentToOpen (U : (Spec A).Opensᵒᵖ) :
    affineCotangentModule K A ⟶ (affineCotangentAPresheaf K A).obj U :=
  CommRingCat.KaehlerDifferential.map
    (f := affineBaseRingMap K A)
    (f' := (schemeConstantPresheafMap (affineStructuralMap K A)).app U)
    (g := 𝟙 (CommRingCat.of K))
    (g' := affineCoordinateMap A U)
    (by simpa using (affineBaseRingMap_coordinateMap K A U).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate differential map is canonical on the generators `da`. -/
theorem affineCotangentToOpen_d (U : (Spec A).Opensᵒᵖ) (a : A) :
    affineCotangentToOpen K A U (CommRingCat.KaehlerDifferential.d a) =
      (cotangentPresheafDerivation (affineStructuralMap K A)).d
        (affineCoordinateMap A U a) :=
  CommRingCat.KaehlerDifferential.map_d _ a

set_option backward.isDefEq.respectTransparency false in
/-- The canonical maps of differential modules commute with restrictions
on arbitrary open sets. -/
theorem affineCotangentToOpen_naturality {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V) :
    affineCotangentToOpen K A U ≫ (affineCotangentAPresheaf K A).map i =
      affineCotangentToOpen K A V := by
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  change (cotangentPresheaf (affineStructuralMap K A)).map i
      (affineCotangentToOpen K A U (CommRingCat.KaehlerDifferential.d a)) =
    affineCotangentToOpen K A V (CommRingCat.KaehlerDifferential.d a)
  rw [affineCotangentToOpen_d, affineCotangentToOpen_d]
  exact ((cotangentPresheafDerivation (affineStructuralMap K A)).d_map i
      (affineCoordinateMap A U a)).symm.trans
    (congrArg (cotangentPresheafDerivation (affineStructuralMap K A)).d
      (congr($(affineCoordinateMap_naturality A i) a)))

set_option backward.isDefEq.respectTransparency false in
/-- On a principal open, the actual cotangent restriction is the localized
coordinate differential module through its canonical differential map. -/
theorem affineCotangentToOpen_isLocalized (r : A) :
    IsLocalizedModule (.powers r)
      (affineCotangentToOpen K A (.op (basicOpen r))).hom := by
  have hloc : IsLocalization (.powers r) Γ(Spec A, basicOpen r) := inferInstance
  let U : (Spec A).Opensᵒᵖ := .op (basicOpen r)
  let f : CommRingCat.of K ⟶ A := affineBaseRingMap K A
  let f' : CommRingCat.of K ⟶ (Spec A).presheaf.obj U :=
    (schemeConstantPresheafMap (affineStructuralMap K A)).app U
  let g' := affineCoordinateMap A U
  let : Algebra K A := f.hom.toAlgebra
  let : Algebra K ((Spec A).presheaf.obj U) := f'.hom.toAlgebra
  let : Algebra A ((Spec A).presheaf.obj U) := g'.hom.toAlgebra
  have : IsScalarTower K A ((Spec A).presheaf.obj U) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom
      (affineBaseRingMap_coordinateMap K A U)).symm
  have : IsLocalization (.powers r) ((Spec A).presheaf.obj U) := by
    convert! hloc using 1
    apply Algebra.algebra_ext
    intro a
    rfl
  change IsLocalizedModule (.powers r)
    (_root_.KaehlerDifferential.map K K A ((Spec A).presheaf.obj U))
  infer_instance

end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
variable (A : CommRingCat.{u})

set_option backward.isDefEq.respectTransparency false in
/-- Forget a structure-module presheaf map using the actual affine
coordinate scalar actions. -/
noncomputable def specPresheafAModuleMap
    {P Q : (Spec A).PresheafOfModules} (f : P ⟶ Q) :
    specPresheafToAModules A P ⟶ specPresheafToAModules A Q where
  app U := ModuleCat.ofHom
    (X := (specPresheafToAModules A P).obj U)
    (Y := (specPresheafToAModules A Q).obj U)
    { toFun := f.app U
      map_add' := (f.app U).hom.map_add
      map_smul' a x := (f.app U).hom.map_smul (affineCoordinateMap A U a) x }
  naturality {U V} i := by ext x; exact congr($(f.naturality i).hom x)

end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
variable (A : CommRingCat.{u})

set_option backward.isDefEq.respectTransparency false in
/-- The direct coordinate action agrees with the native affine sheaf
forgetful functor. -/
theorem specPresheafToAModules_sheaf (N : (Spec A).Modules) :
    specPresheafToAModules A N.val = (modulesSpecToSheaf.obj N).obj := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A natural affine coordinate-module map into an actual structure-module
sheaf is automatically linear over all rings of regular functions. -/
noncomputable def affinePresheafHomOfAModuleHom
    (P : (Spec A).PresheafOfModules) (N : (Spec A).Modules)
    (f : specPresheafToAModules A P ⟶ (modulesSpecToSheaf.obj N).obj) :
    P ⟶ N.val where
  app U := ModuleCat.ofHom (X := P.obj U) (Y := N.val.obj U)
    ⟨(f.app U).hom.toAddHom, by
    intro t m
    apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj N).2
    intro x hxU
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU : basicOpen _ ≤ _⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.unop.2
    refine ⟨_, hrU, hxr, ?_⟩
    refine Eq.trans ?_ (N.val.map_smul (homOfLE hrU).op t _).symm
    change N.val.map (homOfLE hrU).op (f.app _ _) =
      _ • N.val.map (homOfLE hrU).op (f.app _ _)
    have (z : _) : f.app _ (P.map (homOfLE hrU).op z) =
        N.val.map (homOfLE hrU).op (f.app _ z) :=
      congr($(f.naturality (homOfLE hrU).op).hom z)
    rw [← this, ← this, P.map_smul]
    generalize (Spec A).ringCatSheaf.obj.map (homOfLE hrU).op t = t
    let := Module.compHom (R := Γ(Spec A, basicOpen r))
      (P.obj (.op (basicOpen r))) (algebraMap A Γ(Spec A, basicOpen r))
    have : IsScalarTower A Γ(Spec A, basicOpen r) (P.obj (.op (basicOpen r))) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    let := Module.compHom Γ(N, basicOpen r) (algebraMap A Γ(Spec A, basicOpen r))
    have : IsScalarTower A Γ(Spec A, basicOpen r) Γ(N, basicOpen r) :=
      .of_algebraMap_smul fun _ _ ↦ rfl
    exact (IsLocalization.linearMap_compatibleSMul (.powers (M := A) r)
      Γ(Spec A, basicOpen r) (P.obj (.op (basicOpen r))) Γ(N, basicOpen r)).map_smul
      (f.app _).hom _ _⟩
  naturality i := by ext x; exact congr($(f.naturality i).hom x)

set_option backward.isDefEq.respectTransparency false in
/-- Canonical localized coordinate modules give a natural comparison with
the associated sheaf on the actual principal-open basis. -/
noncomputable def affineLocalizedBasisHom
    (P : (Spec A).PresheafOfModules) (M : ModuleCat A)
    (φ : (U : (Spec A).Opensᵒᵖ) → M ⟶ (specPresheafToAModules A P).obj U)
    (hφ : ∀ {U V} (i : U ⟶ V), φ U ≫ (specPresheafToAModules A P).map i = φ V)
    (hloc : ∀ r : A, IsLocalizedModule (.powers r) (φ (.op (basicOpen r))).hom) :
    (inducedFunctor (basicOpen (R := A))).op ⋙ specPresheafToAModules A P ⟶
      (inducedFunctor (basicOpen (R := A))).op ⋙
        (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).obj where
  app (r : Aᵒᵖ) := by
    let := hloc r.unop
    exact ModuleCat.ofHom
      (X := (specPresheafToAModules A P).obj (.op (basicOpen r.unop)))
      (Y := (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).obj.obj
        (.op (basicOpen r.unop)))
      (IsLocalizedModule.linearEquiv (.powers r.unop)
        (φ (.op (basicOpen r.unop))).hom (tilde.toOpen M (basicOpen r.unop)).hom).toLinearMap
  naturality {r s : Aᵒᵖ} i := by
    let := hloc r.unop
    let := hloc s.unop
    ext1
    apply IsLocalizedModule.ext (.powers r.unop) (φ (.op (basicOpen r.unop))).hom
    · rw [Subtype.forall]
      change Submonoid.powers _ ≤ (IsUnit.submonoid _).comap _
      simp only [Submonoid.powers_le, Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact (AlgebraicGeometry.tilde M).isUnit_algebraMap_end_of_le_basicOpen r.unop
        (i.1.hom).le
    · ext x
      change (IsLocalizedModule.linearEquiv (.powers s.unop)
          (φ (.op (basicOpen s.unop))).hom (tilde.toOpen M (basicOpen s.unop)).hom)
          ((specPresheafToAModules A P).map
            (i.1.hom).op
            (φ (.op (basicOpen r.unop)) x)) =
        (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).obj.map
          (i.1.hom).op
          ((IsLocalizedModule.linearEquiv (.powers r.unop)
            (φ (.op (basicOpen r.unop))).hom (tilde.toOpen M (basicOpen r.unop)).hom)
            (φ (.op (basicOpen r.unop)) x))
      have hx : (specPresheafToAModules A P).map (i.1.hom).op
          (φ (.op (basicOpen r.unop)) x) = φ (.op (basicOpen s.unop)) x :=
        congr($(hφ (i.1.hom).op).hom x)
      rw [hx, IsLocalizedModule.linearEquiv_apply, IsLocalizedModule.linearEquiv_apply]
      exact congr($(tilde.toOpen_res M (basicOpen r.unop) (basicOpen s.unop)
        (i.1.hom)) x).symm

end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
variable (A : CommRingCat.{u})

set_option backward.isDefEq.respectTransparency false in
/-- Extend a principal-open coordinate-module map into an actual sheaf,
then derive linearity over regular functions. -/
noncomputable def affineBasisExtend
    (P : (Spec A).PresheafOfModules) (N : (Spec A).Modules)
    (α : (inducedFunctor (basicOpen (R := A))).op ⋙ specPresheafToAModules A P ⟶
      (inducedFunctor (basicOpen (R := A))).op ⋙ (modulesSpecToSheaf.obj N).obj) :
    P ⟶ N.val :=
  affinePresheafHomOfAModuleHom A P N
    (TopCat.Sheaf.restrictHomEquivHom _ _ isBasis_basic_opens α)

set_option backward.isDefEq.respectTransparency false in
/-- The actual dense-basis extension retains its prescribed principal-open
components. -/
theorem affineBasisExtend_apply
    (P : (Spec A).PresheafOfModules) (N : (Spec A).Modules)
    (α : (inducedFunctor (basicOpen (R := A))).op ⋙ specPresheafToAModules A P ⟶
      (inducedFunctor (basicOpen (R := A))).op ⋙ (modulesSpecToSheaf.obj N).obj)
    (r : A) (x : P.obj (.op (basicOpen r))) :
    (affineBasisExtend A P N α).app (.op (basicOpen r)) x = α.app (.op r) x := by
  change (TopCat.Sheaf.restrictHomEquivHom _ _ isBasis_basic_opens α).app
      (.op (basicOpen r)) x = α.app (.op r) x
  exact congr($(TopCat.Sheaf.extend_hom_app (specPresheafToAModules A P)
    (modulesSpecToSheaf.obj N) isBasis_basic_opens α r).hom x)

set_option backward.isDefEq.respectTransparency false in
/-- Actual module presheaf maps into a sheaf are determined on principal opens. -/
theorem affineBasisHomExt (P : (Spec A).PresheafOfModules) (N : (Spec A).Modules)
    {f g : P ⟶ N.val}
    (h : ∀ r : A, f.app (.op (basicOpen r)) = g.app (.op (basicOpen r))) : f = g := by
  have he : specPresheafAModuleMap A f = specPresheafAModuleMap A g :=
    TopCat.Sheaf.hom_ext (specPresheafToAModules A P)
      (modulesSpecToSheaf.obj N) isBasis_basic_opens (fun r ↦ by
        ext x
        exact congr($(h r).hom x))
  ext U x
  exact congr($(he).app U |>.hom x)

variable (P : (Spec A).PresheafOfModules) (M : ModuleCat A)
variable (φ : (U : (Spec A).Opensᵒᵖ) → M ⟶ (specPresheafToAModules A P).obj U)
variable (hφ : ∀ {U V} (i : U ⟶ V), φ U ≫ (specPresheafToAModules A P).map i = φ V)
variable (hloc : ∀ r : A, IsLocalizedModule (.powers r) (φ (.op (basicOpen r))).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical principal-open comparison is a genuine natural isomorphism. -/
noncomputable def affineLocalizedBasisIso :
    (inducedFunctor (basicOpen (R := A))).op ⋙ specPresheafToAModules A P ≅
      (inducedFunctor (basicOpen (R := A))).op ⋙
        (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).obj :=
  NatIso.ofComponents
    (fun (r : Aᵒᵖ) ↦ by
      let := hloc r.unop
      exact LinearEquiv.toModuleIso
        (X₁ := (specPresheafToAModules A P).obj (.op (basicOpen r.unop)))
        (X₂ := (modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).obj.obj
          (.op (basicOpen r.unop)))
        (IsLocalizedModule.linearEquiv (.powers r.unop)
          (φ (.op (basicOpen r.unop))).hom (tilde.toOpen M (basicOpen r.unop)).hom))
    (fun i ↦ (affineLocalizedBasisHom A P M φ hφ hloc).naturality i)

/-- The actual structure-module sheafification of an affine presheaf. -/
noncomputable def affinePresheafSheafification : (Spec A).Modules :=
  (PresheafOfModules.sheafification (𝟙 (Spec A).ringCatSheaf.obj)).obj P

/-- Its canonical sheafification map. -/
noncomputable def affinePresheafSheafificationUnit :
    P ⟶ (affinePresheafSheafification A P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (Spec A).ringCatSheaf.obj)).unit.app P

/-- The actual presheaf comparison obtained from localized coordinate modules. -/
noncomputable def affineLocalizedPresheafHom : P ⟶ (AlgebraicGeometry.tilde M).val :=
  affineBasisExtend A P (AlgebraicGeometry.tilde M)
    (affineLocalizedBasisIso A P M φ hφ hloc).hom

/-- The actual sheaf map given by the sheafification universal property. -/
noncomputable def affineLocalizedSheafificationHom :
    affinePresheafSheafification A P ⟶ AlgebraicGeometry.tilde M :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (Spec A).ringCatSheaf.obj)).symm
    (affineLocalizedPresheafHom A P M φ hφ hloc)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse map extends the canonical basis inverse followed by the
actual sheafification unit. -/
noncomputable def affineLocalizedSheafificationInv :
    AlgebraicGeometry.tilde M ⟶ affinePresheafSheafification A P :=
  ⟨affineBasisExtend A (AlgebraicGeometry.tilde M).val
    (affinePresheafSheafification A P)
    ((affineLocalizedBasisIso A P M φ hφ hloc).inv ≫
      Functor.whiskerLeft (inducedFunctor (basicOpen (R := A))).op
        (specPresheafAModuleMap A (affinePresheafSheafificationUnit A P)))⟩

end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
variable (A : CommRingCat.{u}) (P : (Spec A).PresheafOfModules) (M : ModuleCat A)
variable (φ : (U : (Spec A).Opensᵒᵖ) → M ⟶ (specPresheafToAModules A P).obj U)
variable (hφ : ∀ {U V} (i : U ⟶ V), φ U ≫ (specPresheafToAModules A P).map i = φ V)
variable (hloc : ∀ r : A, IsLocalizedModule (.powers r) (φ (.op (basicOpen r))).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf comparison factors its actual presheaf comparison. -/
theorem affineLocalizedSheafificationHom_fac :
    affinePresheafSheafificationUnit A P ≫
      (affineLocalizedSheafificationHom A P M φ hφ hloc).val =
        affineLocalizedPresheafHom A P M φ hφ hloc := by
  have h := Equiv.apply_symm_apply
    (PresheafOfModules.sheafificationHomEquiv (P := P)
      (F := AlgebraicGeometry.tilde M) (𝟙 (Spec A).ringCatSheaf.obj))
    (affineLocalizedPresheafHom A P M φ hφ hloc)
  rw [← PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    Adjunction.homEquiv_unit] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual sheaf map is the canonical localized comparison on the images
of the sheafification unit over each principal open. -/
theorem affineLocalizedSheafificationHom_unit_apply (r : A)
    (x : P.obj (.op (basicOpen r))) :
    (affineLocalizedSheafificationHom A P M φ hφ hloc).val.app (.op (basicOpen r))
      ((affinePresheafSheafificationUnit A P).app (.op (basicOpen r)) x) =
        (affineLocalizedBasisIso A P M φ hφ hloc).hom.app (.op r) x := by
  calc
    _ = (affineLocalizedPresheafHom A P M φ hφ hloc).app (.op (basicOpen r)) x :=
      congr($(affineLocalizedSheafificationHom_fac A P M φ hφ hloc).app
        (.op (basicOpen r)) |>.hom x)
    _ = _ := affineBasisExtend_apply A P (AlgebraicGeometry.tilde M) _ r x

set_option backward.isDefEq.respectTransparency false in
/-- The inverse retains the genuine basis inverse followed by the unit. -/
theorem affineLocalizedSheafificationInv_apply (r : A)
    (x : Γ(AlgebraicGeometry.tilde M, basicOpen r)) :
    (affineLocalizedSheafificationInv A P M φ hφ hloc).val.app (.op (basicOpen r)) x =
      (affinePresheafSheafificationUnit A P).app (.op (basicOpen r))
        ((affineLocalizedBasisIso A P M φ hφ hloc).inv.app (.op r) x) := by
  change (affineBasisExtend A (AlgebraicGeometry.tilde M).val
    (affinePresheafSheafification A P) _).app (.op (basicOpen r)) x = _
  rw [affineBasisExtend_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The two actual comparison maps compose to the identity on the genuine
sheafification; dense-basis separation and its adjunction prove the result. -/
theorem affineLocalizedSheafificationHom_inv_id :
    affineLocalizedSheafificationHom A P M φ hφ hloc ≫
      affineLocalizedSheafificationInv A P M φ hφ hloc =
        𝟙 (affinePresheafSheafification A P) := by
  apply (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec A).ringCatSheaf.obj)).homEquiv P (affinePresheafSheafification A P) |>.injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change affinePresheafSheafificationUnit A P ≫
      ((affineLocalizedSheafificationHom A P M φ hφ hloc).val ≫
        (affineLocalizedSheafificationInv A P M φ hφ hloc).val) =
    affinePresheafSheafificationUnit A P ≫ 𝟙 _
  rw [Category.comp_id]
  apply affineBasisHomExt A P (affinePresheafSheafification A P)
  intro r
  ext x
  change (affineLocalizedSheafificationInv A P M φ hφ hloc).val.app (.op (basicOpen r))
      ((affineLocalizedSheafificationHom A P M φ hφ hloc).val.app (.op (basicOpen r))
        ((affinePresheafSheafificationUnit A P).app (.op (basicOpen r)) x)) =
    (affinePresheafSheafificationUnit A P).app (.op (basicOpen r)) x
  rw [affineLocalizedSheafificationHom_unit_apply, affineLocalizedSheafificationInv_apply]
  apply congrArg ((affinePresheafSheafificationUnit A P).app (.op (basicOpen r)))
  exact congr($( (affineLocalizedBasisIso A P M φ hφ hloc).hom_inv_id).app (.op r) |>.hom x)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse composite is the identity on the genuine associated sheaf. -/
theorem affineLocalizedSheafificationInv_hom_id :
    affineLocalizedSheafificationInv A P M φ hφ hloc ≫
      affineLocalizedSheafificationHom A P M φ hφ hloc =
        𝟙 (AlgebraicGeometry.tilde M) := by
  apply (Scheme.Modules.toPresheafOfModules (Spec A)).map_injective
  change (affineLocalizedSheafificationInv A P M φ hφ hloc).val ≫
    (affineLocalizedSheafificationHom A P M φ hφ hloc).val = 𝟙 _
  apply affineBasisHomExt A (AlgebraicGeometry.tilde M).val (AlgebraicGeometry.tilde M)
  intro r
  ext x
  change (affineLocalizedSheafificationHom A P M φ hφ hloc).val.app (.op (basicOpen r))
      ((affineLocalizedSheafificationInv A P M φ hφ hloc).val.app (.op (basicOpen r)) x) = x
  rw [affineLocalizedSheafificationInv_apply, affineLocalizedSheafificationHom_unit_apply]
  exact congr($( (affineLocalizedBasisIso A P M φ hφ hloc).inv_hom_id).app (.op r) |>.hom x)

/-- Genuine affine associated-sheaf comparison derived from canonical
localized module maps and their restriction naturality. -/
noncomputable def affineLocalizedSheafificationIso :
    affinePresheafSheafification A P ≅ AlgebraicGeometry.tilde M where
  hom := affineLocalizedSheafificationHom A P M φ hφ hloc
  inv := affineLocalizedSheafificationInv A P M φ hφ hloc
  hom_inv_id := affineLocalizedSheafificationHom_inv_id A P M φ hφ hloc
  inv_hom_id := affineLocalizedSheafificationInv_hom_id A P M φ hφ hloc

end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
variable (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]

/-- The actual affine cotangent sheaf agrees with the associated sheaf of
the coordinate-algebra Kähler module. -/
noncomputable def affineCotangentSheafIso :
    cotangentSheaf (affineStructuralMap K A) ≅ affineCotangentTilde K A :=
  affineLocalizedSheafificationIso A (cotangentPresheaf (affineStructuralMap K A))
    (affineCotangentModule K A) (affineCotangentToOpen K A)
    (fun i ↦ affineCotangentToOpen_naturality K A i)
    (affineCotangentToOpen_isLocalized K A)

set_option backward.isDefEq.respectTransparency false in
/-- Native categorical coordinate differentials agree with the ordinary
Kähler module for the given coordinate-algebra structure. -/
noncomputable def affineCotangentModuleIso :
    affineCotangentModule K A ≅ ModuleCat.of A (KaehlerDifferential K A) := by
  let F : Algebra K A → ModuleCat A := fun a ↦
    letI := a
    ModuleCat.of A (KaehlerDifferential K A)
  exact eqToIso (congrArg F (toAlgebra_algebraMap (R := K) (S := A)))

/-- A genuine standard smooth presentation produces the coordinate module
frame, without any prescribed differential basis. -/
noncomputable def standardSmoothAffineCotangentModuleFrame (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    affineCotangentModule K A ≅ ModuleCat.of A (ULift.{u} (Fin n) →₀ A) :=
  affineCotangentModuleIso K A ≪≫
    ((standardSmoothDifferentialBasis K A n).reindex Equiv.ulift.symm).repr.toModuleIso

/-- A genuine standard smooth presentation trivializes the actual affine
cotangent sheaf as the free structure-module sheaf on `n` generators. -/
noncomputable def standardSmoothAffineCotangentSheafFrame (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    cotangentSheaf (affineStructuralMap K A) ≅
      SheafOfModules.free (R := (Spec A).ringCatSheaf) (ULift.{u} (Fin n)) :=
  affineCotangentSheafIso K A ≪≫
    (tilde.functor A).mapIso (standardSmoothAffineCotangentModuleFrame K A n) ≪≫
      tildeFinsupp (ULift.{u} (Fin n))

end EnvelopeProperty.CanonicalGeometry

namespace EnvelopeProperty.CanonicalGeometry
universe u
variable (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine cotangent sheaf of a standard smooth algebra is
locally free, derived from its genuine free-sheaf frame. -/
theorem standardSmoothAffineCotangentSheaf_locallyFree (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] :
    (cotangentSheaf (affineStructuralMap K A)).IsLocallyFree := by
  let e := standardSmoothAffineCotangentSheafFrame K A n
  let G := (SheafOfModules.free.generatingSections
    (R := (Spec A).ringCatSheaf) (ULift.{u} (Fin n))).ofEpi e.inv
  have : IsIso G.π := by
    dsimp [G]
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    infer_instance
  have : G.localGeneratorsData.IsLocallyFreeData := by
    constructor
    intro i
    dsimp [SheafOfModules.GeneratingSections.localGeneratorsData]
    infer_instance
  exact G.localGeneratorsData.isLocallyFree

end EnvelopeProperty.CanonicalGeometry
