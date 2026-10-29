/-
Mathlib-only proof port. Original source: EnvelopeProperty/ComplexGeometry/Schemes/LineBundleSections.lean
Upstream SHA256: c1adb73fb95953101383fcb6d4ccd7920eb6fa1cbf573811a7626ea54d521dd3
Upstream canonical-source commit: feaaab87c3197e6e4f18c6176d50b5c739c81b50
Compatibility changes: module imports and enclosing namespace only.
Original mathematical statements and proofs below are preserved.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import EnvelopeProperty.AlgGeom.Canonical.ValuationFiltration
import EnvelopeProperty.AlgGeom.Canonical.ValuationIdeals
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalModule
import Mathlib.Tactic

/-!
# Intrinsic line-bundle sections and tensor sheaves

The objects here are actual sheaves of modules on a scheme. Local frames are
isomorphisms to the structure sheaf on an open set; tensor objects are obtained
by sheafifying the actual objectwise tensor presheaf. No section ring or
dimension asymptotic is supplied as data.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace EnvelopeProperty.CanonicalGeometry

noncomputable section

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.obj)

/-- Actual sections over an open set, retaining their natural module structure. -/
abbrev bundleSections (L : X.Modules) (U : X.Opens) : Type u := L.val.obj (op U)

/-- The section module is over the scheme's commutative structure ring. -/
instance bundleSectionsModule (L : X.Modules) (U : X.Opens) :
    Module (X.sheaf.obj.obj (op U)) (bundleSections L U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj (op U)) (L.val.obj (op U)))

instance bundleSectionsSMulCommClass (L : X.Modules) (U : X.Opens) :
    SMulCommClass (X.sheaf.obj.obj (op U)) (X.sheaf.obj.obj (op U)) (bundleSections L U) where
  smul_comm r q s := by rw [← mul_smul, ← mul_smul, mul_comm]

/-- The actual tensor presheaf of two structure-sheaf modules. -/
def bundleTensorPresheaf (L N : X.Modules) : X.PresheafOfModules :=
  PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) L.val N.val

/-- The tensor sheaf is the sheafification of the actual tensor presheaf. -/
def bundleTensor (L N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (bundleTensorPresheaf L N)

set_option backward.isDefEq.respectTransparency false in
/-- Tensor sheaves transport actual sheaf isomorphisms. -/
def bundleTensorIso {L L' N N' : X.Modules} (e : L ≅ L') (f : N ≅ N') :
    bundleTensor L N ≅ bundleTensor L' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.tensorIso ((SheafOfModules.forget _).mapIso e)
      ((SheafOfModules.forget _).mapIso f))

/-- Sheafifying the underlying presheaf of an actual sheaf recovers that
sheaf by the sheafification adjunction counit. -/
def bundleSheafificationIso (L : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj L.val ≅ L := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)
  haveI : IsIso adj.counit := by dsimp [adj]; infer_instance
  exact (asIso adj.counit).app L

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor sheaf with the structure sheaf has its canonical
unit isomorphism. -/
def bundleTensorLeftUnitIso (L : X.Modules) :
    bundleTensor (SheafOfModules.unit X.ringCatSheaf) L ≅ L :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.leftUnitor L.val) ≪≫ bundleSheafificationIso L

/-- Pure tensors of actual sections, mapped into the tensor sheaf by the
sheafification unit. -/
def tensorSection (L N : X.Modules) (U : X.Opens)
    (s : bundleSections L U) (t : bundleSections N U) : bundleSections (bundleTensor L N) U :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (bundleTensorPresheaf L N)).app (op U)).hom
      (s ⊗ₜ[X.sheaf.obj.obj (op U)] t)

@[simp] theorem tensorSection_add_left (L N : X.Modules) (U : X.Opens)
    (s s' : bundleSections L U) (t : bundleSections N U) :
    tensorSection L N U (s + s') t = tensorSection L N U s t + tensorSection L N U s' t := by
  unfold tensorSection
  rw [TensorProduct.add_tmul]
  exact ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (bundleTensorPresheaf L N)).app (op U)).hom).map_add _ _

@[simp] theorem tensorSection_add_right (L N : X.Modules) (U : X.Opens)
    (s : bundleSections L U) (t t' : bundleSections N U) :
    tensorSection L N U s (t + t') = tensorSection L N U s t + tensorSection L N U s t' := by
  unfold tensorSection
  rw [TensorProduct.tmul_add]
  exact ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (bundleTensorPresheaf L N)).app (op U)).hom).map_add _ _

@[simp] theorem tensorSection_zero_left (L N : X.Modules) (U : X.Opens)
    (t : bundleSections N U) : tensorSection L N U 0 t = 0 := by
  unfold tensorSection
  rw [TensorProduct.zero_tmul]
  exact ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (bundleTensorPresheaf L N)).app (op U)).hom).map_zero

@[simp] theorem tensorSection_zero_right (L N : X.Modules) (U : X.Opens)
    (s : bundleSections L U) : tensorSection L N U s 0 = 0 := by
  unfold tensorSection
  rw [TensorProduct.tmul_zero]
  exact ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (bundleTensorPresheaf L N)).app (op U)).hom).map_zero

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem tensorSection_smul_left (L N : X.Modules) (U : X.Opens)
    (r : X.sheaf.obj.obj (op U)) (s : bundleSections L U) (t : bundleSections N U) :
    tensorSection L N U (r • s) t = r • tensorSection L N U s t := by
  have : SMulCommClass (X.sheaf.obj.obj (op U)) (X.sheaf.obj.obj (op U))
      (L.val.obj (op U)) := bundleSectionsSMulCommClass L U
  unfold tensorSection
  rw [← TensorProduct.smul_tmul']
  exact ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (bundleTensorPresheaf L N)).app (op U)).hom).map_smul r _

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem tensorSection_smul_right (L N : X.Modules) (U : X.Opens)
    (r : X.sheaf.obj.obj (op U)) (s : bundleSections L U) (t : bundleSections N U) :
    tensorSection L N U s (r • t) = r • tensorSection L N U s t := by
  have : IsScalarTower (X.sheaf.obj.obj (op U)) (X.sheaf.obj.obj (op U))
      (L.val.obj (op U)) := ⟨fun r q s => mul_smul r q s⟩
  have : IsScalarTower (X.sheaf.obj.obj (op U)) (X.sheaf.obj.obj (op U))
      (N.val.obj (op U)) := ⟨fun r q t => mul_smul r q t⟩
  have h := TensorProduct.smul_tmul (R := X.sheaf.obj.obj (op U))
    (R' := X.sheaf.obj.obj (op U)) r s t
  calc
    tensorSection L N U s (r • t) = tensorSection L N U (r • s) t := by
      exact congrArg
        ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (bundleTensorPresheaf L N)).app (op U)).hom) h.symm
    _ = r • tensorSection L N U s t := tensorSection_smul_left L N U r s t

/-- Tensor section multiplication commutes with restriction to smaller opens. -/
theorem tensorSection_restrict (L N : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (s : bundleSections L U) (t : bundleSections N U) :
    (bundleTensor L N).val.map i.op (tensorSection L N U s t) =
      tensorSection L N V (L.val.map i.op s) (N.val.map i.op t) := by
  have h := PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (bundleTensorPresheaf L N)) i.op
      (s ⊗ₜ[X.sheaf.obj.obj (op U)] t)
  exact h.symm

/-- The intrinsic section product is an actual bilinear map into the
sections of the tensor sheaf. -/
def tensorSectionBilinear (L N : X.Modules) (U : X.Opens) :
    bundleSections L U →ₗ[X.sheaf.obj.obj (op U)]
      bundleSections N U →ₗ[X.sheaf.obj.obj (op U)] bundleSections (bundleTensor L N) U where
  toFun s :=
    { toFun := tensorSection L N U s
      map_add' := tensorSection_add_right L N U s
      map_smul' := fun r t => tensorSection_smul_right L N U r s t }
  map_add' s s' := by ext t; exact tensorSection_add_left L N U s s' t
  map_smul' r s := by ext t; exact tensorSection_smul_left L N U r s t

/-- Recursively formed actual tensor sheaves, starting with the structure sheaf. -/
def bundleTensorPower (L : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => bundleTensor (bundleTensorPower L n) L

/-- Intrinsic global sections of the actual tensor sheaf. -/
abbrev bundlePowerGlobalSections (L : X.Modules) (n : ℕ) : Type u :=
  bundleSections (bundleTensorPower L n) ⊤

/-- Degree-successor multiplication on the actual section spaces. -/
def bundlePowerSectionMul (L : X.Modules) (n : ℕ) (U : X.Opens)
    (s : bundleSections (bundleTensorPower L n) U) (t : bundleSections L U) :
    bundleSections (bundleTensorPower L (n + 1)) U :=
  tensorSection (bundleTensorPower L n) L U s t

/-- Actual successor multiplication on the global sections of the tensor powers. -/
abbrev bundlePowerGlobalSectionMul (L : X.Modules) (n : ℕ) :
    bundlePowerGlobalSections L n →ₗ[X.sheaf.obj.obj (op ⊤)]
      bundleSections L ⊤ →ₗ[X.sheaf.obj.obj (op ⊤)] bundlePowerGlobalSections L (n + 1) :=
  tensorSectionBilinear (bundleTensorPower L n) L ⊤

/-- The degree-successor product is intrinsic under restriction. -/
theorem bundlePowerSectionMul_restrict (L : X.Modules) (n : ℕ)
    {U V : X.Opens} (i : V ⟶ U)
    (s : bundleSections (bundleTensorPower L n) U) (t : bundleSections L U) :
    (bundleTensorPower L (n + 1)).val.map i.op (bundlePowerSectionMul L n U s t) =
      bundlePowerSectionMul L n V ((bundleTensorPower L n).val.map i.op s) (L.val.map i.op t) :=
  tensorSection_restrict (bundleTensorPower L n) L i s t

/-- A local rank-one frame is an isomorphism of actual sheaves on the open site. -/
abbrev LocalBundleFrame (L : X.Modules) (U : X.Opens) :=
  L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)

/-- A genuine rank-one atlas on a sheaf, with an open cover and sheaf frames. -/
structure LineBundleAtlas (L : X.Modules) where
  I : Type u
  opens : I → X.Opens
  covers : ∀ x : X, ∃ i, x ∈ opens i
  frame : ∀ i, LocalBundleFrame L (opens i)

/-- An intrinsic line bundle consists of a sheaf with a rank-one local atlas. -/
structure IntrinsicLineBundle (X : Scheme.{u}) where
  sheaf : X.Modules
  atlas : LineBundleAtlas sheaf

/-- The structure sheaf gives an actual trivial line bundle on any scheme. -/
def trivialIntrinsicLineBundle (X : Scheme.{u}) : IntrinsicLineBundle X where
  sheaf := SheafOfModules.unit X.ringCatSheaf
  atlas :=
    { I := PUnit
      opens := fun _ => ⊤
      covers := fun _ => ⟨PUnit.unit, trivial⟩
      frame := fun _ => Iso.refl _ }

/-- A global isomorphism to the structure sheaf supplies a genuine rank-one
atlas on the actual sheaf. -/
def intrinsicLineBundleOfFrame (L : X.Modules)
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) : IntrinsicLineBundle X where
  sheaf := L
  atlas :=
    { I := PUnit
      opens := fun _ => ⊤
      covers := fun _ => ⟨PUnit.unit, trivial⟩
      frame := fun _ => (SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e }

section AffineCharts

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]

/-- The affine sheaf frame is produced by applying the actual tilde functor
to a module isomorphism, followed by tilde of the coefficient ring. -/
def affineSheafFrameOfTrivialization (e : M ≃ₗ[A] A) :
    AlgebraicGeometry.tilde (ModuleCat.of A M) ≅
      SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf :=
  (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).mapIso e.toModuleIso ≪≫
    AlgebraicGeometry.tildeSelf

/-- The actual affine tilde sheaf of a rank-one module has a constructed atlas. -/
def affineLineBundleOfTrivialization (e : M ≃ₗ[A] A) :
    IntrinsicLineBundle (Spec (CommRingCat.of A)) :=
  intrinsicLineBundleOfFrame (AlgebraicGeometry.tilde (ModuleCat.of A M))
    (affineSheafFrameOfTrivialization e)

variable {K : Type u} [CommRing K] [Algebra K A]

/-- The actual top differential wedge on an affine chart produces its
canonical line sheaf, once differential coordinates are given. -/
def affineCanonicalLineBundle {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    IntrinsicLineBundle (Spec (CommRingCat.of A)) :=
  affineLineBundleOfTrivialization (affineCanonicalTrivialization b)

/-- The actual dual of that differential wedge produces the anticanonical
line sheaf on the affine chart. -/
def affineAnticanonicalLineBundle {n : ℕ}
    (b : Module.Basis (Fin n) A (KaehlerDifferential K A)) :
    IntrinsicLineBundle (Spec (CommRingCat.of A)) :=
  affineLineBundleOfTrivialization (affineAnticanonicalTrivialization b)

/-- The polynomial chart supplies its differential coordinates internally. -/
def polynomialCanonicalLineBundle (K : Type u) [CommRing K] (n : ℕ) :
    IntrinsicLineBundle (Spec (CommRingCat.of (MvPolynomial (Fin n) K))) :=
  affineCanonicalLineBundle (KaehlerDifferential.mvPolynomialBasis K (Fin n))

/-- The polynomial anticanonical line sheaf is the actual tilde of the dual
of the top differential wedge, with no assumed rank-one premise. -/
def polynomialAnticanonicalLineBundle (K : Type u) [CommRing K] (n : ℕ) :
    IntrinsicLineBundle (Spec (CommRingCat.of (MvPolynomial (Fin n) K))) :=
  affineAnticanonicalLineBundle (KaehlerDifferential.mvPolynomialBasis K (Fin n))

end AffineCharts

/-- An actual global sheaf frame produces frames for all tensor powers. -/
def bundleTensorPowerTrivialization {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∀ n, bundleTensorPower L n ≅ SheafOfModules.unit X.ringCatSheaf
  | 0 => Iso.refl _
  | n + 1 => bundleTensorIso (bundleTensorPowerTrivialization e n) e ≪≫
      bundleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)

/-- Every power of a globally framed actual line sheaf has a constructed
line-bundle atlas, obtained from the tensor and unit isomorphisms. -/
def bundleTensorPowerLineBundle {L : X.Modules}
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (n : ℕ) : IntrinsicLineBundle X :=
  intrinsicLineBundleOfFrame (bundleTensorPower L n) (bundleTensorPowerTrivialization e n)

/-- An actual sheaf frame identifies sections on every smaller open with
the corresponding structure-ring sections. -/
def LocalBundleFrame.coefficients {L : X.Modules} {U V : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) :
    bundleSections L V ≃ₗ[X.sheaf.obj.obj (op V)] X.sheaf.obj.obj (op V) :=
  ((SheafOfModules.evaluation (R := X.ringCatSheaf.over U) (op (Over.mk i))).mapIso e).toLinearEquiv

/-- These coefficients commute with actual sheaf restriction maps. -/
theorem LocalBundleFrame.coefficients_restrict {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (i : V ⟶ U) (j : W ⟶ V) (s : bundleSections L V) :
    e.coefficients (j ≫ i) (L.val.map j.op s) =
      X.sheaf.obj.map j.op (e.coefficients i s) := by
  exact PresheafOfModules.naturality_apply e.hom.val
    (Over.homMk j : Over.mk (j ≫ i) ⟶ Over.mk i).op s

/-- The actual regular coefficient of a section on each atlas overlap. -/
def LineBundleAtlas.chartCoefficients {L : X.Modules} (a : LineBundleAtlas L)
    (U : X.Opens) (i : a.I) (s : bundleSections L U) :
    X.sheaf.obj.obj (op (U ⊓ a.opens i)) :=
  (a.frame i).coefficients (homOfLE inf_le_right)
    (L.val.map (homOfLE inf_le_left).op s)

/-- Equality of the coefficients on the chart overlaps implies equality of
the actual section, by the sheaf's separation property. -/
theorem LineBundleAtlas.section_ext {L : X.Modules} (a : LineBundleAtlas L)
    (U : X.Opens) (s t : bundleSections L U)
    (h : ∀ i, a.chartCoefficients U i s = a.chartCoefficients U i t) : s = t := by
  apply TopCat.Presheaf.IsSheaf.section_ext (F := L.val.presheaf) L.isSheaf
  intro x hx
  obtain ⟨i, hi⟩ := a.covers x
  refine ⟨U ⊓ a.opens i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  exact ((a.frame i).coefficients (homOfLE inf_le_right)).injective (h i)

section RankOneTransitions

variable {R S : Type*} [CommRing R] [AddCommGroup S] [Module R S]

/-- Every automorphism of the rank-one free module is multiplication by an
actual unit; its inverse supplies the inverse unit coefficient. -/
def rankOneAutomorphismUnit (e : R ≃ₗ[R] R) : Rˣ where
  val := e 1
  inv := e.symm 1
  val_inv := by
    calc
      e 1 * e.symm 1 = e (e.symm 1) := by
        simpa [smul_eq_mul, mul_comm] using (e.map_smul (e.symm 1) (1 : R)).symm
      _ = 1 := e.apply_symm_apply 1
  inv_val := by
    calc
      e.symm 1 * e 1 = e.symm (e 1) := by
        simpa [smul_eq_mul, mul_comm] using (e.symm.map_smul (e 1) (1 : R)).symm
      _ = 1 := e.symm_apply_apply 1

theorem rankOneAutomorphism_apply (e : R ≃ₗ[R] R) (r : R) :
    e r = (rankOneAutomorphismUnit e : R) * r := by
  simpa [rankOneAutomorphismUnit, smul_eq_mul, mul_comm] using e.map_smul r (1 : R)

/-- The transition unit is derived from the two rank-one linear frames. -/
def sectionFrameTransition (e f : S ≃ₗ[R] R) : Rˣ :=
  rankOneAutomorphismUnit (e.symm.trans f)

theorem sectionFrameTransition_coefficients (e f : S ≃ₗ[R] R) (s : S) :
    f s = (sectionFrameTransition e f : R) * e s := by
  simpa [sectionFrameTransition] using rankOneAutomorphism_apply (e.symm.trans f) (e s)

@[simp] theorem sectionFrameTransition_self (e : S ≃ₗ[R] R) :
    sectionFrameTransition e e = 1 := by
  apply Units.ext
  simp [sectionFrameTransition, rankOneAutomorphismUnit]

/-- Unit transitions satisfy the actual frame cocycle identity. -/
theorem sectionFrameTransition_cocycle (e f g : S ≃ₗ[R] R) :
    sectionFrameTransition e g = sectionFrameTransition f g * sectionFrameTransition e f := by
  apply Units.ext
  have h := sectionFrameTransition_coefficients f g (e.symm 1)
  simpa [sectionFrameTransition, rankOneAutomorphismUnit] using h

end RankOneTransitions

/-- The transition between two sheaf frames on a common smaller open is
an actual unit of that open's structure ring. -/
def localBundleFrameTransition {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V) :
    (X.sheaf.obj.obj (op W))ˣ :=
  sectionFrameTransition (e.coefficients i) (f.coefficients j)

theorem localBundleFrameTransition_coefficients {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V)
    (s : bundleSections L W) :
    f.coefficients j s = (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) *
      e.coefficients i s :=
  sectionFrameTransition_coefficients (e.coefficients i) (f.coefficients j) s

/-- The derived sheaf transition units obey the cocycle identity on a common open. -/
theorem localBundleFrameTransition_cocycle {L : X.Modules} {U V Z W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (g : LocalBundleFrame L Z)
    (i : W ⟶ U) (j : W ⟶ V) (k : W ⟶ Z) :
    localBundleFrameTransition e g i k =
      localBundleFrameTransition f g j k * localBundleFrameTransition e f i j :=
  sectionFrameTransition_cocycle (e.coefficients i) (f.coefficients j) (g.coefficients k)

/-- Transition coefficients restrict as regular functions on the overlap. -/
theorem localBundleFrameTransition_restrict {L : X.Modules} {U V W Z : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V)
    (k : Z ⟶ W) :
    (localBundleFrameTransition e f (k ≫ i) (k ≫ j) : X.sheaf.obj.obj (op Z)) =
      X.sheaf.obj.map k.op (localBundleFrameTransition e f i j : X.sheaf.obj.obj (op W)) := by
  let s : bundleSections L W := (e.coefficients i).symm 1
  have he : e.coefficients (k ≫ i) (L.val.map k.op s) = 1 := by
    rw [e.coefficients_restrict i k s]
    simp [s]
  have hf := f.coefficients_restrict j k s
  have ht := localBundleFrameTransition_coefficients e f (k ≫ i) (k ≫ j) (L.val.map k.op s)
  rw [he, mul_one] at ht
  simpa [s, localBundleFrameTransition, sectionFrameTransition, rankOneAutomorphismUnit]
    using ht.symm.trans hf

/-- A valuation centered on the common coefficient ring gives the same value
in both actual local sheaf frames. -/
theorem localBundleFrame_valuation_independent {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V)
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℝ))
    (ι : X.sheaf.obj.obj (op W) →+* F)
    (hcenter : ∀ r, (0 : WithTop ℝ) ≤ v (ι r)) (s : bundleSections L W) :
    v (ι (f.coefficients j s)) = v (ι (e.coefficients i s)) := by
  rw [localBundleFrameTransition_coefficients e f i j s, map_mul]
  exact valuation_frame_independent v ι hcenter (localBundleFrameTransition e f i j) _

/-- The actual valuation ideal pulls back along the evaluated sheaf frame
to a threshold submodule of actual sections. -/
def localBundleSectionFiltration {L : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame L U) (i : W ⟶ U)
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℝ))
    (ι : X.sheaf.obj.obj (op W) →+* F)
    (hcenter : ∀ r, (0 : WithTop ℝ) ≤ v (ι r)) (a : ℝ) :
    Submodule (X.sheaf.obj.obj (op W)) (bundleSections L W) :=
  Submodule.comap (e.coefficients i).toLinearMap (valuationIdeal v ι hcenter a)

@[simp] theorem mem_localBundleSectionFiltration {L : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame L U) (i : W ⟶ U)
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℝ))
    (ι : X.sheaf.obj.obj (op W) →+* F)
    (hcenter : ∀ r, (0 : WithTop ℝ) ≤ v (ι r)) (a : ℝ) (s : bundleSections L W) :
    s ∈ localBundleSectionFiltration e i v ι hcenter a ↔
      (a : WithTop ℝ) ≤ v (ι (e.coefficients i s)) := Iff.rfl

/-- Raising the threshold shrinks the intrinsic local section submodule. -/
theorem localBundleSectionFiltration_antitone {L : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame L U) (i : W ⟶ U)
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℝ))
    (ι : X.sheaf.obj.obj (op W) →+* F)
    (hcenter : ∀ r, (0 : WithTop ℝ) ≤ v (ι r)) :
    Antitone (localBundleSectionFiltration e i v ι hcenter) := by
  intro a b hab s hs
  exact (WithTop.coe_le_coe.mpr hab).trans hs

/-- The full actual section filtration is independent of the chosen
line-bundle frame on a common open. -/
theorem localBundleSectionFiltration_frame_independent {L : X.Modules} {U V W : X.Opens}
    (e : LocalBundleFrame L U) (f : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V)
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℝ))
    (ι : X.sheaf.obj.obj (op W) →+* F)
    (hcenter : ∀ r, (0 : WithTop ℝ) ≤ v (ι r)) (a : ℝ) :
    localBundleSectionFiltration f j v ι hcenter a =
      localBundleSectionFiltration e i v ι hcenter a := by
  ext s
  simp only [mem_localBundleSectionFiltration]
  rw [localBundleFrame_valuation_independent e f i j v ι hcenter s]

end

end EnvelopeProperty.CanonicalGeometry
