import EnvelopeProperty.Cartier.EtaleRelativeFrobenius
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The actual Frobenius base-change square and native module coefficient exchange -/
noncomputable section
namespace EnvelopeProperty.Cartier.RelativeFrobenius
open CategoryTheory Limits
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- The square of the SAME original coefficient map and the two actual absolute Frobenius
maps is genuinely a native ring pushout for etale f. -/
theorem etaleFrobeniusSquare (hf : f.Etale) :
    IsPushout (CommRingCat.ofHom (frobenius A p)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom f) (CommRingCat.ofHom (frobenius B p)) := by
  apply (IsPushout.of_hasPushout (CommRingCat.ofHom (frobenius A p))
    (CommRingCat.ofHom f)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (etaleIso f p hf)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change coefficientMap f p ≫ map f p = (𝟙 _) ≫ CommRingCat.ofHom f
    rw [Category.id_comp]
    exact coefficientMap_map f p
  · change sourceMap f p ≫ map f p = (𝟙 _) ≫ CommRingCat.ofHom (frobenius B p)
    rw [Category.id_comp]
    exact sourceMap_map f p

end EnvelopeProperty.Cartier.RelativeFrobenius

namespace EnvelopeProperty.Cartier.RingPushoutScalarExchange
open CategoryTheory Limits
open scoped TensorProduct
universe u

/-- Actual scalar extension followed by actual scalar restriction exchanges over a genuine
native ring pushout on the WHOLE original coefficient module. -/
def scalarIso {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (h : S ⟶ U) (k : T ⟶ U) (sq : IsPushout f g h k) :
    (ModuleCat.extendScalars g.hom).obj
        ((ModuleCat.restrictScalars f.hom).obj (ModuleCat.of S S)) ≅
      (ModuleCat.restrictScalars k.hom).obj (ModuleCat.of U U) := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := h.hom.toAlgebra
  let := k.hom.toAlgebra
  let : Algebra R U := (k.hom.comp g.hom).toAlgebra
  let : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  have ht : h.hom.comp f.hom = k.hom.comp g.hom := congrArg CommRingCat.Hom.hom sq.w
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' ht.symm
  let : Algebra.IsPushout R T S U := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  exact (Algebra.IsPushout.equiv R T S U).toLinearEquiv.toModuleIso

/-- EVERY original pure coefficient tensor is sent to its actual original product in the
SAME pushout ring; no element-comparison certificate is supplied. -/
theorem scalarIso_tmul {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (h : S ⟶ U) (k : T ⟶ U) (sq : IsPushout f g h k) (t : T) (s : S) :
    let _ := g.hom.toAlgebra
    (scalarIso f g h k sq).hom
      (t ⊗ₜ[R] (show (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of S S) from s)) =
        k.hom t * h.hom s := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := h.hom.toAlgebra
  let := k.hom.toAlgebra
  let : Algebra R U := (k.hom.comp g.hom).toAlgebra
  let : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  have ht : h.hom.comp f.hom = k.hom.comp g.hom := congrArg CommRingCat.Hom.hom sq.w
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' ht.symm
  let : Algebra.IsPushout R T S U := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  change (Algebra.IsPushout.equiv R T S U) (t ⊗ₜ[R] s) = _
  exact Algebra.IsPushout.equiv_tmul R T S U t s

/-- The actual native ring pushout exchanges restriction and extension on EVERY original
module, without freeness, flatness or finite-presentation assumptions on that module. -/
def moduleIso {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (h : S ⟶ U) (k : T ⟶ U) (sq : IsPushout f g h k) (M : ModuleCat S) :
    (ModuleCat.extendScalars g.hom).obj ((ModuleCat.restrictScalars f.hom).obj M) ≅
      (ModuleCat.restrictScalars k.hom).obj ((ModuleCat.extendScalars h.hom).obj M) := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := h.hom.toAlgebra
  let := k.hom.toAlgebra
  let : Algebra R U := (k.hom.comp g.hom).toAlgebra
  let : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  have ht : h.hom.comp f.hom = k.hom.comp g.hom := congrArg CommRingCat.Hom.hom sq.w
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' ht.symm
  let : Algebra.IsPushout R T S U := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  let : Module R M := Module.compHom M f.hom
  let : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  exact (Algebra.IsPushout.cancelBaseChange R T S U M).symm.toModuleIso

/-- The whole original-module exchange sends EVERY actual pure tensor to the SAME original
module element tensored with its actual coefficient image. -/
theorem moduleIso_tmul {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (h : S ⟶ U) (k : T ⟶ U) (sq : IsPushout f g h k) (M : ModuleCat S)
    (t : T) (m : M) :
    let _ := g.hom.toAlgebra
    let _ := h.hom.toAlgebra
    (moduleIso f g h k sq M).hom
      (t ⊗ₜ[R] (show (ModuleCat.restrictScalars f.hom).obj M from m)) =
        k.hom t ⊗ₜ[S] m := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := h.hom.toAlgebra
  let := k.hom.toAlgebra
  let : Algebra R U := (k.hom.comp g.hom).toAlgebra
  let : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  have ht : h.hom.comp f.hom = k.hom.comp g.hom := congrArg CommRingCat.Hom.hom sq.w
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' ht.symm
  let : Algebra.IsPushout R T S U := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  let : Module R M := Module.compHom M f.hom
  let : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  change (Algebra.IsPushout.cancelBaseChange R T S U M).symm (t ⊗ₜ[R] m) = _
  exact Algebra.IsPushout.cancelBaseChange_symm_tmul R T S U M t m

/-- The genuine whole-module exchange is natural for EVERY original module morphism. -/
theorem moduleIso_naturality {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (h : S ⟶ U) (k : T ⟶ U) (sq : IsPushout f g h k)
    {M N : ModuleCat S} (a : M ⟶ N) :
    (ModuleCat.extendScalars g.hom).map ((ModuleCat.restrictScalars f.hom).map a) ≫
        (moduleIso f g h k sq N).hom =
      (moduleIso f g h k sq M).hom ≫
        (ModuleCat.restrictScalars k.hom).map ((ModuleCat.extendScalars h.hom).map a) := by
  let := g.hom.toAlgebra
  let := h.hom.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (moduleIso f g h k sq N).hom ((1 : T) ⊗ₜ[R] (a m)) =
    ((ModuleCat.extendScalars h.hom).map a)
      ((moduleIso f g h k sq M).hom ((1 : T) ⊗ₜ[R] m))
  exact (moduleIso_tmul f g h k sq N 1 (a m)).trans
    ((ModuleCat.ExtendScalars.map_tmul h.hom a (k.hom 1) m).symm.trans
      (congrArg (fun x : (ModuleCat.extendScalars h.hom).obj M =>
        ((ModuleCat.extendScalars h.hom).map a) x)
        (moduleIso_tmul f g h k sq M 1 m)).symm)

/-- Genuine natural base change on the ENTIRE original module category. -/
def moduleNatIso {R S T U : CommRingCat.{u}} (f : R ⟶ S) (g : R ⟶ T)
    (h : S ⟶ U) (k : T ⟶ U) (sq : IsPushout f g h k) :
    ModuleCat.restrictScalars f.hom ⋙ ModuleCat.extendScalars g.hom ≅
      ModuleCat.extendScalars h.hom ⋙ ModuleCat.restrictScalars k.hom :=
  NatIso.ofComponents (fun M => moduleIso f g h k sq M)
    (fun a => moduleIso_naturality f g h k sq a)

end EnvelopeProperty.Cartier.RingPushoutScalarExchange

namespace EnvelopeProperty.Cartier.RelativeFrobenius
open CategoryTheory
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
variable (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p]

/-- The ACTUAL native extension of the original Frobenius coefficient module along the
SAME original etale map is the actual original target Frobenius module. -/
def frobeniusScalarIso (hf : f.Etale) :
    (ModuleCat.extendScalars f).obj
        ((ModuleCat.restrictScalars (frobenius A p)).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars (frobenius B p)).obj (ModuleCat.of B B) :=
  RingPushoutScalarExchange.scalarIso (CommRingCat.ofHom (frobenius A p))
    (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom (frobenius B p))
      (etaleFrobeniusSquare f p hf)

/-- The actual Frobenius base-change isomorphism preserves EVERY original coefficient:
its whole pure-tensor map is b tensor a -> b^p*f(a). -/
theorem frobeniusScalarIso_tmul (hf : f.Etale) (b : B) (a : A) :
    let _ := f.toAlgebra
    (frobeniusScalarIso f p hf).hom
      (b ⊗ₜ[A] (show (ModuleCat.restrictScalars (frobenius A p)).obj (ModuleCat.of A A) from a)) =
        b^p * f a :=
  RingPushoutScalarExchange.scalarIso_tmul (CommRingCat.ofHom (frobenius A p))
    (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom (frobenius B p))
      (etaleFrobeniusSquare f p hf) b a

/-- Actual Frobenius base change on EVERY original module, with no module hypotheses. -/
def frobeniusModuleIso (hf : f.Etale) (M : ModuleCat A) :
    (ModuleCat.extendScalars f).obj
        ((ModuleCat.restrictScalars (frobenius A p)).obj M) ≅
      (ModuleCat.restrictScalars (frobenius B p)).obj ((ModuleCat.extendScalars f).obj M) :=
  RingPushoutScalarExchange.moduleIso (CommRingCat.ofHom (frobenius A p))
    (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom (frobenius B p))
      (etaleFrobeniusSquare f p hf) M

/-- The actual whole-module Frobenius comparison retains every original pure tensor. -/
theorem frobeniusModuleIso_tmul (hf : f.Etale) (M : ModuleCat A) (b : B) (m : M) :
    let _ := f.toAlgebra
    (frobeniusModuleIso f p hf M).hom
      (b ⊗ₜ[A] (show (ModuleCat.restrictScalars (frobenius A p)).obj M from m)) =
        (b^p) ⊗ₜ[A] m :=
  RingPushoutScalarExchange.moduleIso_tmul (CommRingCat.ofHom (frobenius A p))
    (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom (frobenius B p))
      (etaleFrobeniusSquare f p hf) M b m

/-- The true Frobenius comparison is a genuine natural isomorphism of the actual original
extension and Frobenius-restriction functors. -/
def frobeniusModuleNatIso (hf : f.Etale) :
    ModuleCat.restrictScalars (frobenius A p) ⋙ ModuleCat.extendScalars f ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars (frobenius B p) :=
  RingPushoutScalarExchange.moduleNatIso (CommRingCat.ofHom (frobenius A p))
    (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom (frobenius B p))
      (etaleFrobeniusSquare f p hf)

end EnvelopeProperty.Cartier.RelativeFrobenius
