/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Scheme.Modules.IdealSheafFinite
import Hironaka.Scheme.IdealSheaf.Defs
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Genuine module sheaves of the actual effective Cartier ideals

A regular local equation gives an actual linear isomorphism from the original
ring to the actual ideal. The true affine ideal-module/tilde comparison then
provides genuine rank-one local sheaf trivializations.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty
variable {R : Type u} [CommRing R]

/-- Multiplication by an actual regular generator is an actual linear
isomorphism onto the actual original ideal, without a domain hypothesis. -/
def regularGeneratorModuleEquiv (I : Ideal R) (g : R)
    (hg : g ∈ nonZeroDivisors R) (hI : I = Ideal.span {g}) : R ≃ₗ[R] I := by
  have hmem : g ∈ I := hI.symm ▸ Ideal.mem_span_singleton_self g
  refine LinearEquiv.ofBijective
    { toFun := fun r => ⟨r * g, I.mul_mem_left r hmem⟩
      map_add' := fun r s => Subtype.ext (add_mul r s g)
      map_smul' := fun r s => Subtype.ext (mul_assoc r s g) } ⟨?_, ?_⟩
  · intro r s hrs
    apply sub_eq_zero.mp
    apply (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp
    rw [sub_mul, show r * g = s * g from congrArg Subtype.val hrs, sub_self]
  · intro a
    have ha : (a : R) ∈ Ideal.span {g} := by rw [← hI]; exact a.property
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp ha
    exact ⟨r, Subtype.ext hr⟩

/-- The actual rank-one coordinate is multiplication by the original equation. -/
theorem regularGeneratorModuleEquiv_apply (I : Ideal R) (g : R)
    (hg : g ∈ nonZeroDivisors R) (hI : I = Ideal.span {g}) (r : R) :
    ((regularGeneratorModuleEquiv I g hg hI r : I) : R) = r * g := rfl

end EnvelopeProperty

namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- A true regular affine equation gives an actual isomorphism from the
original affine structure sheaf to the entire actual restricted ideal module. -/
def regularGeneratorModuleIso (U : X.affineOpens) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) (hI : I.ideal U = Ideal.span {g}) :
    SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf ≅ I.toModules.restrict U.2.fromSpec := by
  let e : Γ(X, U) ≃ₗ[Γ(X, U)]
      moduleSpecΓFunctor.obj (I.toModules.restrict U.2.fromSpec) :=
    ((EnvelopeProperty.regularGeneratorModuleEquiv (I.ideal U) g hg hI).trans
      (I.toModulesSectionsEquiv U).symm).trans (I.toModules.topSectionsEquiv U.2)
  let := I.isIso_fromTildeΓ_toModules U.2
  exact (tildeSelf (R := Γ(X, U))).symm ≪≫
    (tilde.functor Γ(X, U)).mapIso e.toModuleIso ≪≫
      asIso (I.toModules.restrict U.2.fromSpec).fromTildeΓ

/-- Invertibility constructs genuine local rank-one trivializations of the
actual existing ideal module sheaf at every original scheme point. -/
theorem IsInvertible.exists_affine_module_trivialization (hI : I.IsInvertible) (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1),
      Nonempty (SheafOfModules.unit (Spec Γ(X, U)).ringCatSheaf ≅
        I.toModules.restrict U.2.fromSpec) := by
  obtain ⟨U, hx, g, hg, hgen⟩ := hI x
  exact ⟨U, hx, ⟨I.regularGeneratorModuleIso U g hg hgen⟩⟩

/-- The true affine-spectrum trivialization yields the actual trivialization
of the whole original ideal sheaf over the corresponding original open. -/
def regularGeneratorModuleOverIso (U : X.affineOpens) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) (hI : I.ideal U = Ideal.span {g}) :
    SheafOfModules.unit (X.ringCatSheaf.over (U : X.Opens)) ≅ I.toModules.over U :=
  (Opens.sheafOfModulesEquivOverInverseUnit (U : X.Opens) X.ringCatSheaf).symm ≪≫
    (Scheme.Modules.overEquiv (U : X.Opens)).inverse.mapIso
      ((Scheme.Modules.restrictUnitIso U.2.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapIso
          (I.regularGeneratorModuleIso U g hg hI) ≪≫ I.toModules.restrictιIso U.2) ≪≫
      I.toModules.overIso U

/-- The actual local Cartier ideal module is free on precisely one generator. -/
def regularGeneratorFreeOverIso (U : X.affineOpens) (g : Γ(X, U))
    (hg : g ∈ nonZeroDivisors Γ(X, U)) (hI : I.ideal U = Ideal.span {g}) :
    SheafOfModules.free (R := X.ringCatSheaf.over (U : X.Opens)) PUnit ≅ I.toModules.over U :=
  (coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit
    (X.ringCatSheaf.over (U : X.Opens)))) ≪≫ I.regularGeneratorModuleOverIso U g hg hI

/-- Actual invertibility proves that the actual original ideal module sheaf
is locally free in the existing interface, with singleton free local charts. -/
theorem IsInvertible.isLocallyFree_toModules (hI : I.IsInvertible) :
    SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) I.toModules := by
  choose U hx g hg hgen using hI
  let e (x : X) := I.regularGeneratorFreeOverIso (U x) (g x) (hg x) (hgen x)
  let q : SheafOfModules.LocalGeneratorsData.{u} (R := X.ringCatSheaf) I.toModules :=
    { I := X
      X := fun x => (U x : X.Opens)
      coversTop := (Opens.coversTop_iff (U := fun x : X => (U x : X.Opens))).mpr
        (top_unique (fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩))
      generators x := (SheafOfModules.free.generatingSections PUnit).ofEpi (e x).hom }
  let : q.IsLocallyFreeData := by
    constructor
    intro x
    change IsIso ((SheafOfModules.free.generatingSections PUnit).ofEpi (e x).hom).π
    rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
    infer_instance
  exact q.isLocallyFree

end AlgebraicGeometry.Scheme.IdealSheafData
