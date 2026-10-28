import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceSpectrum
import EnvelopeProperty.Vanishing.NadelKummerCanonicalBaseChangeCore

/-! # Actual canonical sections on the entire original mixed source

Only the actual original mixed-ring geometry is instantiated here.
The basis-free spectrum comparison is compiled in its separate narrow file.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def originalAlgebraTensorIso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅
      ModuleCat.of S (S ⊗[R] M) := by
  let c := NadelKummerCanonicalBaseChange.algebraRestrictionEquiv (A := R) (B := S)
  let t := TensorProduct.congr c (LinearEquiv.refl R M)
  let e : (ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S] S ⊗[R] M :=
    { __ := t.toAddEquiv
      map_smul' s z := by
        change t (s • z) = s • t z
        induction z using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
        | tmul s' m => rfl }
  exact e.toModuleIso

private def mixedTensorModuleIso
    {A S B C : Type u} [CommRing A] [CommRing S] [CommRing B] [CommRing C]
    [Algebra A S] [Algebra A B] [Algebra A C] [Algebra S C] [Algebra B C]
    [IsScalarTower A S C] [IsScalarTower A B C] [Algebra.IsPushout A S B C]
    (M : ModuleCat B) (P : ModuleCat C)
    (e : (ModuleCat.extendScalars (algebraMap B C)).obj M ≅ P) :
    (ModuleCat.extendScalars (algebraMap A S)).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M) ≅
      (ModuleCat.restrictScalars (algebraMap S C)).obj P := by
  let M₀ := (ModuleCat.restrictScalars (algebraMap A B)).obj M
  letI : Module B M₀ := M.isModule
  letI : IsScalarTower A B M₀ :=
    IsScalarTower.of_algebraMap_smul (R := A) (A := B) (M := M₀) (fun _ _ => rfl)
  let P₀ := (ModuleCat.restrictScalars (algebraMap S C)).obj P
  letI : Module C P₀ := P.isModule
  letI : IsScalarTower S C P₀ :=
    IsScalarTower.of_algebraMap_smul (R := S) (A := C) (M := P₀) (fun _ _ => rfl)
  let e₀ : C ⊗[B] M₀ ≃ₗ[C] P₀ :=
    ((originalAlgebraTensorIso M).symm ≪≫ e).toLinearEquiv
  exact originalAlgebraTensorIso M₀ ≪≫
    (NadelCanonicalBaseChange.mixedTensorEquiv
      (A := A) (S := S) (B := B) (C := C) (M := M₀) (N := P₀) e₀).toModuleIso

private def actualTensorModuleIso
    {A S B : CommRingCat.{u}} [Algebra A S] [Algebra A B]
    (M : ModuleCat B) (P : ModuleCat (CommRingCat.of (S ⊗[A] B)))
    (e : (ModuleCat.extendScalars
      (R := B) (S := CommRingCat.of (S ⊗[A] B))
      (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom).obj M ≅ P) :
    (ModuleCat.extendScalars (algebraMap A S)).obj
      ((ModuleCat.restrictScalars (algebraMap A B)).obj M) ≅
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B)).obj P := by
  letI : Algebra B (S ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  exact mixedTensorModuleIso (A := A) (S := S) (B := B)
    (C := CommRingCat.of (S ⊗[A] B)) M P e

section Mixed
open NadelMixedKummer NadelCanonicalMixed
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Actual entire canonical module of the original mixed source, with
its ORIGINAL B scalar action. -/
def mixedCanonicalModule : ModuleCat (CommRingCat.of (mixedRing x N I σ u)) :=
  (moduleSpecΓFunctor (R := .of (mixedRing x N I σ u))).obj
    (exteriorCotangentSheaf (mixedStructure (k := k) x N I σ u) n)

/-- The actual B→C inclusion, before applying Spec or Γ. -/
def mixedRightHom : CommRingCat.of (mixedRing x N I σ u) ⟶
    CommRingCat.of (extendedMixedRing x N I σ u) :=
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := UnitCover N u)
      (B := mixedRing x N I σ u)).toRingHom

/-- Actual whole canonical sections after the SAME full unit extension,
with the original tensor algebra acting on its own spectrum. -/
def extendedMixedCanonicalModule : ModuleCat (CommRingCat.of (extendedMixedRing x N I σ u)) :=
  (moduleSpecΓFunctor (R := .of (extendedMixedRing x N I σ u))).obj
    (exteriorCotangentSheaf
      (mixedUnitProjection x N I σ u ≫ mixedStructure (k := k) x N I σ u) n)

/-- Original coordinates and tame positive degrees produce the whole
canonical scalar comparison for the SAME entire mixed ring. -/
def mixedNativeSectionsIso
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (ModuleCat.extendScalars
      (R := CommRingCat.of (mixedRing x N I σ u))
      (S := CommRingCat.of (extendedMixedRing x N I σ u))
      (mixedRightHom x N I σ u).hom).obj
      (mixedCanonicalModule (k := k) x N I σ u) ≅
      extendedMixedCanonicalModule (k := k) x N I σ u := by
  letI := mixedStructure_smooth x N I σ u hx hN htame
  letI : Etale (Spec.map (mixedRightHom x N I σ u)) := by
    change Etale (mixedUnitProjection x N I σ u)
    exact mixedUnitProjection_etale x N I σ u hN htame
  exact nativeSectionsIso
    (B := .of (mixedRing x N I σ u)) (C := .of (extendedMixedRing x N I σ u))
    (mixedStructure (k := k) x N I σ u)
    (mixedRightHom x N I σ u) n

/-- The actual original canonical module with its original A action. -/
def mixedCanonicalModuleOverBase : ModuleCat (CommRingCat.of A) :=
  (ModuleCat.restrictScalars
    (R := CommRingCat.of A) (S := CommRingCat.of (mixedRing x N I σ u))
    (algebraMap A (mixedRing x N I σ u))).obj
    (mixedCanonicalModule (k := k) x N I σ u)

/-- The actual canonical comparison required by faithful trace descent:
S⊗A Γ_B(ω_B) ≅ Γ_C(ω_C), with ORIGINAL S action and C=S⊗A B.
All geometric and tensor comparisons are constructed internally. -/
def mixedExtendedSectionsIso
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    (ModuleCat.extendScalars
      (R := CommRingCat.of A) (S := CommRingCat.of (UnitCover N u))
      (algebraMap A (UnitCover N u))).obj
      (mixedCanonicalModuleOverBase (k := k) x N I σ u) ≅
      (ModuleCat.restrictScalars
        (R := CommRingCat.of (UnitCover N u))
        (S := CommRingCat.of (extendedMixedRing x N I σ u))
        (Algebra.TensorProduct.includeLeftRingHom : UnitCover N u →+*
          extendedMixedRing x N I σ u)).obj
        (extendedMixedCanonicalModule (k := k) x N I σ u) := by
  exact actualTensorModuleIso (A := CommRingCat.of A) (S := CommRingCat.of (UnitCover N u))
    (B := CommRingCat.of (mixedRing x N I σ u))
    (mixedCanonicalModule (k := k) x N I σ u)
    (extendedMixedCanonicalModule (k := k) x N I σ u)
    (mixedNativeSectionsIso x N I σ u hx hN htame)

end Mixed
end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
