import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Actual finite products retain the same original module localization -/
open scoped BigOperators
noncomputable section
namespace EnvelopeProperty.FiniteProductModuleLocalization

variable {A : Type*} [CommRing A] {ι : Type*}
variable {M N : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
variable [∀ i, Module A (M i)] [∀ i, Module A (N i)]

/-- The actual WHOLE original coordinate map of the module family. -/
def piMap (a : ∀ i, M i →ₗ[A] N i) : (∀ i, M i) →ₗ[A] (∀ i, N i) where
  toFun x i := a i (x i)
  map_add' x y := funext fun i => (a i).map_add (x i) (y i)
  map_smul' r x := funext fun i => (a i).map_smul r (x i)

/-- Every original coordinate and its actual original map are retained. -/
theorem piMap_apply (a : ∀ i, M i →ₗ[A] N i) (x : ∀ i, M i) (i : ι) :
    piMap a x i = a i (x i) := rfl

/-- A finite family of TRUE localizations gives a TRUE localization of the
ENTIRE actual product at the SAME multiplicative set, including the empty case. -/
theorem piMap_isLocalizedModule [Finite ι] (T : Submonoid A)
    (a : ∀ i, M i →ₗ[A] N i) [∀ i, IsLocalizedModule T (a i)] :
    IsLocalizedModule T (piMap a) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun y : ∀ i, N i => fun i => (s : A) • y i)
    have hi (i : ι) : Function.Bijective (fun y : N i => (s : A) • y) :=
      (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (a i) s)
    refine ⟨fun x y h => funext fun i => (hi i).1 (congrFun h i), fun y => ?_⟩
    choose x hx using fun i => (hi i).2 (y i)
    exact ⟨x, funext hx⟩
  · intro y
    choose z hz using fun i => IsLocalizedModule.surj T (a i) (y i)
    let c : T := ∏ i, (z i).2
    refine ⟨⟨fun i => ((∏ j ∈ Finset.univ.erase i, (z j).2 : T) : A) • (z i).1, c⟩, ?_⟩
    funext i
    change (c : A) • y i =
      a i (((∏ j ∈ Finset.univ.erase i, (z j).2 : T) : A) • (z i).1)
    have hzi : ((z i).2 : A) • y i = a i (z i).1 := hz i
    rw [map_smul, ← hzi, ← mul_smul]
    apply congrArg (fun r : A => r • y i)
    exact congrArg (fun s : T => (s : A))
      (Finset.prod_erase_mul Finset.univ (fun j => (z j).2) (Finset.mem_univ i)).symm
  · intro x y hxy
    choose s hs using fun i => IsLocalizedModule.exists_of_eq
      (S := T) (f := a i) (congrFun hxy i)
    refine ⟨∏ i, s i, ?_⟩
    funext i
    have hc : ((∏ j, s j : T) : A) =
        ((∏ j ∈ Finset.univ.erase i, s j : T) : A) * (s i : A) :=
      congrArg (fun t : T => (t : A))
        (Finset.prod_erase_mul Finset.univ s (Finset.mem_univ i)).symm
    change ((∏ j, s j : T) : A) • x i = ((∏ j, s j : T) : A) • y i
    rw [hc, mul_smul, mul_smul]
    exact congrArg (fun z : M i => ((∏ j ∈ Finset.univ.erase i, s j : T) : A) • z) (hs i)

end EnvelopeProperty.FiniteProductModuleLocalization
