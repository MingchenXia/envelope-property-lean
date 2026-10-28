import EnvelopeProperty.AlgGeom.ClosedProjectiveSerreVanishing
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorFiniteType

/-! # Uniform ample Serre vanishing for arbitrary finite-type quasicoherent modules

These are eventual vanishing theorems.  They supply the large-power endpoint
of the positive Hodge-diagonal argument, without assuming Kodaira or Nadel vanishing.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules

noncomputable section
universe u v

namespace EnvelopeProperty.SchemeAmpleCoherentSerreVanishing

open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem cohomology_subsingleton_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (q : ℕ) (hM : Subsingleton (CategoryTheory.Sheaf.H M.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H N.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := hM
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- One threshold works in all positive degrees for every larger ample power,
with any fixed finite-type quasicoherent module as tensor factor. -/
theorem exists_sheafCohomology_bound {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower A m ⊗ M : X.Modules).sheaf (q + 1)) := by
  classical
  obtain ⟨r, hr, n, i, hi, _hip, ⟨e⟩⟩ := hA.2
  let : IsClosedImmersion i := hi
  have hh (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        ((M ⊗ bundleTensorPower A a.val) ⊗ (Scheme.Modules.pullback i).obj
          (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (d : ℤ)) :
            X.Modules).sheaf (q + 1)) := by
    let L := bundleTensorPower A a.val
    have hL : IsInvertible L :=
      TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible a.val
    let : (M ⊗ L).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight M L hL
    let : (M ⊗ L).IsFiniteType :=
      SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight M L hL
    exact ClosedProjectiveSerreVanishing.exists_sheafCohomology_bound i
      (M ⊗ L) (0 : Fin (n + 1))
  choose N hN using hh
  let T := Finset.univ.sup N
  refine ⟨T * r, fun m hm q => ?_⟩
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  have hd : T ≤ m / r := (Nat.le_div_iff_mul_le hr).mpr hm
  have hv := hN a (m / r) ((Finset.le_sup (f := N) (Finset.mem_univ a)).trans hd) q
  let E : ((M ⊗ bundleTensorPower A a.val) ⊗ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) ((m / r : ℕ) : ℤ))) ≅
      bundleTensorPower A m ⊗ M :=
    (Iso.refl (M ⊗ bundleTensorPower A a.val) ⊗ᵢ
      (PositivePowerProjectiveGeneration.blockTwistIso i A r (0 : Fin (n + 1)) e
        (m / r)).symm) ≪≫
      (α_ M (bundleTensorPower A a.val) (bundleTensorPower A (r * (m / r)))) ≪≫
      (Iso.refl M ⊗ᵢ
        (TensorPowerBaseIdealGrading.tensorPowerAddIso A a.val (r * (m / r)) ≪≫
          eqToIso (congrArg (bundleTensorPower A) (Nat.mod_add_div m r)))) ≪≫
      (β_ M (bundleTensorPower A m))
  exact cohomology_subsingleton_of_iso E (q + 1) hv

/-- A finite family admits one threshold, simultaneously for every member
and every positive cohomology degree. The empty family is included. -/
theorem exists_uniform_sheafCohomology_bound
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    {ι : Type v} [Fintype ι] (M : ι → X.Modules)
    [∀ i, (M i).IsQuasicoherent] [∀ i, (M i).IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i : ι, ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower A m ⊗ M i : X.Modules).sheaf (q + 1)) := by
  classical
  choose N hN using fun i => exists_sheafCohomology_bound p A hA (M i)
  exact ⟨Finset.univ.sup N, fun m hm i q =>
    hN i m ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hm) q⟩

/-- Above the dimension diagonal, all cohomology degrees are positive.
Thus an arbitrary finite coherent Hodge-shaped family is eventually zero
on every such diagonal, with one bound independent of the diagonal. -/
theorem exists_upper_diagonal_bound
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (n : ℕ) (M : Fin (n + 1) → X.Modules)
    [∀ i, (M i).IsQuasicoherent] [∀ i, (M i).IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ t : ℕ, n < t → ∀ i : Fin (n + 1),
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower A m ⊗ M i : X.Modules).sheaf (t - i.val)) := by
  obtain ⟨N, hN⟩ := exists_uniform_sheafCohomology_bound p A hA M
  refine ⟨N, fun m hm t ht i => ?_⟩
  have hi := i.isLt
  have he : t - i.val = (t - i.val - 1) + 1 := by omega
  rw [he]
  exact hN m hm i (t - i.val - 1)

end EnvelopeProperty.SchemeAmpleCoherentSerreVanishing
