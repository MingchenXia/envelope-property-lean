import EnvelopeProperty.Char0.RelativeHomogeneousSectionLiftGeometry
import EnvelopeProperty.Char0.NadelClearedTwistProjective
import EnvelopeProperty.AlgGeom.ClosedProjectiveSerreVanishing

/-! # One internally produced bound lifts all original relative projective sections -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Scheme.Modules MvPolynomial

noncomputable section
universe u

namespace EnvelopeProperty.Char0.RelativeHomogeneousSectionLift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra

private theorem H_subsingleton_of_iso {P : Scheme.{u}} {M N : P.Modules}
    (e : M ≅ N) (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology P) q).mapIso
    ((SheafOfModules.toSheaf P.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology P) q).obj
        ((SheafOfModules.toSheaf P.ringCatSheaf).obj N)) := h
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {N : ℕ} {Y : Scheme.{u}}

/-- A fixed actual closed immersion internally gives ONE bound after which
EVERY original native line-section pullback is surjective, over the SAME R. -/
theorem exists_restriction_surjective_bound
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i] :
    ∃ b : ℕ, ∀ e : ℕ, b ≤ e →
      Function.Surjective (affinePullbackUnitTop i
        (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ))) := by
  let P := Proj (homogeneousSubmodule (Fin (N + 1)) R)
  let p := homogeneousProjπ (R := R) (σ := Fin (N + 1))
  let : LocallyOfFiniteType p := homogeneousProjπ_locallyOfFiniteType (R := R)
  let : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  let : (unitObj P).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj P).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  let : (unitObj Y).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : ((pushforward i).obj (unitObj Y)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom i
  let K := ModularCurves.idealModule i
  let : K.IsQuasicoherent := isQuasicoherent_kernel (FiniteClosedIdealEuler.quotientMap i)
  let : K.IsFiniteType := isFiniteType_kernel (FiniteClosedIdealEuler.quotientMap i)
  obtain ⟨b, hb⟩ := ClosedProjectiveSerreVanishing.exists_sheafCohomology_bound
    (𝟙 P) K (0 : Fin (N + 1))
  refine ⟨b, fun e he => ?_⟩
  let L := coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ)
  let eL : K ⊗ (Scheme.Modules.pullback (𝟙 P)).obj L ≅ K ⊗ L :=
    Iso.refl K ⊗ᵢ (pullbackId P).app L
  let : Subsingleton (CategoryTheory.Sheaf.H (K ⊗ L).sheaf 1) :=
    H_subsingleton_of_iso eL.symm 1 (hb e he 0)
  have hu := unitTop_surjective_of_kernel_tensor_H_one i L
    (coordinateHyperplaneTwist_isInvertible (0 : Fin (N + 1)) (e : ℤ))
  have hnative : affinePullbackUnitTop i L =
      ((pullbackPushforwardAdjunction i).unit.app L).app ⊤ := by
    funext s
    change ((Scheme.Modules.pullback i).obj L).presheaf.map (𝟙 (op (⊤ : Y.Opens)))
      (((pullbackPushforwardAdjunction i).unit.app L).app ⊤ s) = _
    exact ConcreteCategory.congr_hom
      (((Scheme.Modules.pullback i).obj L).presheaf.map_id (op ⊤)) _
  rw [hnative]
  exact hu

/-- Every original section of every larger twist has a genuine original ambient
section lift under the actual native pullback, without any lifting premise. -/
theorem exists_section_lift_bound
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i] :
    ∃ b : ℕ, ∀ e : ℕ, b ≤ e →
      ∀ s : Γ((Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ)), ⊤),
      ∃ t : Γ(coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ), ⊤),
        affinePullbackUnitTop i _ t = s :=
  exists_restriction_surjective_bound i

/-- The SAME bound lifts every section of the SAME original H-power, through
the internally proved original native hyperplane-power comparison. -/
theorem exists_power_section_lift_bound
    (i : Y ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i] :
    ∃ b : ℕ, ∀ e : ℕ, b ≤ e →
      ∀ s : Γ(CanonicalGeometry.bundleTensorPower (NadelClearedTwist.hyperplane i) e, ⊤),
      ∃ t : Γ(coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (e : ℤ), ⊤),
        (NadelClearedTwist.hyperplanePowerIso i e).inv.app ⊤
          (affinePullbackUnitTop i _ t) = s := by
  obtain ⟨b, hb⟩ := exists_section_lift_bound i
  refine ⟨b, fun e he s => ?_⟩
  obtain ⟨t, ht⟩ := hb e he ((NadelClearedTwist.hyperplanePowerIso i e).hom.app ⊤ s)
  refine ⟨t, ?_⟩
  rw [ht]
  exact iso_hom_inv_app_applyT (NadelClearedTwist.hyperplanePowerIso i e) (op ⊤) s

end EnvelopeProperty.Char0.RelativeHomogeneousSectionLift
