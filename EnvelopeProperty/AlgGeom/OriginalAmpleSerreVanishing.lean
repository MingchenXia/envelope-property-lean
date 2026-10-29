import EnvelopeProperty.AlgGeom.ClosedProjectiveSerreVanishingFintype
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorFiniteType
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading

/-! # Serre vanishing for the original geometrically ample line powers -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules MvPolynomial

noncomputable section
universe u

namespace EnvelopeProperty.OriginalAmpleSerreVanishing

open CanonicalGeometry

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory

/-- A single actual geometric power isomorphism determines every original
multiple power, including the genuine zeroth-power unit comparison. -/
def powerMulPullbackTwistIso {R : Type u} [CommRing R] {σ : Type} {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (L : X.Modules) (r : ℕ) (j : σ)
    (η : bundleTensorPower L r ≅ (Scheme.Modules.pullback f).obj
      (coordinateHyperplaneTwist (R := R) j (1 : ℤ))) (d : ℕ) :
    bundleTensorPower L (r*d) ≅ (Scheme.Modules.pullback f).obj
      (coordinateHyperplaneTwist (R := R) j (d : ℤ)) := by
  let F := Scheme.Modules.pullback f
  let : F.Monoidal := Scheme.Modules.pullbackMonoidal f
  induction d with
  | zero =>
    dsimp only [Nat.mul_zero, bundleTensorPower, coordinateHyperplaneTwist,
      coordinateHyperplanePoleSheafPower]
    exact (ModularCurves.monoidalUnitObjIso X).symm ≪≫ Functor.Monoidal.εIso F
  | succ d ih =>
    let e₀ : bundleTensorPower L (r*(d+1)) ≅ bundleTensorPower L (r*d+r) :=
      eqToIso (congrArg (bundleTensorPower L) (Nat.mul_succ r d))
    let e₁ : coordinateHyperplaneTwist (R := R) j ((d : ℤ)+1) ≅
        coordinateHyperplaneTwist (R := R) j ((d+1 : ℕ) : ℤ) :=
      eqToIso (congrArg (coordinateHyperplaneTwist (R := R) j) (by omega))
    exact e₀ ≪≫ (TensorPowerBaseIdealGrading.tensorPowerAddIso L (r*d) r).symm ≪≫
      (ih ⊗ᵢ η) ≪≫ Functor.Monoidal.μIso F
        (coordinateHyperplaneTwist (R := R) j (d : ℤ))
        (coordinateHyperplaneTwist (R := R) j (1 : ℤ)) ≪≫
      F.mapIso (ProjectiveTwistTensorAddition.tensorIso j j j (d : ℤ) 1 ≪≫ e₁)

/-- One actual positive-power closed embedding gives a single bound for all
larger original line powers and every positive original cohomology degree. -/
theorem exists_sheafCohomology_bound {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}}
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (E L : X.Modules) [E.IsQuasicoherent] [E.IsFiniteType] (hL : IsInvertible L)
    (r : ℕ) (hr : 0 < r) (j : σ)
    (η : bundleTensorPower L r ≅ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) j (1 : ℤ))) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H (E ⊗ bundleTensorPower L m).sheaf (q+1)) := by
  classical
  let A : Fin r → X.Modules := fun a => E ⊗ bundleTensorPower L a.val
  have hqc (a : Fin r) : (A a).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight E _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL a.val)
  have hft (a : Fin r) : (A a).IsFiniteType :=
    SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight E _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL a.val)
  have hex (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        (A a ⊗ (Scheme.Modules.pullback i).obj
          (coordinateHyperplaneTwist (R := R) j (d : ℤ))).sheaf (q+1)) := by
    let : (A a).IsQuasicoherent := hqc a
    let : (A a).IsFiniteType := hft a
    exact ClosedProjectiveSerreVanishingFintype.exists_sheafCohomology_bound i (A a) j
  choose N hN using hex
  let B := Finset.univ.sup N
  refine ⟨r*B, ?_⟩
  intro m hm q
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  let d := m / r
  have hBd : B ≤ d := (Nat.le_div_iff_mul_le hr).mpr
    (by simpa only [Nat.mul_comm] using hm)
  have hd : N a ≤ d := (Finset.le_sup (f := N) (Finset.mem_univ a)).trans hBd
  let γ : A a ⊗ (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) j (d : ℤ)) ≅
      E ⊗ bundleTensorPower L m :=
    (Iso.refl (A a) ⊗ᵢ (powerMulPullbackTwistIso i L r j η d).symm) ≪≫
      α_ E (bundleTensorPower L a.val) (bundleTensorPower L (r*d)) ≪≫
      (Iso.refl E ⊗ᵢ TensorPowerBaseIdealGrading.tensorPowerAddIso L a.val (r*d)) ≪≫
      (Iso.refl E ⊗ᵢ eqToIso (congrArg (bundleTensorPower L)
        (show a.val + r*d = m from Nat.mod_add_div m r)))
  let eH := (CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology X) (q+1)).mapIso
      ((Scheme.Modules.toSheaf X).mapIso γ)
  exact AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso
      (@AddCommGrpCat.isZero_of_subsingleton _ (hN a d hd q)) eH.symm)

end EnvelopeProperty.OriginalAmpleSerreVanishing
