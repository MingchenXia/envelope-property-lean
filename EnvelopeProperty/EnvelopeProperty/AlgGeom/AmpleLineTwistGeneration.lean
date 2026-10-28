import EnvelopeProperty.AlgGeom.AmpleTensorLines

/-! # Actual eventual generation and very ampleness after ANY original invertible twist -/
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.AmpleLineTwistGeneration
open CanonicalGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem tensorInvertible {X : Scheme.{u}} {A B : X.Modules}
    (hA : IsInvertible A) (hB : IsInvertible B) : IsInvertible (A ⊗ B) :=
  (hA.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso A B)

/-- A SAME true very-ample line satisfies the actual positive-power ample
criterion, via its canonical first actual tensor power. -/
theorem isAmple_of_isVeryAmple {R : Type u} [CommRing R] {X : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} {A : X.Modules} (hA : SchemeLineAmpleness.IsVeryAmple p A) :
    SchemeLineAmpleness.IsAmple p A :=
  ⟨hA.isInvertible, 1, Nat.zero_lt_one,
    SchemeAmpleClosedRestriction.veryAmple_of_iso hA (bundleTensorLeftUnitIso A).symm⟩

/-- ANY SAME original invertible twist of an original geometrically ample
line has finite genuine global generators at EVERY sufficiently large actual exponent. -/
theorem exists_eventual_generatingSections {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (B : X.Modules) (hB : IsInvertible B) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ G : (bundleTensorPower A m ⊗ B).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨r, hr, n, i, hi, _hip, ⟨e⟩⟩ := hA.2
  let : IsClosedImmersion i := hi
  have hh (a : Fin r) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : ((B ⊗ bundleTensorPower A a.val) ⊗ (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) (d : ℤ))).GeneratingSections,
        G.IsFiniteType := by
    let M := B ⊗ bundleTensorPower A a.val
    let hM := tensorInvertible hB (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible a.val)
    let : M.IsQuasicoherent := hM.isQuasicoherent
    let : M.IsFinitePresentation := hM.isFinitePresentation
    let : M.IsFiniteType := inferInstance
    exact ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections i M (0 : Fin (n + 1))
  choose N hN using hh
  let T := Finset.univ.sup N
  refine ⟨T * r, fun m hm => ?_⟩
  let a : Fin r := ⟨m % r, Nat.mod_lt m hr⟩
  have hd : T ≤ m / r := (Nat.le_div_iff_mul_le hr).mpr hm
  obtain ⟨G, hG⟩ := hN a (m / r) ((Finset.le_sup (f := N) (Finset.mem_univ a)).trans hd)
  let : G.IsFiniteType := hG
  let E : ((B ⊗ bundleTensorPower A a.val) ⊗ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) ((m / r : ℕ) : ℤ))) ≅
      bundleTensorPower A m ⊗ B :=
    (Iso.refl (B ⊗ bundleTensorPower A a.val) ⊗ᵢ
      (PositivePowerProjectiveGeneration.blockTwistIso i A r (0 : Fin (n + 1)) e (m / r)).symm) ≪≫
      (α_ B (bundleTensorPower A a.val) (bundleTensorPower A (r * (m / r)))) ≪≫
      (Iso.refl B ⊗ᵢ
        (TensorPowerBaseIdealGrading.tensorPowerAddIso A a.val (r * (m / r)) ≪≫
          eqToIso (congrArg (bundleTensorPower A) (Nat.mod_add_div m r)))) ≪≫
      (β_ B (bundleTensorPower A m))
  exact ⟨G.ofEpi E.hom, inferInstance⟩

/-- ANY actual original invertible twist becomes geometrically very ample
at EVERY sufficiently large original ample-line exponent. -/
theorem exists_eventual_isVeryAmple {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) (A : X.Modules) (hA : SchemeLineAmpleness.IsAmple p A)
    (B : X.Modules) (hB : IsInvertible B) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower A m ⊗ B) := by
  obtain ⟨r, _hr, hVA⟩ := hA.2
  obtain ⟨N, hN⟩ := exists_eventual_generatingSections p A hA B hB
  refine ⟨N + r, fun m hm => ?_⟩
  have hd : N ≤ m - r := by omega
  have he : r + (m - r) = m := by omega
  obtain ⟨G, hG⟩ := hN (m - r) hd
  have hV := VeryAmpleTensorGenerated.isVeryAmple_tensor p (bundleTensorPower A r)
    (bundleTensorPower A (m - r) ⊗ B) hVA
    (tensorInvertible (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA.isInvertible (m - r)) hB)
    G hG
  exact SchemeAmpleClosedRestriction.veryAmple_of_iso hV
    ((α_ (bundleTensorPower A r) (bundleTensorPower A (m - r)) B).symm ≪≫
      ((TensorPowerBaseIdealGrading.tensorPowerAddIso A r (m - r) ≪≫
        eqToIso (congrArg (bundleTensorPower A) he)) ⊗ᵢ Iso.refl B))

/-- One INTERNALLY derived true exponent threshold makes EVERY original line
in ANY finite original family and its actual dual very ample after the SAME ample power. -/
theorem exists_uniform_eventual_isVeryAmple {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of R)) (A : X.Modules)
    (hA : SchemeLineAmpleness.IsAmple p A) {ι : Type v} [Fintype ι]
    (B : ι → X.Modules) (hB : ∀ i, IsInvertible (B i)) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ i : ι,
      SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower A m ⊗ B i) ∧
        SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower A m ⊗ dualObj (B i)) := by
  classical
  have hh (i : ι) : ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower A m ⊗ B i) ∧
        SchemeLineAmpleness.IsVeryAmple p (bundleTensorPower A m ⊗ dualObj (B i)) := by
    obtain ⟨N, hN⟩ := exists_eventual_isVeryAmple p A hA (B i) (hB i)
    obtain ⟨M, hM⟩ := exists_eventual_isVeryAmple p A hA (dualObj (B i)) (hB i).dual
    exact ⟨max N M, fun m hm => ⟨hN m ((le_max_left _ _).trans hm), hM m ((le_max_right _ _).trans hm)⟩⟩
  choose N hN using hh
  exact ⟨Finset.univ.sup N, fun m hm i => hN i m
    ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hm)⟩
end EnvelopeProperty.AmpleLineTwistGeneration
