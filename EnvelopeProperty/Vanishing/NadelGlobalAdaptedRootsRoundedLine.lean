import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsGlobalCartier
import EnvelopeProperty.Vanishing.NadelGlobalAdaptedRootsWholePowers
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealPowers
import EnvelopeProperty.AlgGeom.BundleTensorPowerTensor

/-! # The actual rounded line on the entire original adapted normalization

The actual ideal is the finite product of powers of ALL original whole row
ideals. Its literal power equality constructs the actual tensor-power line
comparison internally. No line-power isomorphism is an incoming premise.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open scoped BigOperators
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finite_product_isInvertible {Y : Scheme.{u}} {ι : Type*}
    (s : Finset ι) (I : ι → Y.IdealSheafData) (hI : ∀ i ∈ s, (I i).IsInvertible) :
    (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top] using
      (Scheme.IdealSheafData.isInvertible_top (X := Y))
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hI i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hI j (Finset.mem_insert_of_mem hj)))

private theorem finite_product_comap {Y Z : Scheme.{u}} {ι : Type*}
    (s : Finset ι) (I : ι → Y.IdealSheafData) (g : Z ⟶ Y) :
    (∏ i ∈ s, I i).comap g = ∏ i ∈ s, (I i).comap g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Scheme.IdealSheafData.comap_mul, ih]

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    Scheme.Modules.tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)

/-- The entire original ideal product retains EVERY original row. -/
def wholeRoundedIdeal (a : F.ι → ℕ) :
    (normalizedScheme (OriginalData.data F n L m σ)).IdealSheafData :=
  ∏ i, wholeRowIdeal F n L m σ hL i ^ a i

/-- The original integral base line whose pullback is the desired power. -/
def clearedRoundedIdeal (a : F.ι → ℕ) (d : ℕ) : X.IdealSheafData :=
  ∏ i, F.component i ^ (a i * (d / m i))

/-- The SAME original rounded cover line, before any ampleness argument. -/
def wholeRoundedLine (M : X.Modules) (a : F.ι → ℕ) :
    (normalizedScheme (OriginalData.data F n L m σ)).Modules :=
  Scheme.Modules.tensorObj ((pullback (normalizedToOriginal (OriginalData.data F n L m σ))).obj M)
    (wholeRoundedIdeal F n L m σ hL a).toModules

variable {k : Type u} [Field k] [PerfectField k]
  (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).IsSnc)
  (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
  (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

include hD f hG hRows hm hfield

/-- The literal product of ALL original whole row ideals is Cartier. -/
theorem wholeRoundedIdeal_isInvertible (a : F.ι → ℕ) :
    (wholeRoundedIdeal F n L m σ hL a).IsInvertible := by
  classical
  apply finite_product_isInvertible
  intro i _
  exact Scheme.IdealSheafData.isInvertible_pow
    (wholeRowIdeal_isInvertible F n L m σ hL hD f hG hRows hm hfield i) (a i)

/-- The literal original rounded ideal has the exact original cleared power.
The arithmetic divisibility premise does not contain a geometric comparison. -/
theorem wholeRoundedIdeal_power (a : F.ι → ℕ) (d : ℕ) (hd : ∀ i, m i ∣ d) :
    wholeRoundedIdeal F n L m σ hL a ^ d =
      (clearedRoundedIdeal F m a d).comap
        (normalizedToOriginal (OriginalData.data F n L m σ)) := by
  classical
  unfold wholeRoundedIdeal clearedRoundedIdeal
  rw [← Finset.prod_pow, finite_product_comap]
  apply Finset.prod_congr rfl
  intro i _
  have hi := wholeRowIdeal_power F n L m σ hL hD f hG hRows hm hfield i
  have hexp : a i * d = m i * (a i * (d / m i)) := by
    calc
      a i * d = a i * (m i * (d / m i)) :=
        congrArg (fun t : ℕ => a i * t) (Nat.mul_div_cancel' (hd i)).symm
      _ = m i * (a i * (d / m i)) := by ac_rfl
  rw [← pow_mul, hexp, pow_mul, hi, Scheme.IdealSheafData.comap_pow]

omit f hG hRows hm hfield [IsIntegral X] in
private theorem clearedRoundedIdeal_isInvertible (a : F.ι → ℕ) (d : ℕ) :
    (clearedRoundedIdeal F m a d).IsInvertible := by
  classical
  apply finite_product_isInvertible
  intro i _
  exact Scheme.IdealSheafData.isInvertible_pow (hD i) _

/-- Invertibility of the same actual cover line is produced from whole row ideals. -/
theorem wholeRoundedLine_isInvertible (M : X.Modules) (hM : IsInvertible M)
    (a : F.ι → ℕ) : IsInvertible (wholeRoundedLine F n L m σ hL M a) :=
  (hM.pullback _).tensorObj
    (wholeRoundedIdeal_isInvertible F n L m σ hL hD f hG hRows hm hfield a).isInvertibleModule_toModules

/-- Exact whole power comparison for the SAME original rounded root line.
It is constructed from original geometry, never supplied as a certificate.
No target integrality, finite morphism or flatness hypothesis is inserted. -/
def wholeRoundedLinePowerIso (M : X.Modules)
    (a : F.ι → ℕ) (d : ℕ) (hd : ∀ i, m i ∣ d) :
    bundleTensorPower (wholeRoundedLine F n L m σ hL M a) d ≅
      (pullback (normalizedToOriginal (OriginalData.data F n L m σ))).obj
        (Scheme.Modules.tensorObj (bundleTensorPower M d) (clearedRoundedIdeal F m a d).toModules) := by
  let π := normalizedToOriginal (OriginalData.data F n L m σ)
  let P := (pullback π).obj M
  let I := wholeRoundedIdeal F n L m σ hL a
  let K := clearedRoundedIdeal F m a d
  have hI : I.IsInvertible :=
    wholeRoundedIdeal_isInvertible F n L m σ hL hD f hG hRows hm hfield a
  have hK : K.IsInvertible := clearedRoundedIdeal_isInvertible F m hD a d
  have hp : I ^ d = K.comap π :=
    wholeRoundedIdeal_power F n L m σ hL hD f hG hRows hm hfield a d hd
  have hKπ : (K.comap π).IsInvertible := hp ▸ Scheme.IdealSheafData.isInvertible_pow hI d
  let : IsIso (K.toModulesComapPullbackMap π) :=
    hK.toModulesComapPullbackMap_isIso_of_isInvertible_comap π hKπ
  let : (pullback π).Monoidal := Scheme.Modules.pullbackMonoidal π
  exact BundleTensorPowerPullback.powerIso
      (ModularCurves.monoidalTensorObjIso P I.toModules).symm d ≪≫
    BundleTensorPowerTensor.powerTensorIso P I.toModules d ≪≫
    ((BundleTensorPowerPullback.pullbackIso π M d).symm ⊗ᵢ
      (NadelBlowupCanonicalIdealPowers.tensorPowerIso I hI d ≪≫
        eqToIso (congrArg Scheme.IdealSheafData.toModules hp) ≪≫
        (asIso (K.toModulesComapPullbackMap π)).symm)) ≪≫
    Functor.Monoidal.μIso (pullback π) (bundleTensorPower M d) K.toModules ≪≫
    (pullback π).mapIso
      (ModularCurves.monoidalTensorObjIso (bundleTensorPower M d) K.toModules)

end EnvelopeProperty.Vanishing.NadelGlobalAdaptedRoots
