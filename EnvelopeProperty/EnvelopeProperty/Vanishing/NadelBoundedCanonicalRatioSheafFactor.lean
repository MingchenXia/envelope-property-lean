import EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomOriginalFactor
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalRatioPowers
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareTensor

/-! # Produce the actual canonical whole-ideal factor on original ratio charts

The original ratio geometry internally produces the original source frame,
ordinary differential divisibility and membership in the same whole ideal.
The checked original affine canonical computation gives the full sheaf factor.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules
open scoped BigOperators TensorProduct
universe u
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalRatioSheafFactor
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelAdaptedChartMatching NadelGlobalAdaptedModel
open CyclicSectionSNCUniformFramedCharts
open NadelCanonicalMixed.Split NadelCanonicalBaseChange NadelGlobalCanonicalTrace
open NadelBoundedCanonicalSourceFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local infixr:80 " ≫ₛ " => CategoryStruct.comp (obj := Scheme)

run_cmd
  let source := `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomOriginalFactor
  let name := Lean.mkPrivateNameCore source
    `EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineHomOriginalFactor.exists_actual_affineHom_original_factor
  unless (← Lean.getEnv).contains name do throwError "missing checked original coefficient map factor"
  Lean.Elab.Command.modifyScope fun scope =>
    {scope with openDecls := Lean.OpenDecl.explicit `actualAffineHomOriginalFactor name :: scope.openDecls}

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
  (L : F.ι → X.Modules) (m : F.ι → ℕ)
  (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
    tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
  (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
  (y : X) (U : X.affineOpens) [Nonempty U.1] (v : Fin n → Γ(X, U.1))
  (c : {i : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).ι //
    y ∈ ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).component i).support} → Fin n)
  (j₀ : F.ι → Fin (n + 1))
  (w : Fin (OriginalData.data F n L m σ).length → (Γ(X, U.1))ˣ)
  {k : Type u} [Field k] (f : Scheme.Hom X (Spec (.of k))) [SmoothOfRelativeDimension n f]
  (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
  (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))
  (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).IsSnc)
  (hcomp : ∀ i, ((NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
    (OriginalData.ideals F n L m σ hL hD)).component i.1).ideal U = Ideal.span {v (c i)})
  (hyU : y ∈ U.1)
  (habsent : ∀ i, y ∉ (OriginalData.ideals F n L m σ hL hD i (j₀ i)).support)
  (e : NadelAuxiliaryMulticoverCharts.Frames U.1 (OriginalData.data F n L m σ))
  (hw : ∀ i, WholeChart.coefficients U (OriginalData.data F n L m σ) e i =
    (w i : Γ(X, U.1)) * uniformBranches y U v c (OriginalData.branchIndex F n L m σ hL hD i) *
      uniformBranches y U v c (OriginalData.auxiliaryIndex F n L m σ hL hD i))


local instance boundedRatioBaseAffine : IsAffine U.1.toScheme := U.2
local notation "D" => OriginalData.data F n L m σ
local notation "Bᵣ" => RatioRing F n L m σ hL hD y U v c j₀ w
local notation "π" => normalizedToOriginal D
local notation "α" => originalToRatio F n L m σ hL hD y U v c j₀ e w hw habsent
local notation "C" => Model.canonicalChart F n L m σ hL hD y U v c j₀ w
  f het hcinj hm htame hG hcomp hyU habsent e hw

/-- On the SAME actual original canonical ratio chart, the SAME actual
canonical differential factors through the SAME literal whole rounded
ideal. The original source frame, target smoothness, RAW image bound and
actual ideal membership are all produced internally from original geometry. -/
theorem exists_canonicalRoundedIdeal_affine_factor
    (a : F.ι → ℕ) (ha : ∀ i, a i < m i) :
    let _ := f.sectionsAlgebra U.1
    let p : Scheme.Hom (Spec (.of Bᵣ)) (Spec (.of Γ(X, U.1))) :=
      Spec.map (CommRingCat.ofHom (R := Γ(X, U.1)) (S := Bᵣ) (algebraMap Γ(X, U.1) Bᵣ))
    let ΩA := exteriorCotangentSheaf (K := k) (X := Spec (.of Γ(X, U.1))) (U.2.fromSpec ≫ₛ f) n
    let ΩB := exteriorCotangentSheaf (K := k) (X := Spec (.of Bᵣ)) (p ≫ₛ (U.2.fromSpec ≫ₛ f)) n
    let J := (wholeRoundedIdeal F n L m σ hL a).comap
      ((C).hom ≫ₛ (π ⁻¹ᵁ U.1).ι)
    ∃ θ : (pullback p).obj ΩA ⟶ Scheme.Modules.tensorObj ΩB J.toModules,
      θ ≫ SchemeTensorObjMorphisms.tensorObjIdealMap ΩB J.toModules J.toModulesInclusion =
        exteriorCotangentSheafPullbackMap (K := k) (X := Spec (.of Γ(X, U.1))) (Y := Spec (.of Bᵣ)) (U.2.fromSpec ≫ₛ f) p n := by
  let _ := f.sectionsAlgebra U.1
  have hbase : U.2.fromSpec ≫ₛ f = affineStructuralMap k (.of Γ(X, U.1)) := by
    have hh := IsAffineOpen.SpecMap_appLE_fromSpec f
      (isAffineOpen_top (Spec (.of k))) U.2 le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hh
    exact hh.symm
  dsimp only
  rw [hbase]
  let A := Γ(X, U.1)
  let φ : A →ₐ[k] Bᵣ := IsScalarTower.toAlgHom k A Bᵣ
  let ψ : CommRingCat.of A ⟶ CommRingCat.of Bᵣ :=
    CommRingCat.ofHom (R := A) (S := Bᵣ) (algebraMap A Bᵣ)
  have hfield (t : k) : ψ.hom (algebraMap k A t) = algebraMap k Bᵣ t := φ.commutes t
  let J := (wholeRoundedIdeal F n L m σ hL a).comap
    ((C).hom ≫ₛ (π ⁻¹ᵁ U.1).ι)
  have hx : (MvPolynomial.aeval (R := k) v).toRingHom.Etale :=
    (etale_toAffineSpace_iff f U.2 v).mp het
  let : SmoothOfRelativeDimension n (affineStructuralMap k (.of Bᵣ)) := by
    exact Joined.ratio_smoothOfRelativeDimension F n
      (OriginalData.ideals F n L m σ hL hD) j₀ y U v c f het hcinj
      (Joined.degree F n m) (OriginalData.orderedUnits F n L m σ U w)
      (fun i => hm (Joined.row F n i)) (fun i => htame (Joined.row F n i))
  let a₀ : MvPolynomial (Fin n) k →ₐ[k] A := MvPolynomial.aeval v
  have haF : a₀.toRingHom.FormallyEtale := by
    let : Algebra (MvPolynomial (Fin n) k) A := a₀.toRingHom.toAlgebra
    let : Algebra.Etale (MvPolynomial (Fin n) k) A := hx
    exact inferInstanceAs (Algebra.FormallyEtale (MvPolynomial (Fin n) k) A)
  let r := canonicalRoundedMonomial F n L m σ hL hD y U v c j₀ w a
  let rΓ : Γ(Spec (.of Bᵣ), ⊤) := (Scheme.ΓSpecIso (.of Bᵣ)).inv r
  have hr : rΓ ∈ J.ideal ⟨⊤, isAffineOpen_top (Spec (.of Bᵣ))⟩ := by
    rw [canonicalRoundedIdeal_top F n L m σ hL hD y U v c j₀ w
      f het hcinj hm htame hG hcomp hyU habsent e hw a]
    exact Ideal.subset_span (Set.mem_singleton rΓ)
  let G := exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (v j))
  have htop : topPullback (R := k) (A := A) (B := Bᵣ) n G =
      exteriorPower.ιMulti Bᵣ n (fun j => KaehlerDifferential.D k Bᵣ (ψ.hom (v j))) := by
    rw [topPullback_wedge]
    simp only [KaehlerDifferential.map_D]
    rfl
  obtain ⟨ω, hω⟩ := NadelBoundedCanonicalRatioPowers.canonicalRoundedMonomial_topDifferential_factor
    F n L m σ hL hD y U v c j₀ w f hcinj hm a ha
  have hraw : ∃ ω : affineCanonicalModule k Bᵣ n,
      exteriorPower.ιMulti Bᵣ n
        (fun j => KaehlerDifferential.D k Bᵣ (ψ.hom (originalCoordinates a₀ j))) = r • ω := by
    refine ⟨ω, ?_⟩
    simpa only [originalCoordinates, a₀, MvPolynomial.aeval_X] using htop.symm.trans hω
  have hfinal := actualAffineHomOriginalFactor (K := k) (.of A) (.of Bᵣ) ψ hfield n a₀ haF J r hr hraw
  exact hfinal

end EnvelopeProperty.Vanishing.NadelBoundedCanonicalRatioSheafFactor
