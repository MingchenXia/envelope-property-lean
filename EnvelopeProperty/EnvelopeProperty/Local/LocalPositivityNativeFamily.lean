/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Local.LocalPositivityNativeAssembly
import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalOriginalCentralNefTC
import EnvelopeProperty.Local.PLOriginalModelCompatibilityModelPotentialIdentity
import EnvelopeProperty.Local.PLOriginalModelCompatibilityAuxiliaryLine
import EnvelopeProperty.Local.PLNativeTwistLineAmpleness
import EnvelopeProperty.AlgGeom.PLModelAuxiliaryPolarizationNormalized
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedWholeGeneratorExactFS
import EnvelopeProperty.AlgGeom.ProjectiveTwistTensorAddition
import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorPotential

/-!
# Locally convex functions admit native potential families

This file proves the upstream half of the native-scheme proof of Fang–Han–Xia, *The envelope
property for unibranch projective varieties*, Lemma 5.5 (`lem:local-PL-positivity`): a locally
`O(a)`-convex function `φ` on a projectively normal `X = V(I) ⊆ ℙᴹ` admits a native potential
family (`ProjSubvariety.NativePotentialFSFamily`; plan
`.archon-horizon/scratch/ep/PLAN-LP-ASSEMBLY.md` §4). Together with
`LocalPositivity.of_nativePotentialFSFamily` this gives the class `LocalPositivity k` (file
`Local/LocalPositivityInstance.lean`).

## The proof

* (Central nefness, on the explicit model.) By
  `NumericalOriginalCentralNef.exists_prescribedClass_originalCentralNef_nativeProductIdeal`, there
  are `r ≥ 1`, `d = r a`, `B ∈ ℤ` and homogeneous, scaling-invariant ideals `I, J` of `k[t][x]`
  containing powers of `t`, such that on the normalized simultaneous blowup `𝒳` of
  `X × 𝔸¹` along `I, J` one has `r φ(y) = W(y) + B` at every point (`W` the ratio weight), and the
  twisted ratio line `M = q^* O(d) ⊗ I ⊗ J^∨` is nef on the central fibre (BJ22 §§2–4; FHX,
  proof of Lemma 5.5).
* (Test configuration.) `𝒳` is a test configuration `C` of `X`
  (`normalizedSimultaneousNativeTestConfiguration`), `M` is linearized with fibre-one line
  `L = O(d)|_X`, and the model potential satisfies `pot_M = r φ - B`
  (`normalizedSimultaneousNativeModelPotential_eq_convex`).
* (Auxiliary polarization.) The tautological twist `H = q^* O(q) ⊗ ν^*(IJ)`, `q > 0`, is ample on
  the central fibre, linearized, with fibre-one line `K = O(q)|_X`.
* (Exact FS.) For `b ≥ 1`, `M^b ⊗ H` is ample on the central fibre (nef + ample), and
  `b pot_M + pot_H` is an exact finite FS function of class `1` of
  `L^b ⊗ K ≅ O(b d + q)` (`isFinFS_power_tensor_potential_sum_of_central_nef`; the isomorphism is
  `ProjSubvariety.nativeTwistPowerTensorIso`).
* (Boundedness of `pot_H`.) `pot_H` is itself an exact finite FS function of class `1` of `K`
  (`isFinFS_modelPotential_of_central_ample`), hence, read on `X^an`, a finite FS function
  (link 8, `ProjSubvariety.isFiniteFS_of_nativeIsFinFS`), hence continuous and bounded on the
  compact space `X^an`.

## Main results

* `ProjSubvariety.nativeTwistPowerTensorIso`: `O(d)^{⊗ b} ⊗ O(q)^{⊗ a} ≅ O(d b + q a)` on
  `X.NativeScheme`.
* `ProjSubvariety.IsFiniteFS.exists_abs_le`: finite FS functions on `X^an` are bounded.
* `ProjSubvariety.nativePotentialFSFamily_of_testConfiguration`: a test configuration with a
  centrally nef linearized line `M` (fibre-one line `O(d)`, model potential `r φ + c`) and a
  centrally ample linearized line `H` (fibre-one line `O(q)`) gives a native potential family.
* `ProjSubvariety.IsLocallyConvexAll.nativePotentialFSFamily`: the native potential family of a
  locally convex function.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules
open scoped Classical NNReal ENNReal Topology

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra Scheme.Modules.monoidalCategory

namespace EnvelopeProperty.ProjSubvariety

open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint CanonicalGeometry
  NativePulledProjectiveLineFrames NativeTestConfiguration NativeTestConfiguration.TestConfiguration
  ProjectiveCentralFiberSectionLifting
  ProjectiveCentralFiberEmbeddingNeighborhoodClosedWholeGeneratorExactFS

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

private local instance nativeStructureIsProperFamily : IsProper X.nativeStructure := by
  let : IsProper (ProjBerk.nativeStructureMap (R := k) (n := M)) :=
    ProjBerk.nativeStructureMap_isProper
  change IsProper (X.nativeInclusion ≫ ProjBerk.nativeStructureMap)
  infer_instance

/-! ### `O(d)^{⊗ b} ⊗ O(q)^{⊗ a} ≅ O(d b + q a)` -/

/-- The native twists multiply: `O_t(d)^{⊗ b} ⊗ O_t(q)^{⊗ a} ≅ O_t(d b + q a)` on `X.NativeScheme`
(pull-backs of the coordinate-hyperplane twists of `ℙᴹ`, `ProjectiveTwistTensorAddition`). -/
def nativeTwistPowerTensorIso (t : Fin (M + 1)) (d q b a : ℕ) :
    bundleTensorPower (X.nativeTwistLineSheaf t d) b ⊗
        bundleTensorPower (X.nativeTwistLineSheaf t q) a ≅
      X.nativeTwistLineSheaf t (d * b + q * a) := by
  letI := Scheme.Modules.pullbackMonoidal X.nativeProjectiveInclusion
  exact (X.nativeLinePowerIso t d b ⊗ᵢ X.nativeLinePowerIso t q a) ≪≫
    Functor.Monoidal.μIso (Scheme.Modules.pullback X.nativeProjectiveInclusion)
      (MvPolynomial.coordinateHyperplaneTwist (R := k) t ((d * b : ℕ) : ℤ))
      (MvPolynomial.coordinateHyperplaneTwist (R := k) t ((q * a : ℕ) : ℤ)) ≪≫
    (Scheme.Modules.pullback X.nativeProjectiveInclusion).mapIso
      (ProjectiveTwistTensorAddition.tensorIso t t t ((d * b : ℕ) : ℤ) ((q * a : ℕ) : ℤ) ≪≫
        eqToIso (congrArg (MvPolynomial.coordinateHyperplaneTwist (R := k) t)
          (by ring)))

/-! ### Boundedness of finite FS functions -/

variable {X} in
/-- A finite Fubini–Study function on the compact space `X^an` is bounded. -/
theorem IsFiniteFS.exists_abs_le {a : ℚ} {ψ : X.an → ℝ} (h : X.IsFiniteFS a ψ) :
    ∃ K : ℝ, ∀ w, |ψ w| ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn h.continuous.continuousOn
  exact ⟨K, fun w => by simpa only [Real.norm_eq_abs] using hK w (Set.mem_univ w)⟩

/-! ### Native potential families from a test configuration -/

/-- **Native potential families from a test configuration.** Let `X` be projectively normal and
`C` a test configuration of `X` with integral total space dominating `𝔸¹`. Let `M` be a
linearized invertible sheaf on `C`, nef on the central fibre, whose fibre-one line is the twist
`O_t(d)` and whose model potential is `r φ + c` on `X^an` (with `d = r a`), and let `H` be a
linearized invertible sheaf, ample on the central fibre, whose fibre-one line is `O_t(q)`. Then `φ`
admits a native potential family for `a`: `p_M = pot_M`, `p_H = pot_H`, and for `b ≥ 1` the exact
FS realization of `b pot_M + pot_H` for `O_t(d)^{⊗ b} ⊗ O_t(q) ≅ O_t(d b + q)`. -/
theorem nativePotentialFSFamily_of_testConfiguration [Infinite k] (hX : X.IsProjNormal)
    (C : TestConfiguration k (Over.mk X.nativeStructure)) [IsIntegral C.total]
    [IsDominant C.projection] (t : Fin (M + 1)) {d q : ℕ} (hd : 0 < d) (hq : 0 < q)
    (Mℓ H : C.total.Modules) (hM : IsInvertible Mℓ) (hH : IsInvertible H)
    (α : (Scheme.Modules.pullback C.lineActionMap).obj Mℓ ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj Mℓ)
    (β : (Scheme.Modules.pullback C.lineActionMap).obj H ≅
      (Scheme.Modules.pullback C.lineProjectionMap).obj H)
    (e : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj Mℓ ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj (X.nativeTwistLineSheaf t d))
    (f : (Scheme.Modules.pullback C.fibreOneInclusion.left).obj H ≅
      (Scheme.Modules.pullback C.fibreOneIso.hom.left).obj (X.nativeTwistLineSheaf t q))
    (hnef :
      letI : IsProjective (Limits.pullback.snd C.projection (zeroMap k)) :=
        C.centralProjection_isProjective
      NativeRealNumericalClasses.lineClass (Limits.pullback.snd C.projection (zeroMap k))
          ((Scheme.Modules.pullback (zeroInclusion C.projection)).obj Mℓ)
          (hM.pullback (zeroInclusion C.projection)) ∈
        NativeRealNumericalClasses.nefCone (Limits.pullback.snd C.projection (zeroMap k)))
    (hHc : SchemeLineAmpleness.IsAmple (Limits.pullback.snd C.projection (zeroMap k))
      ((Scheme.Modules.pullback (zeroInclusion C.projection)).obj H))
    {a : ℚ} {φ : X.an → ℝ} {r : ℕ} (hr : 0 < r) (hda : (d : ℚ) = r * a) (c : ℝ)
    (hpot : ∀ w : X.an, C.gaussNativeModelPotential Mℓ hM (X.nativeTwistLineSheaf t d) α e
        (X.nativeTwistLineSheaf_isInvertible t d) weightedFSRadius weightedFSRadius_properties.1
        weightedFSRadius_properties.2.1 (X.nativeAnalyticHomeomorph w) = r * φ w + c) :
    X.NativePotentialFSFamily a φ := by
  have : IsIntegral (Over.mk X.nativeStructure).left := X.originalNativeScheme_isIntegral
  set pM : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeStructure → ℝ := fun y =>
    C.gaussNativeModelPotential Mℓ hM (X.nativeTwistLineSheaf t d) α e
      (X.nativeTwistLineSheaf_isInvertible t d) weightedFSRadius weightedFSRadius_properties.1
      weightedFSRadius_properties.2.1 y
  set pH : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeStructure → ℝ := fun y =>
    C.gaussNativeModelPotential H hH (X.nativeTwistLineSheaf t q) β f
      (X.nativeTwistLineSheaf_isInvertible t q) weightedFSRadius weightedFSRadius_properties.1
      weightedFSRadius_properties.2.1 y
  -- `pot_H` is bounded: it is an exact finite FS function, hence finite FS on `X^an`
  have hExact : NativeLineFubiniStudy.IsFinFS X.nativeStructure
      (line X.nativeProjectiveInclusion t q) (line_isInvertible X.nativeProjectiveInclusion t q) 1
      (fun y => ((pH y : ℝ) : EReal)) :=
    isFinFS_modelPotential_of_central_ample
      C H hH (X.nativeTwistLineSheaf t q) β f (X.nativeTwistLineSheaf_isInvertible t q) hHc
  obtain ⟨-, hHfin⟩ := X.isFiniteFS_of_nativeIsFinFS hX t q hExact
  obtain ⟨K, hK⟩ := hHfin.exists_abs_le
  refine ⟨r, hr, d, q, hda, c, K, pM, pH, hpot, fun w => ?_, fun b hb => ?_⟩
  · simpa only [EReal.toReal_coe] using hK w
  · have hFS := C.isFinFS_power_tensor_potential_sum_of_central_nef Mℓ H hM hH
      (X.nativeTwistLineSheaf t d) (X.nativeTwistLineSheaf t q) α β e f
      (X.nativeTwistLineSheaf_isInvertible t d) (X.nativeTwistLineSheaf_isInvertible t q)
      hnef hHc 1 b one_pos (X.nativeTwistLineSheaf_tensorPower_isAmple t d hd b hb)
      (X.nativeTwistLineSheaf_tensorPower_isAmple t q hq 1 one_pos)
    refine ⟨t, d * b + q * 1, 1, _,
      ((TensorPowerBaseIdealGrading.tensorPower_isInvertible
        (X.nativeTwistLineSheaf_isInvertible t d) b).monoidalTensor
          (TensorPowerBaseIdealGrading.tensorPower_isInvertible
            (X.nativeTwistLineSheaf_isInvertible t q) 1)),
      ⟨X.nativeTwistPowerTensorIso t d q b 1⟩, by push_cast; ring, ?_⟩
    have hfun : (fun y => (((b : ℝ) * pM y + pH y : ℝ) : EReal)) = fun y =>
        (((b : ℝ) * pM y + ((1 : ℕ) : ℝ) * pH y : ℝ) : EReal) := by
      funext y
      rw [Nat.cast_one, one_mul]
    rw [hfun]
    exact hFS

/-! ### The native potential family of a locally convex function -/

variable {X} in
/-- **Locally convex functions admit native potential families** (the upstream half of FHX
Lemma 5.5). Let `k` be a perfect infinite field (e.g. algebraically closed), `X = V(I) ⊆ ℙᴹ`
projectively normal, `a ∈ ℚ_{>0}`, and `φ : X^an → ℝ` locally `O(a)`-convex in the sense of FHX
Definition 5.3. Then `φ` admits a native potential family for `a`. -/
theorem IsLocallyConvexAll.nativePotentialFSFamily [PerfectField k] [Infinite k]
    (hX : X.IsProjNormal) {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ} (hφ : X.IsLocallyConvexAll a φ) :
    X.NativePotentialFSFamily a φ := by
  obtain ⟨r, d, hr, hd, hda, B, I, J, -, -, hI, hJ, A₁, A₂, -, -, hA₁, hA₂, hfinAll, hW⟩ :=
    NumericalOriginalCentralNef.exists_prescribedClass_originalCentralNef_nativeProductIdeal
      X hX ha hφ
  set hfin : ∀ w : X.an,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
        (X.nativeProductGaussPoint w) ≠ ⊥ :=
    fun w => hfinAll (X.nativeProductGaussPoint w)
  obtain ⟨hweight, hnef⟩ := hW
  have : IsIntegral
      (X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A₁ A₂ hA₁ hA₂ hX).total :=
    X.normalizedSimultaneousIdealBlowup_isIntegral (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin
  have : IsDominant (X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A₁ A₂ hA₁ hA₂
      hX).projection :=
    X.normalizedSimultaneousStructure_isDominant_anyField (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin
  obtain ⟨q, hq, hHc⟩ :=
    X.normalizedSimultaneousNativeTestConfiguration_exists_central_ample_tautologicalTwist
      I J hfin hI hJ A₁ A₂ hA₁ hA₂ hX
  refine X.nativePotentialFSFamily_of_testConfiguration hX
    (X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A₁ A₂ hA₁ hA₂ hX) 0 hd hq
    (X.normalizedSimultaneousTwistedRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J)
      hfin 0 d)
    (X.normalizedSimultaneousTautologicalTwistLine I J hfin 0 q)
    (X.normalizedSimultaneousTwistedRatioLine_isInvertible (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin 0 d)
    (X.normalizedSimultaneousTautologicalTwistLine_isInvertible I J hfin 0 q)
    (X.normalizedSimultaneousNativeTestConfigurationLineComparison I J hI hJ hfin A₁ A₂ hA₁ hA₂
      hX 0 d)
    (X.normalizedSimultaneousNativeTestConfigurationTautologicalLineComparison I J hfin hI hJ
      A₁ A₂ hA₁ hA₂ hX 0 q)
    (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso I J hI hJ hfin A₁ A₂ hA₁ hA₂
      hX 0 d)
    (X.normalizedSimultaneousNativeTestConfigurationTautologicalFibreOneLineIso I J hfin hI hJ
      A₁ A₂ hA₁ hA₂ hX 0 q)
    (hnef 0) hHc hr hda (-(B : ℝ)) fun w => ?_
  rw [X.normalizedSimultaneousNativeModelPotential_eq_convex I J hI hJ hfin A₁ A₂ hA₁ hA₂ hX 0 d
    (fun y => (hfinAll (X.normalizedSimultaneousProductPointAt (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin y)).1) hweight w]
  ring

end EnvelopeProperty.ProjSubvariety
