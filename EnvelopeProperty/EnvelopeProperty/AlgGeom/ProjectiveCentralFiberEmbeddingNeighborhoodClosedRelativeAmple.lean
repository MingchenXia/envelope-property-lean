import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeEmbedding
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralSerrePowers
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateEmbedding
import EnvelopeProperty.Projective.TestConfigurationSectionTransport

/-! # Actual nearby ampleness from the same original central ample line -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeAmple
open CanonicalGeometry ProjectiveCentralFiberSectionLifting
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralSerrePowers
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateEmbedding
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeEmbedding
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual original central ampleness internally supplies the SAME positive
power's central embedding and H1 vanishing, hence original nearby ampleness.
No vanishing, embedding/matching or nearby positivity certificate is input. -/
theorem exists_ample_near_zero {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of (Polynomial k))) [IsDominant p]
    (hp : IsProjectiveFactorization p) (L : Y.Modules) (hL : IsInvertible L)
    (hCentral : SchemeLineAmpleness.IsAmple (pullback.snd p (zeroMap k))
      ((Scheme.Modules.pullback (zeroInclusion p)).obj L)) :
    ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
      let B : (Spec (.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
      let W := p ⁻¹ᵁ B
      SchemeLineAmpleness.IsAmple (R := Γ(B.toScheme, ⊤))
        ((p ∣_ B) ≫ B.toScheme.toSpecΓ) ((Scheme.Modules.pullback W.ι).obj L) := by
  let M := (Scheme.Modules.pullback (zeroInclusion p)).obj L
  obtain ⟨N, hN⟩ := exists_sheafH1_bound_of_ample (pullback.snd p (zeroMap k)) M hCentral
  obtain ⟨_hM, r, hr, n, i₀, hi₀, hp₀, ⟨E₀⟩⟩ := hCentral
  let s := r * (N + 1)
  have hs : 0 < s := Nat.mul_pos hr (Nat.succ_pos N)
  have hNs : N ≤ s := (Nat.le_succ N).trans (Nat.le_mul_of_pos_left _ hr)
  obtain ⟨n', ψ, hψ, hψp, ⟨Eψ⟩⟩ :=
    mixedTwist_isVeryAmple (R := k) (m := n) (0 : Fin (n + 1)) N
  let i := i₀ ≫ ψ
  have hi : IsClosedImmersion i := @IsClosedImmersion.comp _ _ _ i₀ ψ hi₀ hψ
  have hpi : i ≫ DeJongAlterations.projectiveSpaceStructure k n' =
      pullback.snd p (zeroMap k) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => i₀ ≫ f) hψp).trans hp₀)
  let θ := TestConfigurationSectionTransport.tensorPowerPullbackIso (zeroInclusion p) L s
  let E : (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := k) (0 : Fin (n' + 1)) 1) ≅
      (Scheme.Modules.pullback (zeroInclusion p)).obj (bundleTensorPower L s) :=
    (frameFactorIso i₀ ψ i rfl
      (coordinateHyperplaneTwist (R := k) (0 : Fin (n' + 1)) 1)).symm ≪≫
      (Scheme.Modules.pullback i₀).mapIso Eψ ≪≫
      (OriginalAmpleSerreVanishing.powerMulPullbackTwistIso i₀ M r
        (0 : Fin (n + 1)) E₀.symm (N + 1)).symm ≪≫ θ.symm
  have hH1 : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj (bundleTensorPower L s)).sheaf 1) := by
    let eH := (CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology (zeroFiber p)) 1).mapIso
        ((Scheme.Modules.toSheaf (zeroFiber p)).mapIso θ)
    exact AddCommGrpCat.subsingleton_of_isZero
      (CategoryTheory.Limits.IsZero.of_iso
        (@AddCommGrpCat.isZero_of_subsingleton _ (hN s hNs)) eH)
  have hLs := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL s
  let : IsClosedImmersion i := hi
  obtain ⟨g, hg, hVery⟩ := exists_veryAmple_near_zero p hp (bundleTensorPower L s)
    hLs hH1 i hpi (0 : Fin (n' + 1)) E
  refine ⟨g, hg, ?_⟩
  let B : (Spec (.of (Polynomial k))).Opens := PrimeSpectrum.basicOpen g
  let W := p ⁻¹ᵁ B
  change SchemeLineAmpleness.IsAmple (R := Γ(B.toScheme, ⊤))
    ((p ∣_ B) ≫ B.toScheme.toSpecΓ) ((Scheme.Modules.pullback W.ι).obj L)
  refine ⟨hL.pullback W.ι, s, hs, ?_⟩
  obtain ⟨a, f, hf, hfp, ⟨Ef⟩⟩ := hVery
  exact ⟨a, f, hf, hfp,
    ⟨Ef ≪≫ TestConfigurationSectionTransport.tensorPowerPullbackIso W.ι L s⟩⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRelativeAmple
