import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNativeSquareExt
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceCandidate
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedNormalizationMapTrace
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceMixedExtendedOriginalCoefficientValue

/-! # Normalization of the mixed canonical candidate

Let `A` be a `k`-algebra (`k` a field of characteristic zero) with étale coordinates
`x: Fin n → A`, `B = mixedRing x N I σ u` the mixed Kummer algebra
`A[t]/(tᵢ^{Nᵢ} - dᵢ)` with positive tame degrees, `φ: A → B`, and write `Ω_R = Γ(Ω^n_{R/k})`.
The mixed canonical candidate `τ = mixedCanonicalCandidate: Ω_B ⟶ Ω_A` (an `A`-linear map) is
built through the étale unit cover `S = UnitCover N u` (adjoining `Nᵢ`-th roots of the units):
with `C = S ⊗_A B` and the purification `C ≃ P` onto the pure Kummer algebra over `S`,
```
τ(v) = (ε ⊗ id) (E (1 ⊗ v)), E: S ⊗_A Ω_B ≅ Ω_C ≅ Ω_P ⟶ Ω_S ≅ S ⊗_A Ω_A,
```
where `Ω_P ⟶ Ω_S` is the pure canonical counit and `ε = deg⁻¹ · Tr_{S/A}`.

The main result `mixedCanonicalCandidate_native` is the normalization
```
τ(b · dφ(w)) = Tr_{B/A}(b) · w (b ∈ B, w ∈ Ω_A),
```
i.e. `τ` is the trace of top forms of the finite flat cover `Spec B → Spec A`
(Esnault–Viehweg, *Lectures on vanishing theorems*, §3: Euler's lemma for Kummer covers).

## Proof

`E(1 ⊗ b·dφ(w)) = E((1 ⊗ b) · (1 ⊗ dφ(w)))`. The comparison `S ⊗_A Ω_B ≅ Ω_C` is `C`-linear for
`1 ⊗ b ∈ C` (`mixedExtendedSectionsIso_originalTensorCoefficient`) and the purification
`Ω_C ≅ Ω_P` is semilinear along `e: C ≃ P`, being a `C`-linear iso `Ω_C ≅ e^* Ω_P` followed by
scalar restrictions (`outerComparison_smul`). By the
commutativity of the native square (`originalMixedNativeSquareLeft_eq_rightAligned`,
`NadelGlobalCanonicalTraceMixedNativeSquareExt`) the image of `1 ⊗ dφ(w)` in `Ω_P` is
`dψ(1 ⊗ w)`, the pure differential of `1 ⊗ w ∈ Ω_S`. The pure counit sends `c · dψ(w')` to
`Tr_{P/S}(c) · w'` (`pureCanonicalSectionsCounit_native`), so
`E(1 ⊗ b·dφ(w)) = Tr_{P/S}(e(1 ⊗ b)) · (1 ⊗ w)`. Finally
`Tr_{P/S}(e(1 ⊗ b)) = Tr_{C/S}(1 ⊗ b) = Tr_{B/A}(b)` by base change of the trace
(`mixedPurificationMap_trace_tmul`) and `ε` fixes the elements of `A`
(`unitCoverCoefficientRetraction_algebraMap`).

## Proof design

The computation is the abstract lemma `mixedCanonicalCandidate_value_finish`, over arbitrary
rings and modules. The concrete instantiation reads every concrete map off the definitions and
the accepted statements by unification; the identifications of the comparisons in the accepted
statements with those inside the candidate are single definitional unfoldings, checked last.
Two choices keep the kernel check small (peak below 0.6 GB):
* the semilinearity of the purification comparison is derived from its shape (`hH`, read off its
  definition) rather than from the accepted statement, whose module objects are presented
  differently from those of the candidate;
* the evaluation point `b · dφ(w)` and the scalar `Tr_{B/A}(b)` enter as free variables `v`, `t`
  with deferred identities `hv`, `ht`, so that the conclusion is literally the goal. Comparing two
  presentations of the point under the candidate made the kernel evaluate the candidate.

This normalization identity identifies the mixed canonical candidate with the trace
used in relative Nadel vanishing.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace

open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelCanonicalMixed NadelCanonicalMixed.Split
open scoped TensorProduct ChangeOfRings

/-! ### The abstract computation -/

section Abstract

variable {R S B C P : Type u} [CommRing R] [CommRing S] [CommRing B] [CommRing C] [CommRing P]

/-- The composite `M ≅ ρ^* Q₀`, `ρ^* = (ρ ∘ γ)^*`-comparison, `T : Q₀ ≅ N₀` (the shape of the
purification comparison) is semilinear along `ρ`. -/
theorem outerComparison_smul (γ : S →+* C) (β : S →+* P) (ρ : C →+* P)
    {Y : ModuleCat.{u} C} {Q₀ N₀ : ModuleCat.{u} P}
    (E : Y ≅ (ModuleCat.restrictScalars ρ).obj Q₀) (T : Q₀ ≅ N₀) (hs : β = ρ.comp γ)
    (c : C) (z : Y) :
    ((ModuleCat.restrictScalars γ).mapIso E ≪≫
        (ModuleCat.restrictScalarsComp'App γ ρ β hs Q₀).symm ≪≫
          (ModuleCat.restrictScalars β).mapIso T).hom (c • z) =
      ρ c • (show N₀ from ((ModuleCat.restrictScalars γ).mapIso E ≪≫
        (ModuleCat.restrictScalarsComp'App γ ρ β hs Q₀).symm ≪≫
          (ModuleCat.restrictScalars β).mapIso T).hom z) := by
  change T.hom (E.hom (c • z)) = ρ c • T.hom (E.hom z)
  have h := E.hom.hom.map_smul c z
  have ht := congrArg T.hom.hom.toFun h
  exact ht.trans (T.hom.hom.map_smul (ρ c) (E.hom z))

/-- Abstract computation of a candidate `τ = unit ≫ E ≫ (ε ⊗ id)` with
`E = G ≫ H ≫ K ≫ U⁻¹` on `v = b · F₀(w)`, from the coefficient law of `G`, the shape of `H`
(semilinear along `ρ`), the square `F₀ ≫ G ≫ H = U ≫ D`, the value of `K` on `c · D(w')`, the
value of the retraction on pure tensors and the base change of the trace. `G'` and `e'` are the
presentations of `G` and `ρ` in the accepted value statements. -/
theorem mixedCanonicalCandidate_value_finish
    (α : R →+* S) (φB : R →+* B) (γ : S →+* C) (β : S →+* P) (ρ : C →+* P)
    {MB : ModuleCat.{u} B} {Q : ModuleCat.{u} R} {Y : ModuleCat.{u} C} {Q₀ N₀ : ModuleCat.{u} P}
    {W : ModuleCat.{u} S}
    (τ : (ModuleCat.restrictScalars φB).obj MB ⟶ Q)
    (Eext : (ModuleCat.extendScalars α).obj ((ModuleCat.restrictScalars φB).obj MB) ⟶
      (ModuleCat.extendScalars α).obj Q)
    (ρQ : (ModuleCat.restrictScalars α).obj ((ModuleCat.extendScalars α).obj Q) ⟶ Q)
    (G G' : (ModuleCat.extendScalars α).obj ((ModuleCat.restrictScalars φB).obj MB) ⟶
      (ModuleCat.restrictScalars γ).obj Y)
    (H : (ModuleCat.restrictScalars γ).obj Y ⟶ (ModuleCat.restrictScalars β).obj N₀)
    (EY : Y ≅ (ModuleCat.restrictScalars ρ).obj Q₀) (T : Q₀ ≅ N₀) (hs : β = ρ.comp γ)
    (K : (ModuleCat.restrictScalars β).obj N₀ ⟶ W) (U : (ModuleCat.extendScalars α).obj Q ≅ W)
    (F₀ : Q ⟶ (ModuleCat.restrictScalars φB).obj MB) (D : W ⟶ (ModuleCat.restrictScalars β).obj N₀)
    (hτ : τ = (ModuleCat.extendRestrictScalarsAdj α).unit.app _ ≫
      (ModuleCat.restrictScalars α).map Eext ≫ ρQ)
    (hE : Eext = G ≫ H ≫ K ≫ U.inv)
    (hH : H = ((ModuleCat.restrictScalars γ).mapIso EY ≪≫
        (ModuleCat.restrictScalarsComp'App γ ρ β hs Q₀).symm ≪≫
          (ModuleCat.restrictScalars β).mapIso T).hom)
    (hsq : (ModuleCat.extendScalars α).map F₀ ≫ G ≫ H = U.hom ≫ D)
    (tens : S → B → C)
    (hG : ∀ (s : S) (b : B) (y : MB),
      G' (s ⊗ₜ[R, α] (show (ModuleCat.restrictScalars φB).obj MB from b • y)) =
        tens s b • (show Y from G' ((1 : S) ⊗ₜ[R, α]
          (show (ModuleCat.restrictScalars φB).obj MB from y))))
    (trP : P → S)
    (hK : ∀ (c : P) (w' : W), K (c • (show N₀ from D w')) = trP c • w')
    (ε : S → R)
    (hρ : ∀ (s : S) (q : Q),
      ρQ (show (ModuleCat.extendScalars α).obj Q from s ⊗ₜ[R, α] q) = ε s • q)
    (e' : C → P) (trB : B → R)
    (htr : ∀ (s : S) (c : B), trP (e' (tens s c)) = s * α (trB c))
    (hε : ∀ a : R, ε (α a) = a)
    (hGG : G = G') (hee : ∀ c, ρ c = e' c)
    (b : B) (w : Q) (v : (ModuleCat.restrictScalars φB).obj MB)
    (hv : v = b • (show MB from F₀ w)) (t : R) (ht : t = trB b) :
    τ.hom v = t • w := by
  subst hτ hE hGG hv ht
  -- the value of the square on `1 ⊗ w`
  have hsq' := congrArg (fun f => f ((1 : S) ⊗ₜ[R, α] w)) hsq
  simp only [ModuleCat.comp_apply, ModuleCat.ExtendScalars.map_tmul] at hsq'
  have hHs : ∀ (c : C) (z : Y), H (c • z) = ρ c • (show N₀ from H z) := by
    subst hH
    exact outerComparison_smul γ β ρ EY T hs
  change ρQ (U.inv (K (H (G ((1 : S) ⊗ₜ[R, α]
    (show (ModuleCat.restrictScalars φB).obj MB from b • (show MB from F₀ w))))))) = _
  rw [hG, hHs, hsq', hK, hee, htr]
  have hUinv : U.inv (((1 : S) * α (trB b)) • U.hom ((1 : S) ⊗ₜ[R, α] w)) =
      ((1 : S) * α (trB b)) • ((1 : S) ⊗ₜ[R, α] w) := by
    rw [map_smul, Iso.hom_inv_id_apply]
  rw [hUinv, ModuleCat.ExtendScalars.smul_tmul, hρ, one_mul, mul_one, hε]

end Abstract

/-! ### The mixed candidate -/

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

-- The accepted coefficient statements are deep terms; elaborating the assembly against them
-- exceeds the default recursion depth (512). Heartbeats are not raised.
set_option maxRecDepth 4000 in
/-- **Normalization of the mixed canonical candidate** (R-mix-2): the mixed canonical
candidate sends `b · dφ(w)` to `Tr_{B/A}(b) · w` for every `b ∈ B = mixedRing x N I σ u` and every
top form `w` on `Spec A`. -/
theorem mixedCanonicalCandidate_native
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) (b : mixedRing x N I σ u)
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)) :
    (mixedCanonicalCandidate x N I σ u hx hN htame).hom
        (b • (show mixedCanonicalModule (k := k) x N I σ u from
          mixedNativeCanonicalPullback (k := k) x N I σ u hx w)) =
      Algebra.trace A (mixedRing x N I σ u) b • w := by
  have hsq := originalMixedNativeSquareLeft_eq_rightAligned (k := k) x N I σ u hx hN htame
  have hG := mixedExtendedSectionsIso_originalTensorCoefficient (k := k) x N I σ u hx hN htame
  let : Nontrivial (UnitCover N u) := unitCover_nontrivial N u hN
  have hK := pureCanonicalSectionsCounit_native N I σ hN (unitCoordinateMap (k := k) x N u)
    (unitCoordinateMap_etale x N u hx hN htame) (unitCoordinateMap_formallyEtale x N u hx hN htame)
    (fun i => by simpa only [map_natCast] using (htame i).map (algebraMap A (UnitCover N u)))
  have hρ := unitCoverSectionsRetraction_tmul (k := k) N u hN
    ((moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n))
  have htr := mixedPurificationMap_trace_tmul (k := k) x N I σ u hN
  have hε := unitCoverCoefficientRetraction_algebraMap (k := k) N u hN
  refine mixedCanonicalCandidate_value_finish _ _ _ _ _
    (mixedCanonicalCandidate x N I σ u hx hN htame) _ _ _ _ _ _ _ _ _ _ _ _
    rfl rfl rfl hsq _ hG _ hK _ hρ _ _ htr hε ?hGG ?hee b w _ ?hv _ ?ht
  case hGG => exact rfl
  case hee => exact fun _ => rfl
  case hv => exact rfl
  case ht => exact rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
