import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationCore
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationSectionPresentation
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationNativeValue
import EnvelopeProperty.AlgGeom.Canonical.ExteriorPullbackSections

/-!
# The affine canonical differential and the normalization criterion for line traces

Let `k` be a field, `A → B` a homomorphism of `k`-algebras, `β : Spec B → Spec A` its spectrum
map and `f_A, f_B` the structural morphisms to `Spec k`.  The *affine canonical differential*
`dβ : β^* Ω^n_{f_A} ⟶ Ω^n_{f_B}` is the exterior pullback map
`β^* Ω^n_{f_A} ⟶ Ω^n_{f_A ∘ β}` followed by the identification `f_A ∘ β = f_B`.

* `affineAlgebraCanonicalDifferential_unitTop`: on the pulled-back section `β^* w`, `dβ` is
  the native algebra-map pullback of forms `w ↦ φ^* w` (`affineAlgebraCanonicalPullbackMap`).
* `affinePushforward_comp_eq_of_values` (abstract criterion): for arbitrary `D : β^* M ⟶ P`,
  `T : β_* P ⟶ M` and `S : β_* β^* M ⟶ M` with `M` quasicoherent, `β_* D ≫ T = S` as soon as
  `D (β^* w) = Φ w`, `T (b • Φ w) = t(b) • w` and `S (r • β^* m) = t(r) • m`.
* `affineAlgebraCanonicalDifferential_comp_eq_affinePulledLineTrace` (normalization
  criterion): when `B` is finite free over `A`, a morphism `T : β_* Ω^n_{f_B} ⟶ Ω^n_{f_A}`
  satisfies `β_*(dβ) ≫ T = T_{Ω^n}` (the pulled-line trace of `Ω^n_{f_A}`) as soon as
  `T (b • φ^* w) = Tr_{B/A}(b) • w` for all `b ∈ B` and all forms `w` over `A`.

The criterion is the affine form of the characterization of the trace of differential forms
along a finite flat cover by its normalization `τ(b · π^* w) = Tr(b) · w`
(Esnault–Viehweg, *Lectures on vanishing theorems*, §3).  Its proof only uses that morphisms out
of `β_* β^* Ω^n` are determined on the sections `r • β^* m`
(`affinePushforwardPullback_hom_ext`), the value of the pulled-line trace on these sections
(`affinePulledLineTrace_trace_value`), and the value of `dβ` on `β^* m`.

On a concrete chart, instantiate the abstract criterion by
`refine affinePushforward_comp_eq_of_values _ _ _ _ Φ t ?_ hT ?_` so that `D`, `T` and `S` are
read off the goal, and close the side goals with `affineAlgebraCanonicalDifferential_unitTop` and
`affinePulledLineTrace_trace_value` applied to `_` arguments (see
`NadelGlobalCanonicalTraceAffineLineNormalizationMixed`): an `exact` of the concrete criterion
makes the kernel compare differently elaborated structure maps and ring objects.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules Opposite
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine canonical differential `β^* Ω^n_{f_A} ⟶ Ω^n_{f_B}` of a `k`-algebra map
`φ : A → B`: the exterior pullback map followed by the equality `f_A ∘ Spec φ = f_B`. -/
def affineAlgebraCanonicalDifferential (K : Type u) [Field K] (A B : CommRingCat.{u})
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (n : ℕ) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
        (exteriorCotangentSheaf (affineStructuralMap K A) n) ⟶
      exteriorCotangentSheaf (affineStructuralMap K B) n :=
  exteriorCotangentSheafPullbackMap (affineStructuralMap K A)
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) n ≫
    eqToHom (congrArg (fun g => exteriorCotangentSheaf g n)
      (affineAlgebraMap_structuralSquare K A B φ))

/-- Value of a composite `pb ≫ E : β^* M ⟶ Q` on the pulled-back section `β^* m`, when `pb` is
adjoint to `δ : M ⟶ β_* P`: it is `E (δ m)`.  All objects are arbitrary. -/
theorem affineRawModuleMap_comp_pullbackUnit {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {M : (Spec A).Modules} {P Q : (Spec B).Modules}
    (pb : (Scheme.Modules.pullback (Spec.map φ)).obj M ⟶ P) (E : P ⟶ Q)
    (δ : M ⟶ (pushforward (Spec.map φ)).obj P)
    (hδ : (pullbackPushforwardAdjunction (Spec.map φ)).unit.app M ≫
      (pushforward (Spec.map φ)).map pb = δ)
    (m : M.val.obj (op ⊤)) :
    affineRawModuleMap (pb ≫ E) (affineRawPullbackUnit φ M m) =
      affineRawModuleMap E (affinePushforwardRawRead φ P (affineRawModuleMap δ m)) := by
  have hu := affinePullbackUnitTop_eq_unit φ M m
  have hd := congrArg (fun t => t.app ⊤ m) hδ
  change E.app ⊤ (pb.app ⊤ (affinePullbackUnitTop (Spec.map φ) M m)) = E.app ⊤ (δ.app ⊤ m)
  rw [hu]
  exact congrArg (fun t => E.app ⊤ t) hd

/-- On the pulled-back section `β^* w` of a form `w` over `A`, the affine canonical
differential is the native algebra-map pullback `φ^* w` of `w`. -/
theorem affineAlgebraCanonicalDifferential_unitTop {K : Type u} [Field K]
    (A B : CommRingCat.{u}) [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K A)]
    (w : (moduleSpecΓFunctor (R := A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K A) n)) :
    affineRawModuleMap (affineAlgebraCanonicalDifferential K A B φ n)
        (affineRawPullbackUnit (CommRingCat.ofHom φ.toRingHom)
          (exteriorCotangentSheaf (affineStructuralMap K A) n)
          (ModuleSpecGammaCarrier.toRaw A
            (exteriorCotangentSheaf (affineStructuralMap K A) n) w)) =
      affineRawSection (exteriorCotangentSheaf (affineStructuralMap K B) n)
        (ModuleSpecGammaCarrier.toRaw B (exteriorCotangentSheaf (affineStructuralMap K B) n)
          (restrictedNativeSection φ.toRingHom
            ((moduleSpecΓFunctor (R := B)).obj
              (exteriorCotangentSheaf (affineStructuralMap K B) n))
            ((affineAlgebraCanonicalPullbackMap A B φ n).hom.toFun w))) := by
  rw [affineAlgebraCanonicalDifferential,
    affineRawModuleMap_comp_pullbackUnit (hδ := exteriorCotangentSheafPullbackMap_unit _ _ n),
    affineRawSection, affineAlgebraCanonicalPullbackMap_toRaw]

/-- Abstract normalization criterion on `Spec B → Spec A`.  Let `M` be quasicoherent on
`Spec A`, `D : β^* M ⟶ P`, `T : β_* P ⟶ M`, `S : β_* β^* M ⟶ M`, and let `Φ` be a map from
sections of `M` to sections of `P` and `tr : B → A` a map with
`D(β^* w) = Φ w`, `T(b • Φ w) = tr(b) • w` and `S(r • β^* m) = tr(r) • m`.  Then
`β_* D ≫ T = S`. -/
theorem affinePushforward_comp_eq_of_values {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {M : (Spec A).Modules} [M.IsQuasicoherent] {P : (Spec B).Modules}
    (D : (Scheme.Modules.pullback (Spec.map φ)).obj M ⟶ P)
    (T : (pushforward (Spec.map φ)).obj P ⟶ M)
    (S : (pushforward (Spec.map φ)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) ⟶ M)
    (Φ : (moduleSpecΓFunctor (R := A)).obj M → (moduleSpecΓFunctor (R := B)).obj P)
    (tr : B → A)
    (hD : ∀ w, affineRawModuleMap D
        (affineRawPullbackUnit φ M (ModuleSpecGammaCarrier.toRaw A M w)) =
      affineRawSection P (ModuleSpecGammaCarrier.toRaw B P (Φ w)))
    (hT : ∀ (b : B) w, T.app ⊤ (affinePushforwardRawSection φ P
        (ModuleSpecGammaCarrier.toRaw B P (b • Φ w))) =
      ModuleSpecGammaCarrier.toRaw A M (tr b • w))
    (hS : ∀ (r : Γ(Spec B, ⊤)) (m : Γ(M, ⊤)),
      S.app ⊤ (affinePushforwardRawSection φ ((Scheme.Modules.pullback (Spec.map φ)).obj M)
        ((· • · : Γ(Spec B, ⊤) → Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤) →
            Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤)) r
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m))) =
      (· • · : Γ(Spec A, ⊤) → Γ(M, ⊤) → Γ(M, ⊤))
        ((Scheme.ΓSpecIso A).inv (tr ((Scheme.ΓSpecIso B).hom r))) m) :
    (pushforward (Spec.map φ)).map D ≫ T = S := by
  refine affinePushforwardPullback_hom_ext φ M M fun r m => ?_
  refine Eq.trans ?_ (hS r m).symm
  have h1 := Scheme.Modules.Hom.app_smul D r
    (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m)
  have h2 : D.app ⊤ (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m) =
      ModuleSpecGammaCarrier.toRaw B P (Φ (ModuleSpecGammaCarrier.toNative A M m)) :=
    (congrArg (fun t => D.app ⊤ t) (affinePullbackUnitTop_eq_unit φ M m)).symm.trans
      (hD (ModuleSpecGammaCarrier.toNative A M m))
  have h3 : r = (Scheme.ΓSpecIso B).inv ((Scheme.ΓSpecIso B).hom r) :=
    ((Scheme.ΓSpecIso B).hom_inv_id_apply r).symm
  have h4 : (· • · : Γ(Spec B, ⊤) → Γ(P, ⊤) → Γ(P, ⊤)) r
        (ModuleSpecGammaCarrier.toRaw B P (Φ (ModuleSpecGammaCarrier.toNative A M m))) =
      ModuleSpecGammaCarrier.toRaw B P
        ((Scheme.ΓSpecIso B).hom r • Φ (ModuleSpecGammaCarrier.toNative A M m)) :=
    (congrArg (fun c => (· • · : Γ(Spec B, ⊤) → Γ(P, ⊤) → Γ(P, ⊤)) c
      (ModuleSpecGammaCarrier.toRaw B P (Φ (ModuleSpecGammaCarrier.toNative A M m)))) h3).trans
      (moduleSpecGamma_smul_toRaw B P ((Scheme.ΓSpecIso B).hom r)
        (Φ (ModuleSpecGammaCarrier.toNative A M m))).symm
  have h5 : D.app ⊤ ((· • · : Γ(Spec B, ⊤) → Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤) →
        Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤)) r
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m)) =
      ModuleSpecGammaCarrier.toRaw B P
        ((Scheme.ΓSpecIso B).hom r • Φ (ModuleSpecGammaCarrier.toNative A M m)) :=
    h1.trans ((congrArg (fun t => (· • · : Γ(Spec B, ⊤) → Γ(P, ⊤) → Γ(P, ⊤)) r t) h2).trans h4)
  have h6 := hT ((Scheme.ΓSpecIso B).hom r) (ModuleSpecGammaCarrier.toNative A M m)
  have h7 := moduleSpecGamma_smul_toRaw A M (tr ((Scheme.ΓSpecIso B).hom r))
    (ModuleSpecGammaCarrier.toNative A M m)
  exact ((congrArg (fun t => T.app ⊤ (affinePushforwardRawSection φ P t)) h5).trans h6).trans h7

/-- **Normalization criterion for affine line traces.** Let `B` be a finite free `A`-algebra
over the field `K` and `f_A` smooth of relative dimension `n`.  If a morphism
`T : β_* Ω^n_{f_B} ⟶ Ω^n_{f_A}` sends `b • φ^* w` to `Tr_{B/A}(b) • w` for every `b ∈ B` and
every form `w` over `A`, then `T` composed with the pushed affine canonical differential is
the pulled-line trace of `Ω^n_{f_A}`. -/
theorem affineAlgebraCanonicalDifferential_comp_eq_affinePulledLineTrace {K : Type u}
    [Field K] (A B : CommRingCat.{u}) [Algebra K A] [Algebra K B] [Algebra A B]
    [IsScalarTower K A B] [Module.Free A B] [Module.Finite A B] (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K A)]
    (hω : IsInvertible (exteriorCotangentSheaf (affineStructuralMap K A) n))
    (T : (pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (exteriorCotangentSheaf (affineStructuralMap K B) n) ⟶
      exteriorCotangentSheaf (affineStructuralMap K A) n)
    (hT : ∀ (b : B) (w : (moduleSpecΓFunctor (R := A)).obj
        (exteriorCotangentSheaf (affineStructuralMap K A) n)),
      T.app ⊤ (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap A B))
          (exteriorCotangentSheaf (affineStructuralMap K B) n)
          (ModuleSpecGammaCarrier.toRaw B (exteriorCotangentSheaf (affineStructuralMap K B) n)
            (b • restrictedNativeSection (IsScalarTower.toAlgHom K A B).toRingHom
              ((moduleSpecΓFunctor (R := B)).obj
                (exteriorCotangentSheaf (affineStructuralMap K B) n))
              ((affineAlgebraCanonicalPullbackMap A B (IsScalarTower.toAlgHom K A B) n).hom.toFun
                w)))) =
        ModuleSpecGammaCarrier.toRaw A (exteriorCotangentSheaf (affineStructuralMap K A) n)
          (Algebra.trace A B b • w)) :
    (pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        (affineAlgebraCanonicalDifferential K A B (IsScalarTower.toAlgHom K A B) n) ≫ T =
      affinePulledLineTrace A B (exteriorCotangentSheaf (affineStructuralMap K A) n) hω := by
  have : (exteriorCotangentSheaf (affineStructuralMap K A) n).IsQuasicoherent :=
    hω.isQuasicoherent
  exact affinePushforward_comp_eq_of_values (CommRingCat.ofHom (algebraMap A B))
    (affineAlgebraCanonicalDifferential K A B (IsScalarTower.toAlgHom K A B) n) T
    (affinePulledLineTrace A B (exteriorCotangentSheaf (affineStructuralMap K A) n) hω)
    (fun w => restrictedNativeSection (IsScalarTower.toAlgHom K A B).toRingHom
      ((moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf (affineStructuralMap K B) n))
      ((affineAlgebraCanonicalPullbackMap A B (IsScalarTower.toAlgHom K A B) n).hom.toFun w))
    (Algebra.trace A B)
    (fun w => affineAlgebraCanonicalDifferential_unitTop A B (IsScalarTower.toAlgHom K A B) n w)
    hT
    (fun r m => affinePulledLineTrace_trace_value A B
      (exteriorCotangentSheaf (affineStructuralMap K A) n) hω r m)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
