import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationGamma
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureTensorNaturality
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormulaTraceSection
import EnvelopeProperty.AlgGeom.AffinePullbackStalkTensorReadback

/-!
# The pulled-line trace of a finite free affine morphism

Let `A → B` be a homomorphism of commutative rings making `B` a finite free `A`-module, let
`β : Spec B → Spec A` be its spectrum map, and let `M` be an invertible `𝒪_{Spec A}`-module.
The structure-sheaf trace `τ : β_* 𝒪_{Spec B} → 𝒪_{Spec A}` (the algebra trace of `B/A` on
sections) induces, through the projection formula `β_* 𝒪 ⊗ M ≅ β_*(𝒪 ⊗ β^* M)`, the
*pulled-line trace*
`T_M : β_* β^* M ≅ β_*(𝒪 ⊗ β^* M) ≅ β_* 𝒪 ⊗ M → 𝒪 ⊗ M ≅ M`.

This is the trace map of a finite flat cover twisted by a line bundle (Esnault–Viehweg,
*Lectures on vanishing theorems*, §3).  We prove:

* `affinePulledLineTrace_tmul`: on the sections `r • β^* m` (`r ∈ Γ(Spec B, ⊤)`,
  `m ∈ Γ(M, ⊤)`) the trace is `T_M (r • β^* m) = τ(r) • m`;
* `affinePushforwardPullback_hom_ext`: for quasicoherent `M`, a morphism out of `β_* β^* M`
  is determined by its values on the sections `r • β^* m`, because these sections generate
  `Γ(Spec B, β^* M) = B ⊗_A Γ(M)` additively and `β_* β^* M` is quasicoherent.

Together they say that `T_M` is the unique morphism with `T_M (r • β^* m) = τ(r) • m`.
The definition uses the same left-unit constraint and the same projection formula as the
global regular pulled-line trace, so that its restriction to an affine chart is literally this
map.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules Opposite
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRational
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.actualLeftUnit
  unless (← Lean.getEnv).contains name do
    throwError "missing the left-unit constraint of the global pulled-line trace {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls :=
        Lean.OpenDecl.explicit `affineLineOriginalLeftUnit name :: scope.openDecls }

/-! ### Morphisms out of quasicoherent modules on an affine scheme -/

/-- A morphism out of a quasicoherent module on `Spec A` is determined by its top component:
the counit `Γ(P)^~ ⟶ P` of the tilde-sections adjunction is an isomorphism, and morphisms
`Γ(P)^~ ⟶ N` correspond to `A`-linear maps `Γ(P) ⟶ Γ(N)`. -/
theorem affineSpecModules_hom_ext_top {A : CommRingCat.{u}} {P N : (Spec A).Modules}
    [P.IsQuasicoherent] {f g : P ⟶ N} (h : ∀ x : Γ(P, ⊤), f.app ⊤ x = g.app ⊤ x) :
    f = g := by
  have hΓ : (moduleSpecΓFunctor (R := A)).map f = (moduleSpecΓFunctor (R := A)).map g :=
    ModuleCat.hom_ext (LinearMap.ext fun x => h x)
  have hf : Scheme.Modules.fromTildeΓ (R := A) P ≫ f =
      (tilde.functor A).map ((moduleSpecΓFunctor (R := A)).map f) ≫
        Scheme.Modules.fromTildeΓ (R := A) N :=
    ((tilde.adjunction (R := A)).counit.naturality f).symm
  have hg : Scheme.Modules.fromTildeΓ (R := A) P ≫ g =
      (tilde.functor A).map ((moduleSpecΓFunctor (R := A)).map g) ≫
        Scheme.Modules.fromTildeΓ (R := A) N :=
    ((tilde.adjunction (R := A)).counit.naturality g).symm
  have : IsIso (Scheme.Modules.fromTildeΓ (R := A) P) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent P
  refine (cancel_epi (Scheme.Modules.fromTildeΓ (R := A) P)).mp ?_
  rw [hf, hg, hΓ]

/-- Induction principle for top sections of `β^* M` (`β = Spec φ`, `M` quasicoherent): every
such section is a finite sum of sections `r • β^* m`, since `Γ(Spec B, β^* M)` is the scalar
extension `B ⊗_A Γ(M)` and `b ⊗ m ↦ b • β^* m`. -/
theorem affinePullbackTop_induction {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M : (Spec A).Modules) [M.IsQuasicoherent]
    (p : Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤) → Prop) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y))
    (hgen : ∀ (r : Γ(Spec B, ⊤)) (m : Γ(M, ⊤)),
      p ((· • · : Γ(Spec B, ⊤) → Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤) →
          Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤)) r
        (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m)))
    (x : Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤)) : p x := by
  let : Algebra A B := φ.hom.toAlgebra
  have key : ∀ t : B ⊗[A] (moduleSpecΓFunctor (R := A)).obj M,
      p (AffinePullbackStalkTensorReadback.specPullbackTensorEquiv M φ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero]
      exact h0
    | tmul b m =>
      rw [AffinePullbackStalkTensorReadback.specPullbackTensorEquiv_tmul]
      have hb := hgen ((Scheme.ΓSpecIso B).inv b) m
      rw [← affinePullbackUnitTop_eq_unit φ M m] at hb
      exact hb
    | add a b ha hb =>
      rw [map_add]
      exact hadd _ _ ha hb
  exact (AffinePullbackStalkTensorReadback.specPullbackTensorEquiv M φ).apply_symm_apply x ▸
    key ((AffinePullbackStalkTensorReadback.specPullbackTensorEquiv M φ).symm x)

/-- A morphism out of `β_* β^* M` (`β = Spec φ`, `M` quasicoherent) is determined by its
values on the sections `r • β^* m` with `r ∈ Γ(Spec B, ⊤)` and `m ∈ Γ(M, ⊤)`. -/
theorem affinePushforwardPullback_hom_ext {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (M N : (Spec A).Modules) [M.IsQuasicoherent]
    {f g : (pushforward (Spec.map φ)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M) ⟶ N}
    (h : ∀ (r : Γ(Spec B, ⊤)) (m : Γ(M, ⊤)),
      f.app ⊤ (affinePushforwardRawSection φ ((Scheme.Modules.pullback (Spec.map φ)).obj M)
        ((· • · : Γ(Spec B, ⊤) → Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤) →
            Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤)) r
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m))) =
      g.app ⊤ (affinePushforwardRawSection φ ((Scheme.Modules.pullback (Spec.map φ)).obj M)
        ((· • · : Γ(Spec B, ⊤) → Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤) →
            Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤)) r
          (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m)))) :
    f = g := by
  have : ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent :=
    isQuasicoherent_pullback_of_isAffine (Spec.map φ) M
  have : ((pushforward (Spec.map φ)).obj
      ((Scheme.Modules.pullback (Spec.map φ)).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom (Spec.map φ)
  refine affineSpecModules_hom_ext_top fun x => ?_
  refine affinePullbackTop_induction φ M
    (fun y => f.app ⊤ (affinePushforwardRawSection φ _ y) =
      g.app ⊤ (affinePushforwardRawSection φ _ y)) ?_ ?_ h x
  · exact (map_zero (ConcreteCategory.hom (f.app ⊤))).trans
      (map_zero (ConcreteCategory.hom (g.app ⊤))).symm
  · intro y z hy hz
    exact ((map_add (ConcreteCategory.hom (f.app ⊤)) y z).trans (congrArg₂ (· + ·) hy hz)).trans
      (map_add (ConcreteCategory.hom (g.app ⊤)) y z).symm

/-! ### The pulled-line trace -/

/-- The pulled-line trace `β_* β^* M ⟶ M` of the finite free affine morphism
`β = Spec (A → B)` and an invertible `𝒪_{Spec A}`-module `M`: the inverse projection formula
followed by the structure-sheaf trace `affineStructureTrace A B`, framed by the left-unit
constraints. -/
def affinePulledLineTrace (A B : CommRingCat.{u}) [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (M : (Spec A).Modules) (hM : IsInvertible M) :
    (pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M) ⟶
      M :=
  (pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
      (affineLineOriginalLeftUnit
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)).inv ≫
    (SchemeLineProjectionFormula.lineProjectionFormulaObj
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) M hM (unitObj (Spec B))).inv ≫
    (tensorRight M).map (NadelGlobalStructureTrace.affineStructureTrace A B) ≫
    (affineLineOriginalLeftUnit M).hom

/-- The pulled-line trace written with the transported left-unit constraint of the
projection-formula API. -/
theorem affinePulledLineTrace_eq_transported (A B : CommRingCat.{u}) [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (M : (Spec A).Modules) (hM : IsInvertible M) :
    affinePulledLineTrace A B M hM =
      (pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
          (SchemeLineProjectionFormulaUnit.transportedLeftUnit
            (ModularCurves.monoidalUnitObjIso (Spec B))
            ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
              M)).inv ≫
        (SchemeLineProjectionFormula.lineProjectionFormulaObj
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) M hM (unitObj (Spec B))).inv ≫
        (tensorRight M).map (NadelGlobalStructureTrace.affineStructureTrace A B) ≫
        (SchemeLineProjectionFormulaUnit.transportedLeftUnit
          (ModularCurves.monoidalUnitObjIso (Spec A)) M).hom :=
  rfl

/-- The pulled-line trace sends `r • β^* m` to `τ(r) • m`, where `τ` is the structure-sheaf
trace of `B/A`. -/
theorem affinePulledLineTrace_tmul (A B : CommRingCat.{u}) [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (M : (Spec A).Modules) (hM : IsInvertible M)
    (r : Γ(Spec B, ⊤)) (m : Γ(M, ⊤)) :
    (affinePulledLineTrace A B M hM).app ⊤
        (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap A B))
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)
          ((· • · : Γ(Spec B, ⊤) →
              Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
                M, ⊤) →
              Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
                M, ⊤)) r
            (((pullbackPushforwardAdjunction
              (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.app M).app ⊤ m))) =
      (· • · : Γ(Spec A, ⊤) → Γ(M, ⊤) → Γ(M, ⊤))
        ((NadelGlobalStructureTrace.affineStructureTrace A B).app ⊤ r) m := by
  rw [affinePulledLineTrace_eq_transported]
  exact SchemeLineProjectionFormulaUnit.lineProjectionFormulaObj_unitTrace_app_smul_unit
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) M hM
    (NadelGlobalStructureTrace.affineStructureTrace A B) ⊤ r m

/-- Coefficient form of `affinePulledLineTrace_tmul`: the coefficient `τ(r)` reads as the
algebra trace `Tr_{B/A}` under the spectrum section isomorphisms. -/
theorem affinePulledLineTrace_coefficient (A B : CommRingCat.{u}) [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : Γ(Spec B, ⊤)) :
    (NadelGlobalStructureTrace.affineStructureTrace A B).app ⊤ r =
      (Scheme.ΓSpecIso A).inv (Algebra.trace A B ((Scheme.ΓSpecIso B).hom r)) :=
  ((Scheme.ΓSpecIso A).hom_inv_id_apply _).symm.trans
    (congrArg (Scheme.ΓSpecIso A).inv (NadelGlobalStructureTrace.affineStructureTrace_top A B r))

/-- The pulled-line trace sends `r • β^* m` to `Tr_{B/A}(r) • m`, the trace read through the
spectrum section isomorphisms. -/
theorem affinePulledLineTrace_trace_value (A B : CommRingCat.{u}) [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (M : (Spec A).Modules) (hM : IsInvertible M)
    (r : Γ(Spec B, ⊤)) (m : Γ(M, ⊤)) :
    (affinePulledLineTrace A B M hM).app ⊤
        (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap A B))
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)
          ((· • · : Γ(Spec B, ⊤) →
              Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
                M, ⊤) →
              Γ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
                M, ⊤)) r
            (((pullbackPushforwardAdjunction
              (Spec.map (CommRingCat.ofHom (algebraMap A B)))).unit.app M).app ⊤ m))) =
      (· • · : Γ(Spec A, ⊤) → Γ(M, ⊤) → Γ(M, ⊤))
        ((Scheme.ΓSpecIso A).inv (Algebra.trace A B ((Scheme.ΓSpecIso B).hom r))) m :=
  (affinePulledLineTrace_tmul A B M hM r m).trans
    (congrArg (fun c : Γ(Spec A, ⊤) => (· • · : Γ(Spec A, ⊤) → Γ(M, ⊤) → Γ(M, ⊤)) c m)
      (affinePulledLineTrace_coefficient A B r))

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
