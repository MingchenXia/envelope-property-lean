import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceDenseEtaleCancellation

/-! # The same cancellation on arbitrary actual etale-open target factorizations

The target map can be any original morphism factoring through an actual
open on which the entire cover is etale. In particular a native affine
chart's original generic base map need not be replaced by another field.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceDenseEtaleCancellation
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.differential_isIso_on_etale_base_open
  unless (← Lean.getEnv).contains name do
    throwError "missing frozen original etale-open differential producer {name}"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls := Lean.OpenDecl.explicit `frozenDifferentialOnEtaleOpen name :: scope.openDecls }

/-- Ordinary actual etale geometry detects maps into ANY pushforward
whose original target map factors through the actual etale open.
The input is the actual geometric open and its actual factorization,
not a caller inverse differential or trace compatibility certificate. -/
theorem differential_target_hom_ext_of_etale_open
    {X Y V W : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (π : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f]
    (j : V ⟶ X) [IsOpenImmersion j] [Etale (pullback.snd π j)]
    (γ : W ⟶ X) (t : W ⟶ V) (ht : t ≫ j = γ)
    (N : W.Modules)
    (a b : (pushforward π).obj (exteriorCotangentSheaf (π ≫ f) n) ⟶
      (pushforward γ).obj N)
    (h : (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫ a =
      (pushforward π).map (exteriorCotangentSheafPullbackMap f π n) ≫ b) : a = b := by
  let q := pullback.snd π j
  let v := pullback.fst π j
  let : IsOpenImmersion v := inferInstance
  let δ := exteriorCotangentSheafPullbackMap f π n
  let : IsIso ((Scheme.Modules.pullback v).map δ) :=
    frozenDifferentialOnEtaleOpen f π n j
  let : IsIso ((restrictFunctor v).map δ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback v) δ).mpr inferInstance
  let E := restrictPushforwardIsoOfIsPullback π q v j
    (IsPullback.of_hasPullback π j).flip
  have hr : IsIso ((restrictFunctor j).map ((pushforward π).map δ)) :=
    (NatIso.isIso_map_iff E δ).mpr
      (inferInstance : IsIso ((pushforward q).map ((restrictFunctor v).map δ)))
  let : IsIso ((Scheme.Modules.pullback j).map ((pushforward π).map δ)) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback j) ((pushforward π).map δ)).mp hr
  let J : (pushforward γ).obj N ≅ (pushforward j).obj ((pushforward t).obj N) :=
    (pushforwardCongr ht).symm.app N ≪≫ (pushforwardComp t j).symm.app N
  apply (cancel_mono J.hom).mp
  apply hom_ext_of_map_epi (pullbackPushforwardAdjunction j) ((pushforward π).map δ)
  simpa only [Category.assoc] using congrArg (fun z => z ≫ J.hom) h

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
