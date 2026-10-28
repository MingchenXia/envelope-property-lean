import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationNativeApply
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationNativeTransport
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationNativeDifferential

/-! # The original native differential read in its actual raw carrier -/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
universe u

variable {K : Type u} [Field K] (R S : Type u) [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S]


/-- The same original native algebra differential has the raw transported
adjoint-differential value. -/
theorem affineAlgebraCanonicalPullbackMap_toRaw_onCarriers
    (φ : R →ₐ[K] S) (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K (CommRingCat.of R))]
    (w : (moduleSpecΓFunctor (R := (CommRingCat.of R))).obj
      (exteriorCotangentSheaf (affineStructuralMap K (CommRingCat.of R)) n)) :
    ModuleSpecGammaCarrier.toRaw (CommRingCat.of S) (exteriorCotangentSheaf (affineStructuralMap K (CommRingCat.of S)) n)
      (restrictedNativeSection φ.toRingHom
        ((moduleSpecΓFunctor (R := (CommRingCat.of S))).obj
          (exteriorCotangentSheaf (affineStructuralMap K (CommRingCat.of S)) n))
        ((affineAlgebraCanonicalPullbackMap (CommRingCat.of R) (CommRingCat.of S) φ n).hom.toFun w)) =
    affineRawModuleMap (eqToHom (congrArg (fun g => exteriorCotangentSheaf g n)
      (affineAlgebraMap_structuralSquare K (CommRingCat.of R) (CommRingCat.of S) φ)))
        (affinePushforwardRawRead (A := (CommRingCat.of R)) (B := (CommRingCat.of S)) (CommRingCat.ofHom φ.toRingHom)
          (exteriorCotangentSheaf
            (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K (CommRingCat.of R)) n)
          (affineRawModuleMap (exteriorCotangentSheafMorphism (affineStructuralMap K (CommRingCat.of R))
            (Spec.map (CommRingCat.ofHom φ.toRingHom)) n)
              (ModuleSpecGammaCarrier.toRaw (CommRingCat.of R)
                (exteriorCotangentSheaf (affineStructuralMap K (CommRingCat.of R)) n) w))) := by
  let f := affineStructuralMap K (CommRingCat.of R)
  have horiginal := restrictedModuleSpecGammaToRaw_original
    (A := CommRingCat.of R) (B := CommRingCat.of S) (CommRingCat.ofHom φ.toRingHom)
    (exteriorCotangentSheaf (affineStructuralMap K (CommRingCat.of S)) n)
    ((affineAlgebraCanonicalPullbackMap (CommRingCat.of R) (CommRingCat.of S) φ n).hom.toFun w)
  have hread := affineAlgebraCanonicalPullbackMap_raw_apply (CommRingCat.of R) (CommRingCat.of S) φ n w
  have htransport := affineCanonicalGammaTransport_restricted_toRaw (A := (CommRingCat.of R)) (B := (CommRingCat.of S))
    (CommRingCat.ofHom φ.toRingHom) (affineAlgebraMap_structuralSquare K (CommRingCat.of R) (CommRingCat.of S) φ) n
      ((nativeCanonicalPullbackMap f (CommRingCat.ofHom φ.toRingHom) n).hom.toFun w)
  have hnative := nativeCanonicalPullbackMap_restricted_toRaw (A := (CommRingCat.of R)) (B := (CommRingCat.of S)) f
    (CommRingCat.ofHom φ.toRingHom) n w
  run_tac Lean.Elab.Tactic.withMainContext do
    let findLocal (s : String) : Lean.MetaM Lean.Expr := do
      let ctx ← Lean.getLCtx
      for d in ctx do
        if d.userName.eraseMacroScopes == Lean.Name.mkSimple s then
          return Lean.mkFVar d.fvarId
      throwError "missing original raw equality {s}"
    let eqData (p : Lean.Expr) : Lean.MetaM (Lean.Expr × Array Lean.Expr) := do
      let t ← Lean.Meta.whnf (← Lean.Meta.inferType p)
      unless t.isAppOfArity ``Eq 3 do
        throwError "expected original raw equality"
      return (t, t.getAppArgs)
    let transProof (p q : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let (t, a) ← eqData p
      let (_, b) ← eqData q
      let .const _ levels := t.getAppFn | throwError "missing equality universes"
      return Lean.mkAppN (Lean.mkConst ``Eq.trans levels)
        #[a[0]!, a[1]!, a[2]!, b[2]!, p, q]
    let hb ← findLocal "horiginal"
    let hr ← findLocal "hread"
    let ht ← findLocal "htransport"
    let hn ← findLocal "hnative"
    let (tt, ta) ← eqData ht
    let (nt, na) ← eqData hn
    let .const _ [targetLevel] := tt.getAppFn | throwError "missing target universe"
    let .const _ [sourceLevel] := nt.getAppFn | throwError "missing source universe"
    let .app targetFn _ := ta[2]!.consumeMData |
      throwError "missing actual transport value function"
    let lifted := Lean.mkAppN (Lean.mkConst ``congrArg [sourceLevel, targetLevel])
      #[na[0]!, ta[0]!, na[1]!, na[2]!, targetFn, hn]
    let proof ← transProof hb (← transProof hr (← transProof ht lifted))
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []


end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
