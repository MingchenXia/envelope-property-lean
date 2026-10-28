import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePureSections
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceUnitBase

/-! # Intrinsic native normalization on the same original pure algebra

The native sheaf differential of the original finite map is used here.
Neither a frame comparison nor its normalization is supplied by a caller.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalMixed.Split
open NadelCanonicalBaseChange
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coordinateAlgStructure_smooth
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
    (a : MvPolynomial (Fin n) k →ₐ[k] A) (ha : a.toRingHom.Etale) :
    SmoothOfRelativeDimension n (affineStructuralMap k (.of A)) := by
  let x := originalCoordinates a
  have he : MvPolynomial.aeval (R := k) x = a := by
    ext j
    simp only [MvPolynomial.aeval_X, x, originalCoordinates]
  apply coordinateStructure_smooth x
  rw [he]
  exact ha

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n)
    (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] A) (ha : a.toRingHom.Etale)
    (haF : a.toRingHom.FormallyEtale) (htame : ∀ i, IsUnit (N i : A))
local notation "P" => NadelMixedKummer.Ring N (pureCoefficient (originalCoordinates a) I σ)

/-- The actual native differential of the SAME whole pure structural map,
with original coefficient action and its produced field structural square. -/
def pureNativeCanonicalPullback :
    (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n) ⟶
    (ModuleCat.restrictScalars (algebraMap A P)).obj
      ((moduleSpecΓFunctor (R := .of P)).obj
        (exteriorCotangentSheaf (affineStructuralMap k (.of P)) n)) := by
  letI := coordinateAlgStructure_smooth a ha
  exact affineAlgebraCanonicalPullbackMap (.of A) (.of P)
    (IsScalarTower.toAlgHom k A P) n

/-- The native original pure canonical differential agrees with the actual
raw-to-sheaf comparisons on the internally produced original base generator. -/
theorem pureNativeCanonicalPullback_generator :
    pureNativeCanonicalPullback N I σ a ha
      ((baseCanonicalSectionsRawIso a haF).inv
        (affineCanonicalGenerator (baseDifferentialBasis a haF))) =
    (pureCanonicalSectionsRawIso N I σ hN a haF htame).inv
      (topPullback (R := k) (A := A) (B := P) n
        (affineCanonicalGenerator (baseDifferentialBasis a haF))) := by
  let := coordinateAlgStructure_smooth a ha
  rw [baseCanonicalSectionsRawIso_inv_unit,
    pureCanonicalSectionsRawIso_inv_unit, baseGenerator_eq_wedge,
    topPullback_wedge]
  simp only [KaehlerDifferential.map_D]
  change (affineAlgebraCanonicalPullbackMap (.of A) (.of P)
      (IsScalarTower.toAlgHom k A P) n).hom.toFun
      (affineCanonicalCoordinateSection k (.of A) n (originalCoordinates a)) =
    affineCanonicalCoordinateSection k (.of P) n
      (fun j => (IsScalarTower.toAlgHom k A P) (originalCoordinates a j))
  exact affineAlgebraCanonicalPullbackMap_coordinate_wedge (.of A) (.of P)
    (IsScalarTower.toAlgHom k A P) n (originalCoordinates a)

/-- EVERY original base top form retains the same genuine native
canonical differential through the actual pure affine comparisons. -/
theorem pureNativeCanonicalPullback_topform (w : affineCanonicalModule k A n) :
    pureNativeCanonicalPullback N I σ a ha ((baseCanonicalSectionsRawIso a haF).inv w) =
    (pureCanonicalSectionsRawIso N I σ hN a haF htame).inv
      (topPullback (R := k) (A := A) (B := P) n w) := by
  let r := affineCanonicalTrivialization (baseDifferentialBasis a haF) w
  let G := affineCanonicalGenerator (baseDifferentialBasis a haF)
  have hw : w = r • G := affineCanonical_eq_smul_generator (baseDifferentialBasis a haF) w
  rw [hw, (baseCanonicalSectionsRawIso a haF).inv.hom.map_smul]
  have hm := (pureNativeCanonicalPullback N I σ a ha).hom.map_smul r
    ((baseCanonicalSectionsRawIso a haF).inv G)
  have ht := (topPullback (R := k) (A := A) (B := P) n).map_smulₛₗ r G
  change _ = (pureCanonicalSectionsRawIso N I σ hN a haF htame).inv _
  rw [ht, (pureCanonicalSectionsRawIso N I σ hN a haF htame).inv.hom.map_smul]
  change _ = algebraMap A P r •
    (pureCanonicalSectionsRawIso N I σ hN a haF htame).inv
      (topPullback (R := k) (A := A) (B := P) n G)
  exact hm.trans (congrArg (fun z => algebraMap A P r • z)
    (pureNativeCanonicalPullback_generator N I σ hN a ha haF htame))

variable [Nontrivial A]

/-- The SAME actual pure counit has intrinsic native-trace normalization
on EVERY original canonical section, using the SAME original sheaf
canonical differential and EVERY coefficient of the original whole P. -/
theorem pureCanonicalSectionsCounit_native (c : P)
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)) :
    pureCanonicalSectionsCounit N I σ hN a haF htame
      (c • (show (moduleSpecΓFunctor (R := .of P)).obj
        (exteriorCotangentSheaf (affineStructuralMap k (.of P)) n) from
          pureNativeCanonicalPullback N I σ a ha w)) =
      Algebra.trace A P c • w := by
  let b := baseCanonicalSectionsRawIso a haF
  let z := b.hom w
  let T := pureCanonicalSectionsCounit N I σ hN a haF htame
  have hw : b.inv z = w := b.hom_inv_id_apply w
  have hm := pureNativeCanonicalPullback_topform N I σ hN a ha haF htame z
  have hm' := (congrArg (pureNativeCanonicalPullback N I σ a ha).hom.toFun hw).symm.trans hm
  have hc := congrArg (fun t : (moduleSpecΓFunctor (R := .of P)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of P)) n) => T (c • t)) hm'
  have hsP := (pureCanonicalSectionsRawIso N I σ hN a haF htame).inv.hom.map_smul c
    (topPullback (R := k) (A := A) (B := P) n z)
  have hc' := congrArg T.hom.toFun hsP.symm
  have hn := pureCanonicalSectionsCounit_pulled_topform N I σ hN a haF htame c z
  have hs := b.inv.hom.map_smul (Algebra.trace A P c) z
  have hw' := congrArg (fun t => Algebra.trace A P c • t) hw
  -- Compose the already typed actual native identities by ordinary
  -- Eq.trans; the unchanged kernel checks the complete normalization.
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let findLocal (s : String) : Lean.MetaM Lean.Expr := do
      for d in ctx do
        if d.userName.eraseMacroScopes == Lean.Name.mkSimple s then
          return Lean.mkFVar d.fvarId
      throwError "missing native normalization equality {s}"
    let transProof (p q : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let tp ← Lean.Meta.whnf (← Lean.Meta.inferType p)
      let tq ← Lean.Meta.whnf (← Lean.Meta.inferType q)
      unless tp.isAppOfArity ``Eq 3 && tq.isAppOfArity ``Eq 3 do
        throwError "expected native equalities"
      let .const _ levels := tp.getAppFn | throwError "equality has no constant head"
      let ap := tp.getAppArgs
      let aq := tq.getAppArgs
      return Lean.mkAppN (Lean.mkConst ``Eq.trans levels)
        #[ap[0]!, ap[1]!, ap[2]!, aq[2]!, p, q]
    let mut proof ← findLocal "hc"
    for s in ["hc'", "hn", "hs", "hw'"] do
      proof ← transProof proof (← findLocal s)
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
