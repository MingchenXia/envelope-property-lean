import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceDifferential
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRawUnits
import EnvelopeProperty.AlgGeom.Canonical.AffineCanonicalSheafImage

/-! # Original affine-coordinate wedges under the native canonical map

The arbitrary original algebra map is used on coefficients, ordinary
universal differentials, and the actual sheaf canonical morphism.
These readbacks will discharge normalization of the actual mixed counit.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem nativeExteriorTransportDifferentialWedge
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f₁ f₂ : X ⟶ Spec (.of K)} (h : f₁ = f₂) (n : ℕ)
    (z : Fin n → Γ(X, ⊤)) :
    (eqToHom (congrArg (fun f => exteriorCotangentSheaf f n) h)).val.app (op ⊤)
      ((exteriorSheafificationMap (cotangentPresheaf f₁) n).app (op ⊤)
        (exteriorPower.ιMulti Γ(X, ⊤) n
          (fun j => (cotangentPresheafDerivation f₁).d (z j)))) =
    (exteriorSheafificationMap (cotangentPresheaf f₂) n).app (op ⊤)
      (exteriorPower.ιMulti Γ(X, ⊤) n
        (fun j => (cotangentPresheafDerivation f₂).d (z j))) := by
  cases h
  rfl

private theorem nativeOrdinaryCoordinateWedge
    (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]
    (n : ℕ) (z : Fin n → A) :
    affineExteriorCotangentToOpen K A n (op ⊤)
      (exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D K A (z j))) =
    exteriorPower.ιMulti Γ(Spec A, ⊤) n
      (fun j => (cotangentPresheafDerivation (affineStructuralMap K A)).d
        (affineCoordinateMap A (op ⊤) (z j))) := by
  have h := affineExteriorCotangentToOpen_wedge K A n (op ⊤)
    (fun j => KaehlerDifferential.D K A (z j))
  have hv : (fun j => (affineOrdinaryCotangentSemilinear K A (op ⊤)).toFun
      (KaehlerDifferential.D K A (z j))) =
      (fun j => (cotangentPresheafDerivation (affineStructuralMap K A)).d
        (affineCoordinateMap A (op ⊤) (z j))) :=
    funext (fun j => affineOrdinaryCotangentToOpen_D K A (op ⊤) (z j))
  exact h.trans (congrArg (exteriorPower.ιMulti Γ(Spec A, ⊤) n) hv)

private theorem nativeAffineCoordinateTop (A : CommRingCat.{u}) :
    affineCoordinateMap A (op ⊤) = (Scheme.ΓSpecIso A).inv := by
  unfold affineCoordinateMap
  rw [show ((⊤ : (Spec A).Opens).leTop).op = 𝟙 (op (⊤ : (Spec A).Opens)) from
    Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem nativeAffineCoordinateImage
    (A B : CommRingCat.{u}) (φ : A ⟶ B) (z : A) :
    (Spec.map φ).appTop (affineCoordinateMap A (op ⊤) z) =
      affineCoordinateMap B (op ⊤) (φ z) := by
  rw [nativeAffineCoordinateTop, nativeAffineCoordinateTop]
  have hs := (Scheme.ΓSpecIso_inv_naturality φ).symm
  exact congr($(hs) z)

private theorem nativeCotangentCoordinateImage
    {K : Type u} [Field K] (A B : CommRingCat.{u})
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (z : A) :
    (show (cotangentPresheaf
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A)).obj (op ⊤) from
      (cotangentPresheafMorphism (affineStructuralMap K A)
        (Spec.map (CommRingCat.ofHom φ.toRingHom))).app (op ⊤)
          ((cotangentPresheafDerivation (affineStructuralMap K A)).d
            (affineCoordinateMap A (op ⊤) z))) =
    (cotangentPresheafDerivation
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A)).d
        (affineCoordinateMap B (op ⊤) (φ z)) := by
  have h₁ := cotangentPresheafMorphism_d (affineStructuralMap K A)
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) ⊤ (affineCoordinateMap A (op ⊤) z)
  have h₂ := nativeAffineCoordinateImage A B (CommRingCat.ofHom φ.toRingHom) z
  have h₃ := congrArg (cotangentPresheafDerivation
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A)).d h₂
  -- These are already typed original equalities.  Construct their ordinary
  -- transitivity term without elaborating the entire Spec-module structure.
  -- The unchanged ordinary kernel verifies the resulting Eq.trans proof.
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let findLocal (s : String) : Lean.MetaM Lean.Expr := do
      for d in ctx do
        if d.userName.eraseMacroScopes == Lean.Name.mkSimple s then
          return Lean.mkFVar d.fvarId
      throwError "missing original equality {s}"
    let h₁ ← findLocal "h₁"
    let h₃ ← findLocal "h₃"
    let t₁ ← Lean.Meta.whnf (← Lean.Meta.inferType h₁)
    let t₃ ← Lean.Meta.whnf (← Lean.Meta.inferType h₃)
    unless t₁.isAppOfArity ``Eq 3 && t₃.isAppOfArity ``Eq 3 do
      throwError "expected original equalities"
    let .const _ levels := t₁.getAppFn | throwError "first equality has no constant head"
    let a₁ := t₁.getAppArgs
    let a₃ := t₃.getAppArgs
    let proof := Lean.mkAppN (Lean.mkConst ``Eq.trans levels)
      #[a₁[0]!, a₁[1]!, a₁[2]!, a₃[2]!, h₁, h₃]
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

variable {K : Type u} [Field K] (A B : CommRingCat.{u})
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K A)]

private def sameValue {α : Type u} (a : α) : α :=
  Classical.choose (show ∃ b : α, b = a from ⟨a, rfl⟩)

private theorem sameValue_eq {α : Type u} (a : α) : sameValue a = a :=
  Classical.choose_spec (show ∃ b : α, b = a from ⟨a, rfl⟩)

private def actualCanonicalΓTransport
    {K : Type u} [Field K] (B : CommRingCat.{u})
    {f₁ f₂ : Spec B ⟶ Spec (.of K)} (h : f₁ = f₂) (d : ℕ) :
    (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ d) ⟶
      (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₂ d) :=
  (moduleSpecΓFunctor (R := B)).map
    (X := exteriorCotangentSheaf f₁ d) (Y := exteriorCotangentSheaf f₂ d)
    (eqToHom (congrArg (fun f => exteriorCotangentSheaf f d) h))

private def affineCanonicalΓTransport
    {K : Type u} [Field K] (B : CommRingCat.{u})
    {f₁ f₂ : Spec B ⟶ Spec (.of K)} (h : f₁ = f₂) (d : ℕ) :
    (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ d) ⟶
      (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₂ d) :=
  sameValue (actualCanonicalΓTransport B h d)

private theorem affineCanonicalΓTransport_eq
    {K : Type u} [Field K] (B : CommRingCat.{u})
    {f₁ f₂ : Spec B ⟶ Spec (.of K)} (h : f₁ = f₂) (d : ℕ) :
    affineCanonicalΓTransport B h d = actualCanonicalΓTransport B h d :=
  sameValue_eq (actualCanonicalΓTransport B h d)

/-- The native canonical differential of the same original algebra map,
with the actual original field structure on its target. -/
def affineAlgebraCanonicalPullbackMap :
    (moduleSpecΓFunctor (R := A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K A) n) ⟶
    (ModuleCat.restrictScalars φ.toRingHom).obj
      ((moduleSpecΓFunctor (R := B)).obj
        (exteriorCotangentSheaf (affineStructuralMap K B) n)) :=
  nativeCanonicalPullbackMap (affineStructuralMap K A)
      (CommRingCat.ofHom φ.toRingHom) n ≫
    (ModuleCat.restrictScalars φ.toRingHom).map
      (affineCanonicalΓTransport B
        (affineAlgebraMap_structuralSquare K A B φ) n)



/-- The actual native canonical section represented by an ordinary
coordinate wedge, with its original affine coefficient action. -/
def affineCanonicalCoordinateSection (K : Type u) [Field K]
    (A : CommRingCat.{u}) [Algebra K A] (n : ℕ) (z : Fin n → A) :
    (moduleSpecΓFunctor (R := A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K A) n) :=
  ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K A)) n).app
    (op ⊤)).hom.toFun ((affineExteriorCotangentToOpen K A n (op ⊤)).hom.toFun
      (exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D K A (z j))))


private theorem nativeCanonicalCoordinateSection_eq
    (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]
    (d : ℕ) (z : Fin d → A) :
    affineCanonicalCoordinateSection K A d z =
      exteriorSheafSection (cotangentPresheaf (affineStructuralMap K A)) d ⊤
        (fun j => (cotangentPresheafDerivation (affineStructuralMap K A)).d
          (affineCoordinateMap A (op ⊤) (z j))) := by
  exact congrArg
    ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K A)) d).app
      (op ⊤)).hom.toFun (nativeOrdinaryCoordinateWedge K A d z)

private theorem nativeSchemeCoordinateSection
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X) (d : ℕ) (z : Fin d → Γ(X, ⊤)) :
    ((exteriorCotangentSheafMorphism f g d).val.app (op ⊤)).hom.toFun
      (exteriorSheafSection (cotangentPresheaf f) d ⊤
        (fun j => (cotangentPresheafDerivation f).d (z j))) =
    exteriorSheafSection (cotangentPresheaf (g ≫ f)) d (g ⁻¹ᵁ ⊤)
      (fun j => (cotangentPresheafDerivation (g ≫ f)).d (g.app ⊤ (z j))) := by
  have h₁ := exteriorCotangentSheafMorphism_wedge f g d ⊤
    (fun j => (cotangentPresheafDerivation f).d (z j))
  have hv : (fun j => (cotangentMorphismSemilinear f g (op ⊤)).toFun
      ((cotangentPresheafDerivation f).d (z j))) =
      (fun j => (cotangentPresheafDerivation (g ≫ f)).d (g.app ⊤ (z j))) :=
    funext (fun j => cotangentPresheafMorphism_d f g ⊤ (z j))
  exact h₁.trans (congrArg
    (exteriorSheafSection (cotangentPresheaf (g ≫ f)) d (g ⁻¹ᵁ ⊤)) hv)

private theorem nativeExteriorTransportCoordinateSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f₁ f₂ : X ⟶ Spec (.of K)} (h : f₁ = f₂) (d : ℕ) (z : Fin d → Γ(X, ⊤)) :
    ((eqToHom (congrArg (fun f => exteriorCotangentSheaf f d) h)).val.app
      (op ⊤)).hom.toFun
      (exteriorSheafSection (cotangentPresheaf f₁) d ⊤
        (fun j => (cotangentPresheafDerivation f₁).d (z j))) =
    exteriorSheafSection (cotangentPresheaf f₂) d ⊤
      (fun j => (cotangentPresheafDerivation f₂).d (z j)) := by
  cases h
  rfl


private theorem nativeAffineSheafCoordinateSection
    {K : Type u} [Field K] (A B : CommRingCat.{u})
    [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B) (d : ℕ) (z : Fin d → A) :
    ((exteriorCotangentSheafMorphism (affineStructuralMap K A)
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) d).val.app (op ⊤)).hom.toFun
      (affineCanonicalCoordinateSection K A d z) =
    exteriorSheafSection (cotangentPresheaf
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A)) d ⊤
      (fun j => (cotangentPresheafDerivation
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A)).d
          (affineCoordinateMap B (op ⊤) (φ (z j)))) := by
  let f := affineStructuralMap K A
  let g := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have h₀ := congrArg ((exteriorCotangentSheafMorphism f g d).val.app (op ⊤)).hom.toFun
    (nativeCanonicalCoordinateSection_eq K A d z)
  have h₁ := nativeSchemeCoordinateSection f g d
    (fun j => affineCoordinateMap A (op ⊤) (z j))
  have hv : (fun j => (cotangentPresheafDerivation (g ≫ f)).d
      (g.app ⊤ (affineCoordinateMap A (op ⊤) (z j)))) =
      (fun j => (cotangentPresheafDerivation (g ≫ f)).d
        (affineCoordinateMap B (op ⊤) (φ (z j)))) :=
    funext (fun j => congrArg (cotangentPresheafDerivation (g ≫ f)).d
      (nativeAffineCoordinateImage A B (CommRingCat.ofHom φ.toRingHom) (z j)))
  have h₂ := congrArg
    (exteriorSheafSection (cotangentPresheaf (g ≫ f)) d (g ⁻¹ᵁ ⊤)) hv
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let findLocal (s : String) : Lean.MetaM Lean.Expr := do
      for d in ctx do
        if d.userName.eraseMacroScopes == Lean.Name.mkSimple s then
          return Lean.mkFVar d.fvarId
      throwError "missing native equality {s}"
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
    let mut proof ← findLocal "h₀"
    for s in ["h₁", "h₂"] do
      proof ← transProof proof (← findLocal s)
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []


private theorem nativeΓTransportCoordinateSection
    {K : Type u} [Field K] (B : CommRingCat.{u})
    {f₁ f₂ : Spec B ⟶ Spec (.of K)} (h : f₁ = f₂) (d : ℕ)
    (z : Fin d → Γ(Spec B, ⊤)) :
    (affineCanonicalΓTransport B h d).hom.toFun
      (exteriorSheafSection (cotangentPresheaf f₁) d ⊤
        (fun j => (cotangentPresheafDerivation f₁).d (z j))) =
    exteriorSheafSection (cotangentPresheaf f₂) d ⊤
      (fun j => (cotangentPresheafDerivation f₂).d (z j)) := by
  cases h
  rw [affineCanonicalΓTransport_eq]
  exact congrArg (fun t :
      (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ d) ⟶
        (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ d) =>
      t.hom.toFun (exteriorSheafSection (cotangentPresheaf f₁) d ⊤
        (fun j => (cotangentPresheafDerivation f₁).d (z j))))
    ((moduleSpecΓFunctor (R := B)).map_id (exteriorCotangentSheaf f₁ d))


private theorem affineAlgebraCanonicalPullbackMap_apply
    (w : (moduleSpecΓFunctor (R := A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K A) n)) :
    (affineAlgebraCanonicalPullbackMap A B φ n).hom.toFun w =
      (affineCanonicalΓTransport B (affineAlgebraMap_structuralSquare K A B φ) n).hom.toFun
        ((nativeCanonicalPullbackMap (affineStructuralMap K A)
          (CommRingCat.ofHom φ.toRingHom) n).hom.toFun w) := rfl


/-- Every original coordinate wedge follows the same arbitrary original
algebra map through its actual native canonical differential. -/
theorem affineAlgebraCanonicalPullbackMap_coordinate_wedge
    (z : Fin n → A) :
    (affineAlgebraCanonicalPullbackMap A B φ n).hom.toFun
      (affineCanonicalCoordinateSection K A n z) =
    affineCanonicalCoordinateSection K B n (fun j => φ (z j)) := by
  let f := affineStructuralMap K A
  let he := affineAlgebraMap_structuralSquare K A B φ
  let T := (affineCanonicalΓTransport B he n).hom.toFun
  have h₀ := affineAlgebraCanonicalPullbackMap_apply A B φ n
    (affineCanonicalCoordinateSection K A n z)
  have h₁ := congrArg T (nativeCanonicalPullbackMap_apply f
    (CommRingCat.ofHom φ.toRingHom) n (affineCanonicalCoordinateSection K A n z))
  have h₂ := congrArg T (nativeAffineSheafCoordinateSection A B φ n z)
  have h₃ := nativeΓTransportCoordinateSection B he n
    (fun j => affineCoordinateMap B (op ⊤) (φ (z j)))
  have h₄ := (nativeCanonicalCoordinateSection_eq K B n (fun j => φ (z j))).symm
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let findLocal (s : String) : Lean.MetaM Lean.Expr := do
      for d in ctx do
        if d.userName.eraseMacroScopes == Lean.Name.mkSimple s then
          return Lean.mkFVar d.fvarId
      throwError "missing native equality {s}"
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
    let mut proof ← findLocal "h₀"
    for s in ["h₁", "h₂", "h₃", "h₄"] do
      proof ← transProof proof (← findLocal s)
    (← Lean.Elab.Tactic.getMainGoal).assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
