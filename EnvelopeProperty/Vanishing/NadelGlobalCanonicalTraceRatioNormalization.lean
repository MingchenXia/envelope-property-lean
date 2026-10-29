import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalization
import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRatioSheafCandidate

/-!
# Differential normalization on the ratio charts of the adapted cover

Let `X` be integral and smooth of relative dimension `n` over `k`, let `π : Y' → X` be the
normalized adapted Kummer cover of an SNC datum `(F, L, m, σ)`, and let
`U ⊆ X` be an affine open with étale coordinates `v`. Over `U` the cover is the spectrum of
the *ratio algebra* `B_r = RatioRing F n L m σ hL hD y U v c j₀ w`, the joined Kummer algebra
whose coefficients are the branch ratios; `p : Spec B_r → Spec Γ(X, U)` is its spectrum map.
The ratio coefficients are, coefficientwise, the mixed coefficients `u_i v_{τ(i)}` (active
branches) and `u_i` (inactive branches) of a mixed Kummer chart
(`Joined.ratioCoefficient_eq`, `OriginalMixed.coefficient_eq_mixed`), and
`ratioCanonicalSheafCandidate` is the mixed sheaf candidate transported along this equality
and along the identification `U ↪ X → Spec k = Spec Γ(X, U) → Spec k`.

Main result, `ratioCanonicalSheafCandidate_differential`: under
`MixedCanonicalCandidateNormalization k`, the pushed canonical differential of `p` followed by
the ratio candidate is the affine pulled-line trace of `p`:
`p_*(dp) ≫ τ_r = T_{Ω^n}`.

The proof is the affine values criterion `affinePushforward_comp_eq_of_values`: both sides are
morphisms out of `p_* p^* Ω^n_U`, determined by their values on the sections `b · p^* w`, where
`p^* w` is the geometric pullback `ratioNativePullback` of `w`. The three value identities are
the standalone theorems `ratioCanonicalSheafCandidate_values_hD` (the value of `dp` on `p^* w`),
`ratioCanonicalSheafCandidate_values_hT` (the value `Tr_{B_r/Γ(X, U)}(b) · w` of the ratio
candidate on `b · p^* w`: transport along `U → Spec k = Spec Γ(X, U) → Spec k`, where the
geometric pullback becomes the algebraic pullback of forms, and along the coefficient
equality, where it is the normalization of the mixed candidate) and
`ratioCanonicalSheafCandidate_values_hS` (the value of the pulled-line trace).

Implementation note. The criterion is applied in `ratioCanonicalSheafCandidate_differential_of_eq`
to a *variable* `R` equal to the candidate, and the main theorem generalizes the candidate
before applying it. The candidate contains `eqToHom` casts between canonical sheaves of
morphisms that are equal but not definitionally equal; if the kernel ever had to evaluate the
candidate on a section (which it does when comparing two non-identical applications
`DFunLike.coe (T.app ⊤) x`), it would try to refute such definitional equalities by unfolding
the sheafified exterior powers. With `R` a variable this evaluation stops at once.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
open NadelCanonicalMixed NadelMixedKummer
open NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelGlobalAdaptedRoots NadelGlobalAdaptedModel NadelAdaptedChartMatching
open CyclicSectionSNCUniformFramedCharts
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local infixr:80 " ≫ₛ " => CategoryStruct.comp (obj := Scheme)

/-! ### Values of the canonical differential and of its transports -/

/-- The exterior pullback differential `dφ : φ^* Ω^n_g ⟶ Ω^n_{φ ≫ g}` sends the pulled-back top
section `φ^* m` to the geometric pullback of `m`. -/
private theorem pullbackMap_unit_value {K : Type u} [Field K] {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (g : Spec A ⟶ Spec (.of K)) (n : ℕ)
    (m : (exteriorCotangentSheaf g n).val.obj (Opposite.op ⊤)) :
    affineRawModuleMap (exteriorCotangentSheafPullbackMap g (Spec.map φ) n)
        (affineRawPullbackUnit φ (exteriorCotangentSheaf g n) m) =
      affinePushforwardRawRead φ (exteriorCotangentSheaf (Spec.map φ ≫ g) n)
        (affineRawModuleMap (exteriorCotangentSheafMorphism g (Spec.map φ) n) m) := by
  have hu := affinePullbackUnitTop_eq_unit φ (exteriorCotangentSheaf g n) m
  have hd := congrArg (fun t => t.app ⊤ m)
    (exteriorCotangentSheafPullbackMap_unit g (Spec.map φ) n)
  change (exteriorCotangentSheafPullbackMap g (Spec.map φ) n).app ⊤
      (affinePullbackUnitTop (Spec.map φ) (exteriorCotangentSheaf g n) m) =
    (exteriorCotangentSheafMorphism g (Spec.map φ) n).app ⊤ m
  rw [hu]
  exact hd

run_cmd
  let name := Lean.mkPrivateNameCore
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceRatioSheafCandidate
    `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.coefficientSheafCandidate
  unless (← Lean.getEnv).contains name do
    throwError "missing original coefficient sheaf candidate"
  Lean.Elab.Command.modifyScope fun scope =>
    { scope with openDecls :=
        Lean.OpenDecl.explicit `originalCoefficientSheafCandidate name :: scope.openDecls }

/-- On the mixed coefficients themselves, the coefficient-transported candidate is the mixed
sheaf candidate. -/
private theorem coefficientSheafCandidate_mixed
    {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (τ : I ↪ Fin n) (u : Fin q → Aˣ)
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) :
    originalCoefficientSheafCandidate x N I τ u (mixedCoefficient x I τ u) rfl hx hN htame =
      mixedCanonicalSheafCandidate x N I τ u hx hN htame :=
  rfl

/-- Under the normalization of the mixed candidate, the coefficient-transported candidate sends
`b · φ^* w` to `Tr(b) · w`, for the algebraic pullback `φ^*` of forms. -/
private theorem coefficientSheafCandidate_value
    {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (τ : I ↪ Fin n) (u : Fin q → Aˣ) (d : Fin q → A)
    (hd : d = mixedCoefficient x I τ u)
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (hmix : MixedCanonicalCandidateNormalization k)
    [SmoothOfRelativeDimension n (affineStructuralMap k (.of A))]
    (b : NadelMixedKummer.Ring N d)
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)) :
    (originalCoefficientSheafCandidate x N I τ u d hd hx hN htame).app ⊤
      (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap A (NadelMixedKummer.Ring N d)))
        (exteriorCotangentSheaf (affineStructuralMap k (.of (NadelMixedKummer.Ring N d))) n)
        (ModuleSpecGammaCarrier.toRaw (.of (NadelMixedKummer.Ring N d))
          (exteriorCotangentSheaf (affineStructuralMap k (.of (NadelMixedKummer.Ring N d))) n)
          (b • restrictedNativeSection
            (IsScalarTower.toAlgHom k A (NadelMixedKummer.Ring N d)).toRingHom
            ((moduleSpecΓFunctor (R := .of (NadelMixedKummer.Ring N d))).obj
              (exteriorCotangentSheaf (affineStructuralMap k (.of (NadelMixedKummer.Ring N d))) n))
            ((affineAlgebraCanonicalPullbackMap (.of A) (.of (NadelMixedKummer.Ring N d))
              (IsScalarTower.toAlgHom k A (NadelMixedKummer.Ring N d)) n).hom.toFun w)))) =
      ModuleSpecGammaCarrier.toRaw (.of A)
        (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)
        (Algebra.trace A (NadelMixedKummer.Ring N d) b • w) := by
  subst d
  rw [coefficientSheafCandidate_mixed x N I τ u hx hN htame]
  exact mixedCanonicalSheafCandidate_native x N I τ u hx hN htame hmix b w

/-! ### Raw-value helpers for the `hT` side goal

The value of the ratio candidate is computed through the regular-head wrappers
`affineRawModuleMap`, `affinePushforwardRawSection`, `ModuleSpecGammaCarrier.toRaw` and the
local wrappers below, so that the kernel compares the intermediate values argument by
argument and never has to evaluate a scalar action or a sheaf map on a section. Every
change of presentation is made by a generic lemma (all modules arbitrary) proved by `rfl`. -/

/-- The scalar action on native top sections, read in the raw carrier (scalars in a bundled
ring). -/
private def ratioSmulRaw (B : CommRingCat.{u}) (M : (Spec B).Modules) (b : B)
    (s : (moduleSpecΓFunctor (R := B)).obj M) : M.val.obj (Opposite.op ⊤) :=
  ModuleSpecGammaCarrier.toRaw B M (b • s)

/-- The scalar action on native top sections, read in the raw carrier (scalars in an unbundled
ring). -/
private def ratioSmulRawT (A₀ : Type u) [CommRing A₀] (M : (Spec (.of A₀)).Modules) (a : A₀)
    (s : (moduleSpecΓFunctor (R := .of A₀)).obj M) : M.val.obj (Opposite.op ⊤) :=
  ModuleSpecGammaCarrier.toRaw (.of A₀) M (a • s)

/-- The trace of an algebra, as a regular-head value. -/
private def ratioTraceValue (A₀ B₀ : Type u) [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]
    (b : B₀) : A₀ :=
  Algebra.trace A₀ B₀ b

/-- Transport of a native top section along an equality of modules. -/
private def ratioTransportSection {R : CommRingCat.{u}} {M N : (Spec R).Modules} (h : M = N)
    (w : (moduleSpecΓFunctor (R := R)).obj M) : (moduleSpecΓFunctor (R := R)).obj N :=
  ModuleSpecGammaCarrier.toNative R N
    ((eqToIso h).hom.app ⊤ (ModuleSpecGammaCarrier.toRaw R M w))

/-- The geometric pullback of a top form along `Spec φ`, in native sections. -/
private def ratioGeometricPullback {K : Type u} [Field K] {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (g : Spec A ⟶ Spec (.of K)) (n : ℕ)
    (w : (moduleSpecΓFunctor (R := A)).obj (exteriorCotangentSheaf g n)) :
    (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf (Spec.map φ ≫ g) n) :=
  ModuleSpecGammaCarrier.toNative B _ (affinePushforwardRawRead φ _
    (affineRawModuleMap (exteriorCotangentSheafMorphism g (Spec.map φ) n)
      (ModuleSpecGammaCarrier.toRaw A _ w)))

/-- The algebraic pullback of top forms along `A → B₀`, in native sections. -/
private def ratioAlgebraicPullback {K : Type u} [Field K] (A : CommRingCat.{u}) (B₀ : Type u)
    [CommRing B₀] [Algebra K A] [Algebra K B₀] [Algebra A B₀] [IsScalarTower K A B₀] (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K (.of A))]
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K (.of A)) n)) :
    (moduleSpecΓFunctor (R := .of B₀)).obj
      (exteriorCotangentSheaf (affineStructuralMap K (.of B₀)) n) :=
  restrictedNativeSection (IsScalarTower.toAlgHom K A B₀).toRingHom
    ((moduleSpecΓFunctor (R := .of B₀)).obj
      (exteriorCotangentSheaf (affineStructuralMap K (.of B₀)) n))
    ((affineAlgebraCanonicalPullbackMap (.of A) (.of B₀) (IsScalarTower.toAlgHom K A B₀)
      n).hom.toFun w)

/-- A top component of a module map, read as the raw module map in the raw carrier. -/
private theorem ratioHT_app_of_raw {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    (x : Γ(F, ⊤)) (r : G.val.obj (Opposite.op ⊤)) (h : affineRawModuleMap f x = r) :
    f.app ⊤ x = r :=
  h

/-- A top component of a module map is its raw module map. -/
private theorem ratioHT_app_eq_raw {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    (x : Γ(F, ⊤)) : f.app ⊤ x = affineRawModuleMap f x :=
  rfl

/-- The inverse of `eqToIso` undoes its forward map on raw top sections. -/
private theorem ratioHT_eqToIso_inv_hom {X : Scheme.{u}} {M N : X.Modules} (h : M = N)
    (r : M.val.obj (Opposite.op ⊤)) :
    affineRawModuleMap (eqToIso h).inv (affineRawModuleMap (eqToIso h).hom r) = r := by
  subst h
  rfl

/-- The forward map of `eqToIso h` in raw form, as the raw map of `eqToHom h'`. -/
private theorem ratioHT_eqToIso_hom_raw {X : Scheme.{u}} {M N : X.Modules} (h h' : M = N)
    (x : M.val.obj (Opposite.op ⊤)) :
    affineRawModuleMap (eqToIso h).hom x = affineRawModuleMap (eqToHom h') x :=
  rfl

/-- Transport along a reflexive equality is the identity. -/
private theorem ratioHT_transport_refl {R : CommRingCat.{u}} {M : (Spec R).Modules} (h : M = M)
    (w : (moduleSpecΓFunctor (R := R)).obj M) : ratioTransportSection h w = w := by
  unfold ratioTransportSection
  rw [eqToIso_refl]
  rfl

/-- The unbundled scalar action on native sections reads as the section action. -/
private theorem ratioHT_smulT_toRaw {B₀ : Type u} [CommRing B₀] (M : (Spec (.of B₀)).Modules)
    (b : B₀) (s : (moduleSpecΓFunctor (R := .of B₀)).obj M) :
    ModuleSpecGammaCarrier.toRaw (.of B₀) M (b • s) =
      (· • · : Γ(Spec (.of B₀), ⊤) → Γ(M, ⊤) → Γ(M, ⊤))
        ((Scheme.ΓSpecIso (.of B₀)).inv b)
        (show Γ(M, ⊤) from ModuleSpecGammaCarrier.toRaw (.of B₀) M s) :=
  rfl

/-- A module map on `Spec B` commutes with the `B`-action on native top sections. -/
private theorem ratioHT_app_toRaw_smul {B : CommRingCat.{u}} {P Q : (Spec B).Modules}
    (E : P ⟶ Q) (b : B) (s : (moduleSpecΓFunctor (R := B)).obj P)
    (s' : (moduleSpecΓFunctor (R := B)).obj Q)
    (h : E.app ⊤ (ModuleSpecGammaCarrier.toRaw B P s) = ModuleSpecGammaCarrier.toRaw B Q s') :
    E.app ⊤ (ModuleSpecGammaCarrier.toRaw B P (b • s)) =
      ModuleSpecGammaCarrier.toRaw B Q (b • s') :=
  (congrArg (fun t => E.app ⊤ t) (moduleSpecGamma_smul_toRaw B P b s)).trans
    ((Scheme.Modules.Hom.app_smul E _ _).trans
      ((congrArg (fun t => (Scheme.ΓSpecIso B).inv b • t) h).trans
        (moduleSpecGamma_smul_toRaw B Q b s').symm))

/-- Unbundled-scalar linearity of a module map on native top sections. -/
private theorem ratioHT_app_toRaw_smulT {B₀ : Type u} [CommRing B₀]
    {P Q : (Spec (.of B₀)).Modules} (E : P ⟶ Q) (b : B₀)
    (s : (moduleSpecΓFunctor (R := .of B₀)).obj P)
    (s' : (moduleSpecΓFunctor (R := .of B₀)).obj Q)
    (h : E.app ⊤ (ModuleSpecGammaCarrier.toRaw (.of B₀) P s) =
      ModuleSpecGammaCarrier.toRaw (.of B₀) Q s') :
    E.app ⊤ (ModuleSpecGammaCarrier.toRaw (.of B₀) P (b • s)) =
      ModuleSpecGammaCarrier.toRaw (.of B₀) Q (b • s') :=
  (congrArg (fun t => E.app ⊤ t) (ratioHT_smulT_toRaw P b s)).trans
    ((Scheme.Modules.Hom.app_smul E _ _).trans
      ((congrArg (fun t => (Scheme.ΓSpecIso (.of B₀)).inv b • t) h).trans
        (ratioHT_smulT_toRaw Q b s').symm))

/-- **The value of a candidate given by its defining composite.** If `T` is (heterogeneously)
the composite `(pushforward φ)_* E_B ≫ T_aff ≫ E_A`, read over `Spec (of A)` on objects `F`, `G`
equal to its source and target, then the raw value of `T` on `x` is computed factor by factor.
All objects and morphisms are arbitrary, so the change of presentation happens here, once. -/
private theorem ratioHT_sandwich_heq {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {P Q : (Spec B).Modules} {M' M : (Spec A).Modules} (EB : P ⟶ Q)
    (Taff : (pushforward (Spec.map φ)).obj Q ⟶ M') (EA : M' ⟶ M)
    {F G : (Spec (CommRingCat.of A)).Modules} (T : F ⟶ G)
    (hT : HEq ((pushforward (Spec.map φ)).map EB ≫ Taff ≫ EA) T)
    (hF : (pushforward (Spec.map φ)).obj P = F) (hG : M = G)
    (x : F.val.obj (Opposite.op ⊤))
    (x' : ((pushforward (Spec.map φ)).obj P).val.obj (Opposite.op ⊤)) (hxx : HEq x x')
    (r : G.val.obj (Opposite.op ⊤)) (r' : M.val.obj (Opposite.op ⊤)) (hrr : HEq r r')
    (y : Q.val.obj (Opposite.op ⊤)) (z : M'.val.obj (Opposite.op ⊤))
    (hx : affineRawModuleMap EB (affinePushforwardRawRead φ P x') = y)
    (hy : affineRawModuleMap Taff (affinePushforwardRawSection φ Q y) = z)
    (hz : affineRawModuleMap EA z = r') :
    affineRawModuleMap T x = r := by
  subst hF hG
  cases eq_of_heq hT
  cases eq_of_heq hxx
  cases eq_of_heq hrr
  subst hx hy hz
  rfl

/-- The `hx` step with the pushed section given in its own presentation (`φ₁`, `P₁`, `s₁`). -/
private theorem ratioHT_pushed_heq {A A₁ B : CommRingCat.{u}} (φ : A ⟶ B) (φ₁ : A₁ ⟶ B)
    {P P₁ Q : (Spec B).Modules} (E : P ⟶ Q) (b : B)
    (s₁ : (moduleSpecΓFunctor (R := B)).obj P₁)
    (x : ((pushforward (Spec.map φ)).obj P).val.obj (Opposite.op ⊤))
    (hx : HEq x (affinePushforwardRawSection φ₁ P₁ (ModuleSpecGammaCarrier.toRaw B P₁ (b • s₁))))
    (hA : A₁ = A) (hφ : HEq φ₁ φ) (hP : P₁ = P)
    (s : (moduleSpecΓFunctor (R := B)).obj P) (hs : HEq s₁ s)
    (s' : (moduleSpecΓFunctor (R := B)).obj Q)
    (h : affineRawModuleMap E (ModuleSpecGammaCarrier.toRaw B P s) =
      ModuleSpecGammaCarrier.toRaw B Q s') :
    affineRawModuleMap E (affinePushforwardRawRead φ P x) = ratioSmulRaw B Q b s' := by
  subst hA hP
  cases eq_of_heq hφ
  cases eq_of_heq hx
  cases eq_of_heq hs
  exact ratioHT_app_toRaw_smul E b s₁ s' h

/-- The outer transport step: `e.hom (a • w) = a • transport w`. -/
private theorem ratioHT_transport_smul {A₀ : Type u} [CommRing A₀]
    {M N : (Spec (.of A₀)).Modules} (h : M = N) (a : A₀)
    (w : (moduleSpecΓFunctor (R := .of A₀)).obj M) :
    affineRawModuleMap (eqToIso h).hom (ModuleSpecGammaCarrier.toRaw (.of A₀) M (a • w)) =
      ratioSmulRawT A₀ N a (ratioTransportSection h w) :=
  ratioHT_app_toRaw_smulT _ a w _ rfl

/-- The trace as its regular-head value. -/
private theorem ratioHT_trace_eq {A₀ B₀ : Type u} {iA₀ : CommRing A₀} {iB₀ : CommRing B₀}
    {iA : Algebra A₀ B₀} (b : B₀) : Algebra.trace A₀ B₀ b = ratioTraceValue A₀ B₀ b :=
  rfl

/-- The algebraic pullback of `w` along `A → B₀`, read in its defining presentation. -/
private theorem ratioHT_algebraicPullback_eq {K : Type u} [Field K] (A : CommRingCat.{u})
    (B₀ : Type u) [CommRing B₀] [Algebra K A] [Algebra K B₀] [Algebra A B₀]
    [IsScalarTower K A B₀] (n : ℕ) [SmoothOfRelativeDimension n (affineStructuralMap K (.of A))]
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K (.of A)) n)) :
    ratioAlgebraicPullback A B₀ n w =
      restrictedNativeSection (IsScalarTower.toAlgHom K A B₀).toRingHom
        ((moduleSpecΓFunctor (R := .of B₀)).obj
          (exteriorCotangentSheaf (affineStructuralMap K (.of B₀)) n))
        ((affineAlgebraCanonicalPullbackMap (.of A) (.of B₀)
          (IsScalarTower.toAlgHom K A B₀) n).hom.toFun w) :=
  rfl

/-- The bundled and unbundled scalar actions agree. -/
private theorem ratioHT_smulRaw_eq {B₀ : Type u} [CommRing B₀] (M : (Spec (.of B₀)).Modules)
    (b : ↑(CommRingCat.of B₀)) (s : (moduleSpecΓFunctor (R := .of B₀)).obj M) :
    ratioSmulRaw (.of B₀) M b s = ratioSmulRawT B₀ M b s :=
  rfl

/-- The unbundled scalar action wrapper, unfolded. -/
private theorem ratioHT_smulRawT_eq {A₀ : Type u} [CommRing A₀] (M : (Spec (.of A₀)).Modules)
    (a : A₀) (s : (moduleSpecΓFunctor (R := .of A₀)).obj M) :
    ratioSmulRawT A₀ M a s = ModuleSpecGammaCarrier.toRaw (.of A₀) M (a • s) :=
  rfl

/-- The algebraic pullback of top forms is the transport of the geometric pullback (unbundled
codomain `B₀`). -/
private theorem ratioHT_transported_geometric {K : Type u} [Field K] (A₀ B₀ : Type u)
    [CommRing A₀] [CommRing B₀] [Algebra K A₀] [Algebra K B₀] [Algebra A₀ B₀]
    [IsScalarTower K A₀ B₀] (n : ℕ)
    [SmoothOfRelativeDimension n (affineStructuralMap K (.of A₀))]
    (hfield : Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)) ≫ affineStructuralMap K (.of A₀) =
      affineStructuralMap K (.of B₀))
    (w : (moduleSpecΓFunctor (R := .of A₀)).obj
      (exteriorCotangentSheaf (affineStructuralMap K (.of A₀)) n)) :
    affineRawModuleMap (eqToHom (congrArg (fun z => exteriorCotangentSheaf z n) hfield))
        (affinePushforwardRawRead (CommRingCat.ofHom (algebraMap A₀ B₀))
          (exteriorCotangentSheaf
            (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀)) ≫ affineStructuralMap K (.of A₀)) n)
          (affineRawModuleMap (exteriorCotangentSheafMorphism (affineStructuralMap K (.of A₀))
            (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) n)
              (ModuleSpecGammaCarrier.toRaw (.of A₀)
                (exteriorCotangentSheaf (affineStructuralMap K (.of A₀)) n) w))) =
      ModuleSpecGammaCarrier.toRaw (.of B₀)
        (exteriorCotangentSheaf (affineStructuralMap K (.of B₀)) n)
        (restrictedNativeSection (IsScalarTower.toAlgHom K A₀ B₀).toRingHom
          ((moduleSpecΓFunctor (R := .of B₀)).obj
            (exteriorCotangentSheaf (affineStructuralMap K (.of B₀)) n))
          ((affineAlgebraCanonicalPullbackMap (.of A₀) (.of B₀)
            (IsScalarTower.toAlgHom K A₀ B₀) n).hom.toFun w)) :=
  (affineAlgebraCanonicalPullbackMap_toRaw (.of A₀) (.of B₀)
    (IsScalarTower.toAlgHom K A₀ B₀) n w).symm

/-- **Geometric transport.** Transporting the geometric pullback of a form along
`g = (Spec A → Spec K)` and `Spec B₀ → Spec A → Spec K = Spec B₀ → Spec K` gives the algebraic
pullback of the transported form. -/
private theorem ratioHT_geometric_transport {K : Type u} [Field K] (A : CommRingCat.{u})
    (B₀ : Type u) [CommRing B₀] [Algebra K A] [Algebra K B₀] [Algebra A B₀]
    [IsScalarTower K A B₀] (n : ℕ) [SmoothOfRelativeDimension n (affineStructuralMap K (.of A))]
    (φ : A ⟶ CommRingCat.of B₀) (hφ : φ = CommRingCat.ofHom (algebraMap A B₀))
    (g : Spec A ⟶ Spec (.of K)) (hbase : g = affineStructuralMap K (.of A))
    (hfield : Spec.map (CommRingCat.ofHom (algebraMap A B₀)) ≫ affineStructuralMap K (.of A) =
      affineStructuralMap K (.of B₀))
    (hB : exteriorCotangentSheaf (Spec.map φ ≫ g) n =
      exteriorCotangentSheaf (affineStructuralMap K (.of B₀)) n)
    (hA : exteriorCotangentSheaf g n = exteriorCotangentSheaf (affineStructuralMap K (.of A)) n)
    (w : (moduleSpecΓFunctor (R := A)).obj (exteriorCotangentSheaf g n)) :
    affineRawModuleMap (eqToIso hB).hom
        (ModuleSpecGammaCarrier.toRaw (.of B₀) _ (ratioGeometricPullback φ g n w)) =
      ModuleSpecGammaCarrier.toRaw (.of B₀) _
        (ratioAlgebraicPullback A B₀ n (ratioTransportSection hA w)) := by
  subst hφ
  subst hbase
  rw [ratioHT_transport_refl hA w]
  exact (ratioHT_eqToIso_hom_raw hB hB _).trans
    (ratioHT_transported_geometric (K := K) A B₀ n hfield w)

/-- **Value of the coefficient-transported candidate**, in raw regular-head form. -/
private theorem ratioHT_coefficient_value {K : Type u} [Field K] [CharZero K]
    (A : CommRingCat.{u}) [Algebra K A] [Nontrivial A] {n q : ℕ} (x : Fin n → A)
    (N : Fin q → ℕ) (I : Set (Fin q)) (τ : I ↪ Fin n) (u : Fin q → Aˣ) (d : Fin q → A)
    (hd : d = mixedCoefficient x I τ u)
    (hx : (MvPolynomial.aeval (R := K) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (hmix : MixedCanonicalCandidateNormalization K)
    [SmoothOfRelativeDimension n (affineStructuralMap K (.of A))]
    (b : ↑(CommRingCat.of (NadelMixedKummer.Ring N d)))
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap K (.of A)) n)) :
    affineRawModuleMap (originalCoefficientSheafCandidate x N I τ u d hd hx hN htame)
      (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap A (NadelMixedKummer.Ring N d)))
        (exteriorCotangentSheaf (affineStructuralMap K (.of (NadelMixedKummer.Ring N d))) n)
        (ratioSmulRaw (.of (NadelMixedKummer.Ring N d))
          (exteriorCotangentSheaf (affineStructuralMap K (.of (NadelMixedKummer.Ring N d))) n) b
          (ratioAlgebraicPullback A (NadelMixedKummer.Ring N d) n w))) =
      ratioSmulRawT A (exteriorCotangentSheaf (affineStructuralMap K (.of A)) n)
        (ratioTraceValue A (NadelMixedKummer.Ring N d) b) w := by
  refine Eq.trans (congrArg (fun t => affineRawModuleMap
      (originalCoefficientSheafCandidate x N I τ u d hd hx hN htame)
      (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap A (NadelMixedKummer.Ring N d)))
        (exteriorCotangentSheaf (affineStructuralMap K (.of (NadelMixedKummer.Ring N d))) n) t))
      ((ratioHT_smulRaw_eq _ b _).trans
        ((congrArg (fun s => ratioSmulRawT (NadelMixedKummer.Ring N d)
          (exteriorCotangentSheaf (affineStructuralMap K (.of (NadelMixedKummer.Ring N d))) n) b s)
          (ratioHT_algebraicPullback_eq (K := K) A (NadelMixedKummer.Ring N d) n w)).trans
          (ratioHT_smulRawT_eq _ b _)))) ?_
  refine Eq.trans (ratioHT_app_eq_raw _ _).symm ?_
  refine Eq.trans (coefficientSheafCandidate_value x N I τ u d hd hx hN htame hmix b w) ?_
  refine Eq.trans (ratioHT_smulRawT_eq _ _ w).symm ?_
  exact congrArg (fun t => ratioSmulRawT A
    (exteriorCotangentSheaf (affineStructuralMap K (.of A)) n) t w)
    (ratioHT_trace_eq (A₀ := A) (B₀ := NadelMixedKummer.Ring N d) b)


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
    {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (het : Etale (toAffineSpace f U.1 v)) (hcinj : Function.Injective c)
    (hm : ∀ i, 0 < m i) (htame : ∀ i, IsUnit (m i : Γ(X, U.1)))

local notation "Bᵣ" => RatioRing F n L m σ hL hD y U v c j₀ w

/-- The geometric pullback `w ↦ p^* w` of a top form on `U` along the ratio chart
`p : Spec B_r → Spec Γ(X, U)`, as a native section over `B_r`: the image of `w` under
`Ω^n_U → p_* Ω^n_{B_r}`. -/
def ratioNativePullback
    (w₀ : (moduleSpecΓFunctor (R := .of Γ(X, U.1))).obj
      (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)) :
    (moduleSpecΓFunctor (R := .of Bᵣ)).obj (exteriorCotangentSheaf
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) ≫ (U.2.fromSpec ≫ f)) n) :=
  ModuleSpecGammaCarrier.toNative _ _
    (affinePushforwardRawRead (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) _
      (affineRawModuleMap (exteriorCotangentSheafMorphism (U.2.fromSpec ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))) n)
        (ModuleSpecGammaCarrier.toRaw _ _ w₀)))

omit [IsIntegral X] [Nonempty U.1] [CharZero k] [SmoothOfRelativeDimension n f] in
/-- **Value of the differential.** The pushed canonical differential of the ratio chart sends
the pulled-back section `p^* w` to the geometric pullback `ratioNativePullback w`. -/
theorem ratioCanonicalSheafCandidate_values_hD
    (w₀ : (moduleSpecΓFunctor (R := .of Γ(X, U.1))).obj
        (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)) :
    affineRawModuleMap (exteriorCotangentSheafPullbackMap (U.2.fromSpec ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))) n)
      (affineRawPullbackUnit (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))
        (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)
        (ModuleSpecGammaCarrier.toRaw (.of Γ(X, U.1))
          (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n) w₀)) =
    affineRawSection (exteriorCotangentSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) ≫ (U.2.fromSpec ≫ f)) n)
      (ModuleSpecGammaCarrier.toRaw (.of Bᵣ) _
        (ratioNativePullback F n L m σ hL hD y U v c j₀ w f w₀)) :=
  pullbackMap_unit_value _ _ n _

omit [IsIntegral X] [CharZero k] [SmoothOfRelativeDimension n f] in
/-- **Value of the pulled-line trace.** The affine pulled-line trace of `Ω^n_U` along the ratio
chart sends `r · η(m)` to `Tr_{B_r/Γ(X, U)}(r) · m`. -/
theorem ratioCanonicalSheafCandidate_values_hS
    (hω : IsInvertible (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)) :
    letI : Module.Free Γ(X, U.1) Bᵣ := VaryingFinite.free (Joined.degree F n m)
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
    letI : Module.Finite Γ(X, U.1) Bᵣ := VaryingFinite.finite (Joined.degree F n m)
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
    ∀ (r : Γ(Spec (.of Bᵣ), ⊤)) (m₀ : Γ(exteriorCotangentSheaf (U.2.fromSpec ≫ f) n, ⊤)),
      (affinePulledLineTrace Γ(X, U.1) (.of Bᵣ) (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)
          hω).app ⊤
        (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))
          ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)))).obj
            (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n))
          ((· • · : Γ(Spec (.of Bᵣ), ⊤) →
              Γ((Scheme.Modules.pullback
                (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)))).obj
                  (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n), ⊤) →
              Γ((Scheme.Modules.pullback
                (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)))).obj
                  (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n), ⊤)) r
            (((pullbackPushforwardAdjunction
              (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)))).unit.app
                (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)).app ⊤ m₀))) =
        (· • · : Γ(Spec (.of Γ(X, U.1)), ⊤) → Γ(exteriorCotangentSheaf (U.2.fromSpec ≫ f) n, ⊤) →
            Γ(exteriorCotangentSheaf (U.2.fromSpec ≫ f) n, ⊤))
          ((Scheme.ΓSpecIso (.of Γ(X, U.1))).inv
            (Algebra.trace Γ(X, U.1) Bᵣ ((Scheme.ΓSpecIso (.of Bᵣ)).hom r))) m₀ := by
  intro r m₀
  let : Module.Free Γ(X, U.1) Bᵣ := VaryingFinite.free (Joined.degree F n m)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
  let : Module.Finite Γ(X, U.1) Bᵣ := VaryingFinite.finite (Joined.degree F n m)
    (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
  exact affinePulledLineTrace_trace_value _ _ _ _ r m₀

/-- **Value of the ratio candidate.** Under the normalization of the mixed candidate, the ratio
candidate (here any `R` equal to it) sends `b · p^* w` to `Tr_{B_r/Γ(X, U)}(b) · w`. -/
theorem ratioCanonicalSheafCandidate_values_hT
    (hmix : MixedCanonicalCandidateNormalization k)
    (R : (pushforward (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)))).obj
        (exteriorCotangentSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) ≫ (U.2.fromSpec ≫ f)) n) ⟶
      exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)
    (hR : ratioCanonicalSheafCandidate F n L m σ hL hD y U v c j₀ w f het hcinj hm htame = R) :
    ∀ (b : ↑(CommRingCat.of Bᵣ))
      (w₀ : (moduleSpecΓFunctor (R := .of Γ(X, U.1))).obj
        (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)),
      R.app ⊤ (affinePushforwardRawSection (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) _
        (ModuleSpecGammaCarrier.toRaw (.of Bᵣ) _
          (b • ratioNativePullback F n L m σ hL hD y U v c j₀ w f w₀))) =
        ModuleSpecGammaCarrier.toRaw (.of Γ(X, U.1)) (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)
          (Algebra.trace Γ(X, U.1) Bᵣ b • w₀) := by
  intro b w₀
  let := f.sectionsAlgebra U.1
  have : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hx : (MvPolynomial.aeval (R := k) v).toRingHom.Etale :=
    (etale_toAffineSpace_iff f U.2 v).mp het
  have : SmoothOfRelativeDimension n (affineStructuralMap k (.of Γ(X, U.1))) :=
    coordinateStructure_smooth v hx
  have hbase : U.2.fromSpec ≫ₛ f = affineStructuralMap k (.of Γ(X, U.1)) := by
    have hh := IsAffineOpen.SpecMap_appLE_fromSpec f
      (isAffineOpen_top (Spec (.of k))) U.2 le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hh
    exact hh.symm
  have hfield : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) ≫
      affineStructuralMap k (.of Γ(X, U.1)) = affineStructuralMap k (.of Bᵣ) :=
    affineAlgebraMap_structuralSquare k (.of Γ(X, U.1)) (.of Bᵣ)
      (IsScalarTower.toAlgHom k Γ(X, U.1) Bᵣ)
  have hA₀ : exteriorCotangentSheaf (U.2.fromSpec ≫ₛ f) n =
      exteriorCotangentSheaf (affineStructuralMap k (.of Γ(X, U.1))) n :=
    congrArg (fun z => exteriorCotangentSheaf z n) hbase
  delta ratioCanonicalSheafCandidate at hR
  dsimp only at hR
  refine ratioHT_app_of_raw _ _ _ ?_
  have hT := heq_of_eq hR
  refine ratioHT_sandwich_heq (A := Γ(X, U.1)) _ _ _ _ R hT ?hF ?hG _ _ HEq.rfl _ _ HEq.rfl ?y _
    ?hx ?hy (ratioHT_eqToIso_inv_hom _ _)
  case hF =>
    rfl
  case hG => rfl
  case y =>
    exact ratioSmulRaw (CommRingCat.of Bᵣ) _ b
      (ratioAlgebraicPullback Γ(X, U.1) Bᵣ n (ratioTransportSection hA₀ w₀))
  case hx =>
    refine ratioHT_pushed_heq _ (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) _ b
      (ratioNativePullback F n L m σ hL hD y U v c j₀ w f w₀) _ HEq.rfl rfl HEq.rfl rfl _ HEq.rfl _
      ?_
    exact ratioHT_geometric_transport Γ(X, U.1) Bᵣ n _ rfl _ hbase hfield _ hA₀ w₀
  case hy =>
    refine Eq.trans ?_ (ratioHT_transport_smul (A₀ := Γ(X, U.1)) _
      (Algebra.trace Γ(X, U.1) Bᵣ b) w₀).symm
    refine Eq.trans ?_ (congrArg (fun t => ratioSmulRawT Γ(X, U.1)
      (exteriorCotangentSheaf (affineStructuralMap k (.of Γ(X, U.1))) n) t
      (ratioTransportSection _ w₀)) (ratioHT_trace_eq (B₀ := Bᵣ) b)).symm
    exact ratioHT_coefficient_value (K := k) Γ(X, U.1) v (Joined.degree F n m) _ _ _
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w) _ hx _ _ hmix b _

/-- The ratio-chart normalization for any `R` equal to the ratio candidate: the values
criterion applied to the three value identities. -/
theorem ratioCanonicalSheafCandidate_differential_of_eq
    (hmix : MixedCanonicalCandidateNormalization k)
    (hω : IsInvertible (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n))
    (R : (pushforward (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)))).obj
        (exteriorCotangentSheaf
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)) ≫ (U.2.fromSpec ≫ f)) n) ⟶
      exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)
    (hR : ratioCanonicalSheafCandidate F n L m σ hL hD y U v c j₀ w f het hcinj hm htame = R) :
    letI : Module.Free Γ(X, U.1) Bᵣ := VaryingFinite.free (Joined.degree F n m)
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
    letI : Module.Finite Γ(X, U.1) Bᵣ := VaryingFinite.finite (Joined.degree F n m)
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
    (pushforward (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ)))).map
        (exteriorCotangentSheafPullbackMap (U.2.fromSpec ≫ f)
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))) n) ≫ R =
      affinePulledLineTrace Γ(X, U.1) (.of Bᵣ) (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)
        hω := by
  have : (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n).IsQuasicoherent := hω.isQuasicoherent
  exact affinePushforward_comp_eq_of_values _ _ R _
    (ratioNativePullback F n L m σ hL hD y U v c j₀ w f) (Algebra.trace Γ(X, U.1) Bᵣ)
    (ratioCanonicalSheafCandidate_values_hD F n L m σ hL hD y U v c j₀ w f)
    (ratioCanonicalSheafCandidate_values_hT F n L m σ hL hD y U v c j₀ w f het hcinj hm htame
      hmix R hR)
    (ratioCanonicalSheafCandidate_values_hS F n L m σ hL hD y U v c j₀ w f hm hω)

/-- **Ratio-chart normalization.** Under the normalization of the mixed candidate, the pushed
canonical differential of the ratio chart `p : Spec B_r → Spec Γ(X, U)` followed by the ratio
canonical candidate is the affine pulled-line trace of `Ω^n_{U/k}` along `p`. -/
theorem ratioCanonicalSheafCandidate_differential
    (hmix : MixedCanonicalCandidateNormalization k)
    (hω : IsInvertible (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n)) :
    let _ := f.sectionsAlgebra U.1
    let _ : Module.Free Γ(X, U.1) Bᵣ := VaryingFinite.free (Joined.degree F n m)
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
    let _ : Module.Finite Γ(X, U.1) Bᵣ := VaryingFinite.finite (Joined.degree F n m)
      (ratioCoefficients F n L m σ hL hD y U v c j₀ w) (fun i => hm (Joined.row F n i))
    let p := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Bᵣ))
    (pushforward p).map (exteriorCotangentSheafPullbackMap (U.2.fromSpec ≫ f) p n) ≫
        ratioCanonicalSheafCandidate F n L m σ hL hD y U v c j₀ w f het hcinj hm htame =
      affinePulledLineTrace Γ(X, U.1) (.of Bᵣ)
        (exteriorCotangentSheaf (U.2.fromSpec ≫ f) n) hω := by
  dsimp only
  generalize hR :
    ratioCanonicalSheafCandidate F n L m σ hL hD y U v c j₀ w f het hcinj hm htame = R
  exact ratioCanonicalSheafCandidate_differential_of_eq F n L m σ hL hD y U v c j₀ w f het hcinj
    hm htame hmix hω R hR

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
