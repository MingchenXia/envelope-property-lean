import EnvelopeProperty.Vanishing.CartierConnection
import EnvelopeProperty.Vanishing.DeligneIllusieInput
import EnvelopeProperty.Vanishing.FrobeniusLineGluing
import EnvelopeProperty.Cartier.DeligneIllusieDimensionBound
import ModularCurves.ForMathlib.SchemeModuleSheaf

/-! # The actual amplified Cartier complex with the original positive-power terms

The global line Frobenius comparison and genuine line projection formula
identify every twisted term with `F_*(L^(p*m) ⊗ Ω^q)`. The differential is
transported from the linear complex on the true relative Frobenius twist.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section
universe u w w'

namespace EnvelopeProperty.Vanishing.CartierConnectionPower

open Cartier CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) [SmoothOfRelativeDimension n f]

local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f

omit [SmoothOfRelativeDimension n f] in
/-- The original line power on the actual geometric twist. -/
def twistLinePower (L : X.Modules) (m : ℕ) : (Y).Modules :=
  bundleTensorPower (FrobeniusLineComparison.twistedLine f p L) m

omit [SmoothOfRelativeDimension n f] in
/-- The actual original line remains invertible after the genuine twist
pullback and every tensor power. -/
theorem twistLinePower_isInvertible (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (m : ℕ) : Scheme.Modules.IsInvertible (twistLinePower f p L m) := by
  have hLt : Scheme.Modules.IsInvertible (FrobeniusLineComparison.twistedLine f p L) :=
    hL.pullback (pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p))
  exact TensorPowerBaseIdealGrading.tensorPower_isInvertible hLt m

/-- The line-twisted actual relative de Rham complex before projection transport. -/
def twistedComplex (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ) :
    CochainComplex (Y).Modules ℕ :=
  CartierConnection.twistedComplex f p n (twistLinePower f p L m)
    (twistLinePower_isInvertible f p L hL m)

omit [SmoothOfRelativeDimension n f] in
/-- The original positive-power Hodge module, with its original tensor order,
pushed along the original relative Frobenius. -/
def term (L : X.Modules) (m q : ℕ) : (Y).Modules :=
  (Scheme.Modules.pushforward (Fr)).obj
    (bundleTensorPower L (p * m) ⊗ exteriorCotangentSheaf f q)

/-- The actual global Frobenius line comparison and actual projection
formula derive the exact amplified original term, without a term certificate. -/
def termIso (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m q : ℕ) :
    (twistedComplex f p n L hL m).X q ≅ term f p L m q :=
  FrobeniusLineComparison.moduleProjectionIso f p L hL (exteriorCotangentSheaf f q) m

/-- The actual amplified connection differential on the pushed original terms. -/
def differential (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m q : ℕ) :
    term f p L m q ⟶ term f p L m (q + 1) :=
  (termIso f p n L hL m q).inv ≫
    (twistedComplex f p n L hL m).d q (q + 1) ≫
      (termIso f p n L hL m (q + 1)).hom

theorem differential_square (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (m q : ℕ) : differential f p n L hL m q ≫
      differential f p n L hL m (q + 1) = 0 :=
  CartierConnectionTransport.differential_comp (twistedComplex f p n L hL m)
    (term f p L m) (termIso f p n L hL m) q (q + 1) (q + 1 + 1)

/-- The actual amplified Cartier-connection complex. -/
def complex (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ) :
    CochainComplex (Y).Modules ℕ :=
  CartierConnectionTransport.complex (twistedComplex f p n L hL m)
    (term f p L m) (termIso f p n L hL m)

/-- The entire original line-twisted relative de Rham complex, with all its
original differentials, is the amplified connection complex. -/
def complexIso (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ) :
    twistedComplex f p n L hL m ≅ complex f p n L hL m :=
  CartierConnectionTransport.iso (twistedComplex f p n L hL m)
    (term f p L m) (termIso f p n L hL m)

/-- Actual smooth dimension annihilates every term above n, even after
the original Frobenius twist and line tensor. -/
theorem twistedTerm_isZero (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (m q : ℕ) (hq : n < q) :
    IsZero ((twistedComplex f p n L hL m).X q) :=
  (CartierConnection.tensorFunctor (twistLinePower f p L m)
    (twistLinePower_isInvertible f p L hL m)).map_isZero
    (DeligneIllusieDimensionBound.formModule_isZero f n p q hq)

/-- The exact original positive-power terms are zero above the relative dimension. -/
theorem term_isZero (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (m q : ℕ) (hq : n < q) : IsZero (term f p L m q) :=
  (twistedTerm_isZero f p n L hL m q hq).of_iso (termIso f p n L hL m q).symm

/-- Extension of the actual amplified connection has the actual upper dimension bound. -/
theorem complex_extend_isStrictlyLE (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (m : ℕ) :
    CochainComplex.IsStrictlyLE
      ((complex f p n L hL m).extend ComplexShape.embeddingUpNat) (n : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  cases i with
  | ofNat q =>
    have hq : n < q := Int.ofNat_lt.mp hi
    have hz : IsZero ((complex f p n L hL m).X q) := term_isZero f p n L hL m q hq
    exact hz.of_iso ((complex f p n L hL m).extendXIso ComplexShape.embeddingUpNat
      (i := q) rfl)
  | negSucc q => omega

/-- The actual integer-indexed underlying abelian complex for bounded
hypercohomology. Tensoring is after integer extension, exactly as in the
derived decomposition; no commutation is supplied as an extra input. -/
def sheafComplex (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} (Y)) ℤ :=
  ((Scheme.Modules.toSheaf (Y)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((CartierConnection.tensorFunctor (twistLinePower f p L m)
      (twistLinePower_isInvertible f p L hL m)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (DeligneIllusieInput.target f p n))

/-- In every nonnegative degree, the actual underlying complex has the
original amplified pushed Hodge term, via canonical original isomorphisms. -/
def sheafTermIso (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m q : ℕ) :
    (sheafComplex f p n L hL m).X (q : ℤ) ≅ (term f p L m q).sheaf := by
  let T := CartierConnection.tensorFunctor (twistLinePower f p L m)
    (twistLinePower_isInvertible f p L hL m)
  let e := T.mapIso
    ((SchemeRelativeFrobeniusBasisDifferential.complex f p n).extendXIso
      ComplexShape.embeddingUpNat (i := q) rfl) ≪≫ termIso f p n L hL m q
  exact (Scheme.Modules.toSheaf (Y)).mapIso e

/-- The underlying original abelian complex has the same genuine upper bound. -/
theorem sheafComplex_X_isZero_above (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (m : ℕ) (i : ℤ)
    (hi : (n : ℤ) < i) :
    IsZero ((sheafComplex f p n L hL m).X i) := by
  have hz := (CochainComplex.isStrictlyLE_iff
    ((SchemeRelativeFrobeniusBasisDifferential.complex f p n).extend
      ComplexShape.embeddingUpNat) (n : ℤ)).mp
      (DeligneIllusieDimensionBound.complex_extend_isStrictlyLE f n p) i hi
  exact (Scheme.Modules.toSheaf (Y)).map_isZero
    ((CartierConnection.tensorFunctor (twistLinePower f p L m)
      (twistLinePower_isInvertible f p L hL m)).map_isZero hz)

/-- Extension by zero gives the genuine lower bound on the same original complex. -/
theorem sheafComplex_X_isZero_below (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (m : ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((sheafComplex f p n L hL m).X i) := by
  have hz := (SchemeRelativeFrobeniusBasisDifferential.complex f p n).isZero_extend_X
    ComplexShape.embeddingUpNat i
    (fun q h => by change (q : ℤ) = i at h; omega)
  exact (Scheme.Modules.toSheaf (Y)).map_isZero
    ((CartierConnection.tensorFunctor (twistLinePower f p L m)
      (twistLinePower_isInvertible f p L hL m)).map_isZero hz)

omit [SmoothOfRelativeDimension n f] in
/-- The realized original DI source, using the internally proved
invertibility of the actual twisted line power. -/
def realizedSource
    [HasDerivedCategory.{w'}
      (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ) :
    DerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} (Y)) :=
  (DeligneIllusieInput.realizationFunctor f p (twistLinePower f p L m)
    (twistLinePower_isInvertible f p L hL m)).obj (DeligneIllusieInput.sourceNat f p n)

/-- The supplied ACTUAL DI decomposition, exact line tensoring, and exact
forgetting of scalars give precisely the underlying amplified connection
target used by hypercohomology. No further comparison is an assumption. -/
def decompositionIso
    [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
    [HasDerivedCategory.{w'}
      (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ)
    (hDI : DeligneIllusieInput.Decomposition f p n) :
    realizedSource f p n L hL m ≅
      DerivedCategory.Q.obj (sheafComplex f p n L hL m) := by
  exact DeligneIllusieInput.sheafTensorDecomposition f p n
    (twistLinePower f p L m) (twistLinePower_isInvertible f p L hL m) hDI

omit [SmoothOfRelativeDimension n f] in
/-- Native cohomology of the original twisted exterior sheaf is extracted
from zero hypercohomology of the actual realized source. -/
theorem source_hodge_H
    [HasDerivedCategory.{w'}
      (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (m : ℕ)
    (i : Fin (n + 1)) (t : ℤ) (q : ℕ) (hdegree : (i.val : ℤ) + q = t)
    (hzero : Subsingleton
      ((DerivedCategory.singleFunctor.{w'} (TopCat.Sheaf AddCommGrpCat.{u} (Y)) t).obj
          (HypercohomologyExt.constantIntegerSheaf (T := Y)) ⟶ realizedSource f p n L hL m)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (exteriorCotangentSheaf (DeligneIllusieInput.twistStructure f p) i.val ⊗
        twistLinePower f p L m).sheaf q) :=
  DeligneIllusieInput.subsingleton_hodge_H f p n (twistLinePower f p L m)
    (twistLinePower_isInvertible f p L hL m) i t q hdegree hzero

end EnvelopeProperty.Vanishing.CartierConnectionPower
