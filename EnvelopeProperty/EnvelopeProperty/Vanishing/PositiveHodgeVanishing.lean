import EnvelopeProperty.Vanishing.HodgeSerreVanishing
import EnvelopeProperty.Vanishing.CartierConnectionPower
import EnvelopeProperty.Vanishing.FrobeniusCohomologyHodge
import EnvelopeProperty.Vanishing.HypercohomologyDiagonal

/-! # Positive Hodge vanishing from an explicit actual Deligne--Illusie decomposition

The only imported mathematical input is the actual derived decomposition.
The amplification step uses actual connection terms, affine pushforward,
bounded hypercohomology, source summands and the field-Frobenius comparison.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section
universe u w w'

namespace EnvelopeProperty.Vanishing.PositiveHodgeVanishing

open Cartier CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem subsingleton_H_of_iso {T : Type u} [TopologicalSpace T]
    {M N : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}}
    (e : M ≅ N) (q : ℕ)
    (hN : Subsingleton (CategoryTheory.Sheaf.H N q)) :
    Subsingleton (CategoryTheory.Sheaf.H M q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology T) q).mapIso e
  let : Subsingleton ((CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology T) q).obj N) := hN
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (n : ℕ) [SmoothOfRelativeDimension n f]

variable [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p f).Modules]
    [HasDerivedCategory.{w'} (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))]

/-- The actual one-step geometric descent.  Unlike the elementary iteration
criterion, its only imported mathematical premise is the DI decomposition. -/
theorem diagonal_descent (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L)
    (hDI : DeligneIllusieInput.Decomposition f p n) (t : ℕ) (ht : n < t)
    (m : ℕ)
    (hnext : ∀ i : Fin (n + 1), Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower L (p * m) ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
        (t - i.val))) :
    ∀ i : Fin (n + 1), Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
        (t - i.val)) := by
  let K := CartierConnectionPower.sheafComplex f p n L hL.isInvertible m
  let A := (DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))
    (t : ℤ)).obj (HypercohomologyExt.constantIntegerSheaf (T := SchemeRelativeFrobenius.twist p f))
  have hdiag (i : Fin (n + 1)) :
      Subsingleton (CategoryTheory.Sheaf.H (K.X (i.val : ℤ)) (t - i.val)) := by
    let W := exteriorCotangentSheaf f i.val
    let B := bundleTensorPower L (p * m)
    let M : X.Modules := B ⊗ W
    let : W.IsQuasicoherent := SmoothExteriorFiniteType.isQuasicoherent f n i.val
    have hB : Scheme.Modules.IsInvertible B :=
      TensorPowerBaseIdealGrading.tensorPower_isInvertible hL.isInvertible (p * m)
    let : (W ⊗ B).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight W B hB
    let : M.IsQuasicoherent :=
      (Scheme.Modules.isQuasicoherent X).prop_of_iso (β_ W B) inferInstance
    have hi := i.isLt
    have he : t - i.val = (t - i.val - 1) + 1 := by omega
    have hpush : Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pushforward (SchemeRelativeFrobenius.map p f)).obj M).sheaf
          (t - i.val)) := by
      rw [he]
      apply (FrobeniusCohomology.relativePushforward_subsingleton_H_iff f p
        hL.isProjectiveFactorization M (t - i.val - 1)).mpr
      have hc : Subsingleton (CategoryTheory.Sheaf.H M.sheaf (t - i.val)) := hnext i
      exact he ▸ hc
    exact subsingleton_H_of_iso
      (CartierConnectionPower.sheafTermIso f p n L hL.isInvertible m i.val)
      (t - i.val) hpush
  let : HasDerivedCategory.{w'} (CategoryTheory.Sheaf
      (_root_.Opens.grothendieckTopology (SchemeRelativeFrobenius.twist p f))
      AddCommGrpCat.{u}) := by
    change HasDerivedCategory.{w'}
      (TopCat.Sheaf AddCommGrpCat.{u} (SchemeRelativeFrobenius.twist p f))
    infer_instance
  have htotal : Subsingleton (A ⟶ DerivedCategory.Q.obj K) :=
    HypercohomologyDiagonal.subsingleton_single_hypercohomology_of_upper_diagonal
      K n t ht
      (CartierConnectionPower.sheafComplex_X_isZero_below f p n L hL.isInvertible m)
      (CartierConnectionPower.sheafComplex_X_isZero_above f p n L hL.isInvertible m) hdiag
  let e := CartierConnectionPower.decompositionIso f p n L hL.isInvertible m hDI
  have hsource : Subsingleton (A ⟶
      CartierConnectionPower.realizedSource f p n L hL.isInvertible m) := by
    let := htotal
    exact ⟨fun a b => (cancel_mono e.hom).mp (Subsingleton.elim _ _)⟩
  intro i
  let Lm := CartierConnectionPower.twistLinePower f p L m
  let Oi := exteriorCotangentSheaf (DeligneIllusieInput.twistStructure f p) i.val
  have hi := i.isLt
  have he : (i.val : ℤ) + (t - i.val : ℕ) = (t : ℤ) := by omega
  have htwisted : Subsingleton (CategoryTheory.Sheaf.H (Oi ⊗ Lm).sheaf (t - i.val)) :=
    CartierConnectionPower.source_hodge_H f p n L hL.isInvertible m i
      (t : ℤ) (t - i.val) he hsource
  have hswapped : Subsingleton (CategoryTheory.Sheaf.H (Lm ⊗ Oi).sheaf (t - i.val)) :=
    subsingleton_H_of_iso ((Scheme.Modules.toSheaf (SchemeRelativeFrobenius.twist p f)).mapIso (β_ Lm Oi))
      (t - i.val) htwisted
  have hdegree : t - i.val = (t - i.val - 1) + 1 := by omega
  rw [hdegree] at hswapped ⊢
  exact (FrobeniusCohomologyHodge.twistHodge_subsingleton_H_iff f p n L hL
    m i.val (t - i.val - 1)).mp hswapped

/-- Every positive original ample power has vanishing actual Hodge groups
above the dimension diagonal, conditional only on the actual DI decomposition. -/
theorem upper_diagonal (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L)
    (hDI : DeligneIllusieInput.Decomposition f p n) (t : ℕ) (ht : n < t)
    {m : ℕ} (hm : 0 < m) (i : Fin (n + 1)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i.val : X.Modules).sheaf
        (t - i.val)) :=
  HodgeSerreVanishing.upper_diagonal_of_descent f n L hL
    (Fact.out : p.Prime).two_le t ht
    (fun m _ => diagonal_descent f p n L hL hDI t ht m) hm i

/-- The top exterior sheaf gives the Kodaira cohomology degrees at every
positive ample power. Characteristic-zero specialization is a separate step. -/
theorem top_degree (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L)
    (hDI : DeligneIllusieInput.Decomposition f p n) {m : ℕ} (hm : 0 < m) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower L m ⊗ exteriorCotangentSheaf f n : X.Modules).sheaf (q + 1)) := by
  have h := upper_diagonal f p n L hL hDI (n + q + 1) (by omega) hm (Fin.last n)
  have he : n + q + 1 - n = q + 1 := by omega
  simpa only [Fin.val_last, he] using h

/-- The usual Kodaira tensor order and the original first ample power,
still with the actual derived decomposition as the only imported theorem. -/
theorem kodaira_of_decomposition (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L)
    (hDI : DeligneIllusieInput.Decomposition f p n) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (exteriorCotangentSheaf f n ⊗ L : X.Modules).sheaf (q + 1)) := by
  let W := exteriorCotangentSheaf f n
  let e : W ⊗ L ≅ bundleTensorPower L 1 ⊗ W :=
    (β_ W L) ≪≫ ((bundleTensorLeftUnitIso L).symm ⊗ᵢ Iso.refl W)
  exact subsingleton_H_of_iso ((Scheme.Modules.toSheaf X).mapIso e) (q + 1)
    (top_degree f p n L hL hDI Nat.zero_lt_one q)

/-- The actual Witt model and the actual dimension bound supply precisely
the explicit temporary DI input used by the proved Kodaira deduction. -/
theorem kodaira_of_wittLift (hDI : DeligneIllusieInput.WittDecompositionInput.{u,w} p k)
    {Xlift : Scheme.{u}} (fLift : Xlift ⟶ Spec (.of (DeligneIllusie.WittTwo.Ring p k)))
    (n : ℕ) [SmoothOfRelativeDimension n fLift] [IsSeparated fLift]
    [HasDerivedCategory.{w} (SchemeRelativeFrobenius.twist p
      (DeligneIllusieInput.specialFibreStructure p k fLift)).Modules]
    [HasDerivedCategory.{w'} (TopCat.Sheaf AddCommGrpCat.{u}
      (SchemeRelativeFrobenius.twist p
        (DeligneIllusieInput.specialFibreStructure p k fLift)))]
    (hn : n < p) (L : (DeligneIllusieInput.specialFibre p k fLift).Modules)
    (hL : SchemeLineAmpleness.IsAmple
      (DeligneIllusieInput.specialFibreStructure p k fLift) L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (exteriorCotangentSheaf (DeligneIllusieInput.specialFibreStructure p k fLift) n ⊗ L :
        (DeligneIllusieInput.specialFibre p k fLift).Modules).sheaf (q + 1)) := by
  let := DeligneIllusieInput.specialFibre_smoothOfRelativeDimension p k fLift n
  exact kodaira_of_decomposition (DeligneIllusieInput.specialFibreStructure p k fLift)
    p n L hL (DeligneIllusieInput.ofWittLift p k hDI fLift n hn) q

end EnvelopeProperty.Vanishing.PositiveHodgeVanishing
