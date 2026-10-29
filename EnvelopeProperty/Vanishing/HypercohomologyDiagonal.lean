import EnvelopeProperty.Vanishing.HypercohomologyBrutalTail
import EnvelopeProperty.Vanishing.HypercohomologyExt

/-! # Bounded hypercohomology vanishes when its entire term diagonal vanishes

The proof constructs consecutive brutal-tail short exact sequences and uses
the exact Hom sequence of their genuine distinguished triangles.  No spectral
sequence, filtration, vanishing-transfer or decomposition certificate is assumed.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section
universe u v w w'

namespace EnvelopeProperty.Vanishing.HypercohomologyDiagonal

open HypercohomologyBrutalTail

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

/-- Exactness of the genuine derived triangle of consecutive brutal tails
propagates zero from the higher tail and its actual original cutoff term. -/
theorem subsingleton_hom_tail_step (K : CochainComplex C ℤ) (S : DerivedCategory C)
    (a : ℤ) (hnext : Subsingleton (S ⟶ DerivedCategory.Q.obj (tail K (a + 1))))
    (hterm : Subsingleton
      (S ⟶ (DerivedCategory.singleFunctor C a).obj (K.X a))) :
    Subsingleton (S ⟶ DerivedCategory.Q.obj (tail K a)) := by
  let hSES := sequence_shortExact K a
  let T := DerivedCategory.triangleOfSES hSES
  have hT := DerivedCategory.triangleOfSES_distinguished hSES
  let : Subsingleton (S ⟶ T.obj₁) := hnext
  let : Subsingleton (S ⟶ T.obj₃) := hterm
  have hz (f : S ⟶ DerivedCategory.Q.obj (tail K a)) : f = 0 := by
    have hf : f ≫ T.mor₂ = 0 := Subsingleton.elim _ _
    obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f hf
    rw [hg, Subsingleton.elim g 0, zero_comp]
    rfl
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

/-- A bounded actual brutal tail has zero derived Hom when every original
term on its whole diagonal does.  The bound is on the actual complex terms. -/
theorem subsingleton_hom_tail (K : CochainComplex C ℤ) (S : DerivedCategory C)
    (a : ℤ) (N : ℕ)
    (hupper : ∀ i : ℤ, a + N ≤ i → IsZero (K.X i))
    (hterms : ∀ k : Fin N, Subsingleton
      (S ⟶ (DerivedCategory.singleFunctor C (a + k.val)).obj (K.X (a + k.val)))) :
    Subsingleton (S ⟶ DerivedCategory.Q.obj (tail K a)) := by
  induction N generalizing a with
  | zero =>
    have hzero : IsZero (tail K a) :=
      isZero_tail K a (fun i hi => hupper i (by simpa using hi))
    have hQ : IsZero (DerivedCategory.Q.obj (tail K a)) :=
      DerivedCategory.Q.map_isZero hzero
    exact ⟨fun f g => hQ.eq_of_tgt f g⟩
  | succ N ih =>
    have hnext : Subsingleton (S ⟶ DerivedCategory.Q.obj (tail K (a + 1))) := by
      apply ih (a + 1)
      · intro i hi
        exact hupper i (by omega)
      · intro k
        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using
          hterms ⟨k.val + 1, by omega⟩
    have hterm : Subsingleton
        (S ⟶ (DerivedCategory.singleFunctor C a).obj (K.X a)) := by
      simpa using hterms ⟨0, Nat.zero_lt_succ N⟩
    exact subsingleton_hom_tail_step K S a hnext hterm

/-- The original bounded complex itself has zero derived Hom when each
actual term has zero single-term derived Hom in the corresponding degree. -/
theorem subsingleton_hom_of_bounded_terms (K : CochainComplex C ℤ)
    (S : DerivedCategory C) (a : ℤ) (N : ℕ)
    (hlower : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hupper : ∀ i : ℤ, a + N ≤ i → IsZero (K.X i))
    (hterms : ∀ k : Fin N, Subsingleton
      (S ⟶ (DerivedCategory.singleFunctor C (a + k.val)).obj (K.X (a + k.val)))) :
    Subsingleton (S ⟶ DerivedCategory.Q.obj K) := by
  let := subsingleton_hom_tail K S a N hupper hterms
  let e := DerivedCategory.Q.mapIso (inclusionIso K a hlower)
  exact e.symm.homToEquiv.injective.subsingleton

section Sheaves

variable {T : Type u} [TopologicalSpace T]
  [HasSheafify (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})]
  [HasDerivedCategory.{w'}
    (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})]

open HypercohomologyExt

/-- Native sheaf cohomology on the whole diagonal annihilates the actual
derived Hom from the constant sheaf placed in the original total degree. -/
theorem subsingleton_single_hypercohomology_of_H
    (K : CochainComplex
      (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}) ℤ)
    (a : ℤ) (N : ℕ) (t : ℤ)
    (hlower : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hupper : ∀ i : ℤ, a + N ≤ i → IsZero (K.X i))
    (ht : a + N ≤ t + 1)
    (hdiag : ∀ i : Fin N,
      Subsingleton (CategoryTheory.Sheaf.H (K.X (a + i.val))
        (t - (a + i.val)).toNat)) :
    Subsingleton
      ((DerivedCategory.singleFunctor _ t).obj (constantIntegerSheaf (T := T)) ⟶
        DerivedCategory.Q.obj K) := by
  have hterms (i : Fin N) : Subsingleton
      ((DerivedCategory.singleFunctor _ t).obj (constantIntegerSheaf (T := T)) ⟶
        (DerivedCategory.singleFunctor _ (a + i.val)).obj (K.X (a + i.val))) :=
    subsingleton_singleHom_of_H (K.X (a + i.val)) (a + i.val) t
      (t - (a + i.val)).toNat (by have := i.isLt; omega) (hdiag i)
  exact subsingleton_hom_of_bounded_terms K
    ((DerivedCategory.singleFunctor _ t).obj (constantIntegerSheaf (T := T)))
    a N hlower hupper hterms

/-- The positive Hodge diagonal of an actual complex supported in degrees
zero through n annihilates its actual total-degree-t hypercohomology. -/
theorem subsingleton_single_hypercohomology_of_upper_diagonal
    (K : CochainComplex
      (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}) ℤ)
    (n t : ℕ) (ht : n < t)
    (hlower : ∀ i : ℤ, i < 0 → IsZero (K.X i))
    (hupper : ∀ i : ℤ, (n : ℤ) < i → IsZero (K.X i))
    (hdiag : ∀ i : Fin (n + 1), Subsingleton
      (CategoryTheory.Sheaf.H (K.X (i.val : ℤ)) (t - i.val))) :
    Subsingleton
      ((DerivedCategory.singleFunctor _ (t : ℤ)).obj
        (constantIntegerSheaf (T := T)) ⟶ DerivedCategory.Q.obj K) := by
  apply subsingleton_single_hypercohomology_of_H K 0 (n + 1) t hlower
  · intro i hi
    exact hupper i (by omega)
  · omega
  · intro i
    have hi := i.isLt
    have he : ((t : ℤ) - (i.val : ℤ)).toNat = t - i.val := by omega
    simpa only [zero_add, he] using hdiag i

/-- The same actual vanishing in the usual presentation with the constant
sheaf in degree zero and a shift of the original complex. -/
theorem subsingleton_hypercohomology_of_H
    (K : CochainComplex
      (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}) ℤ)
    (a : ℤ) (N : ℕ) (t : ℤ)
    (hlower : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hupper : ∀ i : ℤ, a + N ≤ i → IsZero (K.X i))
    (ht : a + N ≤ t + 1)
    (hdiag : ∀ i : Fin N,
      Subsingleton (CategoryTheory.Sheaf.H (K.X (a + i.val))
        (t - (a + i.val)).toNat)) :
    Subsingleton
      ((DerivedCategory.singleFunctor _ 0).obj (constantIntegerSheaf (T := T)) ⟶
        (DerivedCategory.Q.obj K)⟦t⟧) := by
  let := subsingleton_single_hypercohomology_of_H K a N t hlower hupper ht hdiag
  let eA :
      ((DerivedCategory.singleFunctor _ t).obj (constantIntegerSheaf (T := T)))⟦t⟧ ≅
        (DerivedCategory.singleFunctor _ 0).obj (constantIntegerSheaf (T := T)) :=
    ((DerivedCategory.singleFunctors _).shiftIso t 0 t (by simp)).app _
  let e :
      ((DerivedCategory.singleFunctor _ t).obj (constantIntegerSheaf (T := T)) ⟶
        DerivedCategory.Q.obj K) ≃
      ((DerivedCategory.singleFunctor _ 0).obj (constantIntegerSheaf (T := T)) ⟶
        (DerivedCategory.Q.obj K)⟦t⟧) :=
    (Functor.FullyFaithful.ofFullyFaithful
      (shiftFunctor (DerivedCategory
        (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})) t)).homEquiv.trans
    eA.homFromEquiv
  exact e.symm.injective.subsingleton

end Sheaves

end EnvelopeProperty.Vanishing.HypercohomologyDiagonal
