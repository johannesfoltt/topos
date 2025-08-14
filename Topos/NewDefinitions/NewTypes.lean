import Mathlib.CategoryTheory.Closed.Types
import Topos.NewDefinitions.NewTopos
import Topos.NewDefinitions.NewClassifierMeet


namespace CategoryTheory

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Classical Types Classifier Classifier PowerObject ChosenPowerObjects

universe u

namespace Types

abbrev true_ : 𝟙_ (Type u) ⟶ (ULift.{u} Prop) := fun _ => ULift.up True

abbrev char {A B : Type u} (f : A ⟶ B) : B ⟶ (ULift.{u} Prop) :=
  fun b => ULift.up (∃ a : A, f a = b)

lemma isPullback_condition {X : Type u} {χ : X ⟶ (ULift.{u} Prop)} : ∀ {U : Type u} (m : U ⟶ X) [Mono m], (IsPullback m (ChosenTerminalObject.from_ U) χ true_) ↔ (∀ (x : X), (χ x).down ↔ ∃ (u : U), m u = x) := by {
  intros U m mono
  apply Iff.intro
  · intros hpb x
    apply Iff.intro
    · intro h'
      rw [← Lean.Grind.eq_true_eq (χ x).down] at h'
      have comm : (fun _ => x : 𝟙_ (Type u) ⟶ X) ≫ χ = (𝟙 _) ≫ true_ := by {
        apply funext
        intro x'
        unfold true_
        rw [← h']
        simp
      }
      use (hpb.lift _ _ comm) PUnit.unit
      exact congrFun (hpb.lift_fst _ _ comm) _
    · intro h'
      apply Exists.elim h'
      intros u h''
      rw [← Lean.Grind.eq_true_eq (χ x).down, ← h'']
      change _ = (ULift.up True).down
      apply congrArg
      exact congrFun hpb.w _
  · intro h
    refine { toCommSq := {w := by aesop}, isLimit' := ⟨?_⟩}
    apply (PullbackCone.isLimitEquivBijective _).invFun
    apply And.intro
    · intros x y h'
      simp at x; simp at y
      unfold PullbackCone.toPullbackObj at h'; simp at h'
      exact ((mono_iff_injective m).mp mono) h'.1
    · rintro ⟨p, hp⟩
      unfold PullbackCone.toPullbackObj
      simp
      rw [ULift.ext_iff] at hp; simp at hp
      apply Exists.elim ((h p.1).1 hp)
      intros u hu
      use u
      rw [hu, PUnit.ext (toUnit U u) p.2, Prod.mk.eta]
}

instance instClassifier : Classifier (Type u) where
  t_ := true_
  char {U X : Type u} (m : U ⟶ X) [Mono m] := char m
  isPullback {U X : Type u} (m : U ⟶ X) [Mono m] := by {
    rw [isPullback_condition]
    aesop
  }
  uniq {U X : Type u} {m : U ⟶ X} [Mono m] {χ : X ⟶ (ULift.{u} Prop)} (h : IsPullback m (ChosenTerminalObject.from_ U) χ true_) := by {
    rw [isPullback_condition] at h
    aesop
  }


instance instPowerObjectType (X : Type u) : PowerObject X where
  pow := Set X
  in_ := fun x => ULift.up (x.1 ∈ x.2)
  transpose {Y : Type u} (f : X ⊗ Y ⟶ Ω) := fun y => {x | (f (x,y)).down}
  comm := by aesop
  uniq := by aesop

instance instChosenPowerObjectsType : ChosenPowerObjects (Type u) where
  powerObject := instPowerObjectType

instance instToposType : Topos (Type u) where
  cartesianMonoidal := typesCartesianMonoidalCategory
  hasPullbacks := instHasPullbacksType
  classifier := instClassifier
  cartesianClosed := instCartesianClosedType
  chosenPowerObjects := instChosenPowerObjectsType
