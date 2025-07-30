import Mathlib.CategoryTheory.Closed.Types
import Topos.NewDefinitions.NewTopos


namespace CategoryTheory

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Classical Types Classifier Classifier PowerObject ChosenPowerObjects

universe u

noncomputable section

namespace Types

inductive Ω : Type u where
| T
| F

abbrev T := Ω.T
abbrev F := Ω.F

lemma Ω.em (z : Ω) : z = T ∨ z = F := by
  cases z with
  | T => left; rfl
  | F => right; rfl

abbrev true_ : 𝟙_ (Type u) ⟶ Ω := fun _ => T

abbrev false_ : 𝟙_ (Type u) ⟶ Ω := fun _ => F

abbrev char {A B : Type u} (f : A ⟶ B) [Mono f] : B ⟶ Ω :=
  fun b => if (∃ a : A, f a = b) then T else F

variable {A B : Type u} (f : A ⟶ B) [Mono f]

--lemma f_inj : Function.Injective f := by (expose_names; exact (mono_iff_injective f).mp inst)

lemma char_true (b : B) (h : ∃ a : A, f a = b) : char f b = T := by
  simp; assumption

lemma char_true_iff (b : B) : (∃ a : A, f a = b) ↔ char f b = T := by simp

lemma char_true_iff_uniq (b : B) : (∃! a : A, f a = b) ↔ char f b = T := by
  simp
  apply Iff.intro
  · exact fun ⟨a, h₁, _⟩ => ⟨a, h₁⟩
  · expose_names
    exact fun ⟨a, h⟩ =>
    ⟨a, h, fun _ h₁ => ((mono_iff_injective f).mp inst) (h₁.trans h.symm)⟩

def charCommSq : CommSq f (toUnit A) (char f) true_ where
  w := by funext a; simp

def charPullbackCone : PullbackCone (char f) true_ :=
  PullbackCone.mk f (toUnit A) (charCommSq f).w

variable {f}


instance charPullbackLimit : IsLimit (charPullbackCone f) where
  lift := by
    intro s
    intro x
    have h' : (char f) ((PullbackCone.fst s) x) = T := by
      change (PullbackCone.fst s ≫ (char f)) x = T
      rw [PullbackCone.condition s, types_comp_apply]
    exact ((char_true_iff f (PullbackCone.fst s x)).mpr h').choose
  fac := by
    intro s j
    cases j with
    | none =>
      simp [charPullbackCone]
      funext x
      rw [(charCommSq f).w]
      simp [true_, PullbackCone.condition s]
      rw [←types_comp_apply (PullbackCone.fst s) (char f) x, (PullbackCone.condition s)]
      simp
    | some val =>
      cases val
      · simp
        funext x
        have h' : (char f) ((PullbackCone.fst s) x) = T := by
          change (PullbackCone.fst s ≫ (char f)) x = T
          rw [PullbackCone.condition s, types_comp_apply]

        exact ((char_true_iff f (PullbackCone.fst s x)).mpr h').choose_spec
      · simp
        rfl
  uniq := by
    intro s j hj
    funext x
    have h' : (char f) ((PullbackCone.fst s) x) = T := by
      change (PullbackCone.fst s ≫ (char f)) x = T
      rw [PullbackCone.condition s, types_comp_apply]
    expose_names
    apply (mono_iff_injective f).mp inst
    have hj' := hj (some WalkingPair.left)
    simp [charPullbackCone] at hj'
    rw [←types_comp_apply j f, hj']
    exact ((char_true_iff f (PullbackCone.fst s x)).mpr h').choose_spec.symm

def charPullback (f : A ⟶ B) [Mono f] : IsPullback f (toUnit _) (char f) true_ where
  w := (charCommSq f).w
  isLimit' := ⟨charPullbackLimit⟩

instance classifier : Classifier (Type u) where
  t_ := true_
  char := char
  isPullback := charPullback
  uniq := by
    intro A B f inst χ hχ
    funext x
    if h : (∃ a : A, f a = x) then
      simp [char, h]
      rw [h.choose_spec.symm, ←types_comp_apply f χ, hχ.w]
      simp
    else
      simp [char, h]
      by_contra h'
      have h'' : χ x = T := by
        cases (Ω.em (χ x)) with
        | inl _ => assumption
        | inr _ => contradiction
      have k := hχ.w
      let A' := {b : B // (∃ a : A, f a = b) ∨ b = x}
      let f' : A' ⟶ B := fun b => (b : B)
      have hA' : f' ≫ χ = toUnit A' ≫ true_ := by
        funext y
        simp [true_, f']
        cases y.property with
        | inl k' =>
          have r := congrArg χ k'.choose_spec
          rw [←types_comp_apply f χ k'.choose, k] at r
          simp [true_] at r
          exact r.symm
        | inr k' => rw [k']; assumption
      have lift := hχ.lift _ _ hA'
      have char_x : char f x = F := by
        dsimp [char]
        simp [h]
      have app : (hχ.lift _ _ hA' ≫ f ≫ char f) ⟨x, by simp⟩ = T := by simp
      have final : char f x = T := by
        rw [←assoc] at app
        rw [hχ.lift_fst _ _ hA', types_comp_apply] at app
        dsimp [f'] at app
        assumption
      have s : T = F := final.symm.trans char_x
      contradiction
