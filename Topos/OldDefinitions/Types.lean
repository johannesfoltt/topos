import Topos.Basic
import Mathlib.Order.Basic
import Mathlib.CategoryTheory.Sites.Types
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.CategoryTheory.Monoidal.Types.Basic

namespace CategoryTheory

open CategoryTheory Category Topos Opposite Limits Classifier Types Classical

namespace Topos

universe u

#check ChosenFiniteProducts
#synth HasTerminal (Type u)
#synth HasPullbacks (Type u)
#synth HasProducts (Type u)
#synth Category (Type u)

#check Classical.byCases

#check PUnit.{u}
#check ⊤_ (Type u)

noncomputable section

variable {A B : Type u}
variable {p : Prop} (C : Type u)

-- "the" subobject classifier for `Type u`
inductive Ω : Type u where
| T
| F

abbrev T := Ω.T
abbrev F := Ω.F

lemma Ω.em (z : Ω) : z = T ∨ z = F := by
  cases z with
  | T => left; rfl
  | F => right; rfl

abbrev true_ : ⊤_ (Type u) ⟶ Ω := fun _ => T

abbrev false_ : ⊤_ (Type u) ⟶ Ω := fun _ => F

abbrev char (f : A ⟶ B) [Mono f] : B ⟶ Ω :=
  fun b => if (∃ a : A, f a = b) then T else F

variable (f : A ⟶ B) [mono : Mono f]

lemma f_inj : Function.Injective f := (mono_iff_injective f).mp mono

lemma char_true (b : B) (h : ∃ a : A, f a = b) : char f b = T := by
  simp; assumption

lemma char_true_iff (b : B) : (∃ a : A, f a = b) ↔ char f b = T := by simp

lemma char_true_iff_uniq (b : B) : (∃! a : A, f a = b) ↔ char f b = T := by
  simp
  apply Iff.intro
  · exact fun ⟨a, h₁, _⟩ => ⟨a, h₁⟩
  · exact fun ⟨a, h⟩ =>
    ⟨a, h, fun _ h₁ => ((mono_iff_injective f).mp mono) (h₁.trans h.symm)⟩

def charCommSq : CommSq f (terminal.from A) (char f) true_ where
  w := by funext a; simp

def pullbackCone : PullbackCone (char f) true_ :=
  PullbackCone.mk f (terminal.from A) (charCommSq f).w

variable {f}

def lift {X : Type u} (g : X ⟶ B) (hg : g ≫ char f = terminal.from X ≫ true_) :
    X ⟶ A :=
  fun x => ((char_true_iff f (g x)).mpr
  (by show char f (g x) = T; rw [←types_comp_apply g (char f), hg, types_comp_apply])).choose

lemma lift_fac {X : Type u} (g : X ⟶ B) (hg : g ≫ char f = terminal.from X ≫ true_) :
    lift g hg ≫ f = g := by
  funext x
  exact ((char_true_iff f (g x)).mpr
  (by show char f (g x) = T; rw [←types_comp_apply g (char f), hg, types_comp_apply])).choose_spec

instance typesLimit : IsLimit (pullbackCone f) where
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
      simp [pullbackCone]
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
        have ha : (PullbackCone.snd s) = terminal.from s.pt :=
          terminal.hom_ext (PullbackCone.snd s) (terminal.from s.pt)
        have hb : (pullbackCone f).snd = terminal.from A :=
          terminal.hom_ext (pullbackCone f).snd (terminal.from A)
        rw [ha, hb]
        apply terminal.comp_from
  uniq := by
    intro s j hj
    funext x
    have h' : (char f) ((PullbackCone.fst s) x) = T := by
      change (PullbackCone.fst s ≫ (char f)) x = T
      rw [PullbackCone.condition s, types_comp_apply]
    apply f_inj f
    have hj' := hj (some WalkingPair.left)
    simp [pullbackCone] at hj'
    rw [←types_comp_apply j f, hj']
    exact ((char_true_iff f (PullbackCone.fst s x)).mpr h').choose_spec.symm


def isPullback (f : A ⟶ B) [Mono f] : IsPullback f (terminal.from _) (char f) true_ where
  w := (charCommSq f).w
  isLimit' := Nonempty.intro typesLimit

def classifier : Classifier (Type u) where
  t := true_
  char := char
  isPullback := isPullback
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
      have hA' : f' ≫ χ = terminal.from A' ≫ true_ := by
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

instance typesHasClassifier : HasClassifier (Type u) where
  exists_classifier := ⟨classifier⟩

variable (B)

-- needs to use "a" subobject classifier. can't use just `Ω`
def pow : Type u := (B ⟶ HasClassifier.Ω _)

def in_ : B × (pow B) ⟶ HasClassifier.Ω _ :=
  fun (b, f) => f b

--def powerObject : Power.PowerObject B where
--  pow := pow B
--  in_ := in_ B

instance typeIsTopos : IsTopos (Type u) where
  has_power_objects := sorry

end
end CategoryTheory.Topos
