import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.NewDefinitions.NewClassifier
import Topos.HelpfulCategoryTheory.OverLimits

namespace CategoryTheory

open Category Limits Over MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier

universe u v

namespace Over

noncomputable section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C] [Classifier C] {X : C}

instance : CartesianMonoidalCategory (Over X) := cartesianMonoidalCategory X


omit [HasPullbacks C] in
lemma classifierOver.isPullback_left {S A : Over X} (m : S ⟶ A) [Mono m] : IsPullback m.left S.hom (lift (χ_ m.left) A.hom) (lift (Predicate.true_ X) (𝟙 X)) where
  w := by {
    rw [comp_lift, comp_lift]
    apply CartesianMonoidalCategory.hom_ext
    · simp
      unfold Predicate.true_
      rw [← assoc, comp_from, Classifier.comm]
    · simp
  }
  isLimit' := by {
    apply Nonempty.intro
    have comm (s : PullbackCone (lift (χ_ m.left) A.hom) (lift (Predicate.true_ X) (𝟙 X))) : s.fst ≫ (char m.left) = (s.snd ≫ from_ X) ≫ t_ := by {
      rw [assoc, ← Predicate.true_]
      have help := (CartesianMonoidalCategory.hom_ext_iff.1 s.condition).1
      simp at help
      assumption
    }
    apply PullbackCone.IsLimit.mk _ (fun s ↦ ((isPullback m.left).lift _ _ (comm s)))
    · intro s
      simp
    · intro s
      nth_rewrite 2 [← comp_id s.snd]
      convert_to  _ = s.snd ≫ (lift (Predicate.true_ X) (𝟙 X) ≫ snd Ω X)
      · exact congrArg (CategoryStruct.comp s.snd) (id (Eq.symm (lift_snd (Predicate.true_ X) (𝟙 X))))
      rw [← assoc, ← s.condition]
      simp
      rw [← Over.w m, ← assoc, (isPullback m.left).lift_fst s.fst (toUnit s.pt) _]
    · intros s l h_fst h_snd
      apply (isPullback m.left).hom_ext
      · aesop_cat
      · aesop_cat
  }



instance classifier : Classifier (Over X) where
  Ω := mk (snd Ω X)
  t_ := homMk (lift (Predicate.true_ X) (𝟙 X))
  char {S A : Over X} (m : S ⟶ A) [Mono m] := homMk (lift (χ_ m.left) (A.hom))
  isPullback {S A : Over X} (m : S ⟶ A) [Mono m] := by {
    apply isPullback_of_isPullback_left
    simp
    exact classifierOver.isPullback_left m
  }


variable {c} {m}

-- set_option trace.Meta.Tactic.simp true in
lemma Over.classifierOver.uniq_w {χ : S ⟶ (Ω c)} (s : PullbackCone (χ.left ≫ prod.fst) c.t) : (homMk s.fst : mk (s.fst ≫ S.hom) ⟶ S) ≫ χ = terminal.from _ ≫ t c := by {
  rw [OverMorphism.ext_iff, comp_left, ← assoc, @homMk_left]
  simp [-PullbackCone.π_app_left]
  -- Danke an Hannah in Bachelorarbeit
  refine Limits.prod.hom_ext ?_ ?_
  · rw [assoc, s.condition, prod.lift_fst, cancel_mono, terminal.hom_ext s.snd]
  · have h : (prod.snd : c.Ω ⨯ X ⟶ X) = (Ω c).hom := rfl
    rw [prod.lift_snd, assoc, h, w χ]
    unfold mkIdTerminal
    unfold CostructuredArrow.mkIdTerminal
    unfold IsTerminal.from
    unfold Functor.preimage
    simp [-PullbackCone.π_app_left]
}

variable (c) (m)

lemma Over.classifierOver.uniq (χ : S ⟶ (Ω c)) (hχ : IsPullback m (terminal.from U) χ (t c)) : χ = char c m := by {
  rw [OverMorphism.ext_iff]; simp
  refine Limits.prod.hom_ext ?_ ?_
  · simp
    have isPullback' : IsPullback m.left (terminal.from U.left) (χ.left ≫ prod.fst) (c.t) := {
      w := by {
        have help' := hχ.w
        rw [OverMorphism.ext_iff, comp_left, comp_left] at help'
        rw [← assoc, help']
        aesop_cat
      }
      isLimit' := by {
        apply Nonempty.intro
        apply PullbackCone.IsLimit.mk _ (fun s ↦ (hχ.lift _ _ (uniq_w s)).left)
        · intro s
          rw [← comp_left]
          simp [-PullbackCone.π_app_left]
        · intro s
          simp [-PullbackCone.π_app_left]
          exact terminal.hom_ext (terminal.from s.pt) s.snd
        · intro s m' h₁ h₂
          have w : m' ≫ U.hom = (mk (s.fst ≫ S.hom)).hom := by {
            rw [← w m, ← assoc, h₁]
            simp [-PullbackCone.π_app_left]
          }
          let m'' : mk (s.fst ≫ S.hom) ⟶ U := homMk m' w
          change m''.left = _
          rw [← OverMorphism.ext_iff]
          apply hχ.hom_ext
          · simp [-PullbackCone.π_app_left]
            exact OverMorphism.ext h₁
          · simp [-PullbackCone.π_app_left]
      }
    }
    exact c.uniq m.left (χ.left ≫ prod.fst) isPullback'
  · simp
    exact w χ
}
