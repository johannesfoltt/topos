import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Topos.NewDefinitions.NewClassifier
import Topos.HelpfulCategoryTheory.OverLimits

namespace CategoryTheory

open Category Limits Over MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier

universe u v

namespace Over

noncomputable section

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C] [Classifier C] {X : C}

instance : CartesianMonoidalCategory (Over X) := by exact cartesianMonoidalCategory X

--here, abbrev is needed, because else aesop_cat cannot solve commutativity condition

abbrev classifierOver.Over_Ω : (Over X) := mk (snd Ω X)

abbrev classifierOver.Over_t_ : 𝟙_ (Over X) ⟶ Over_Ω := homMk (lift (Predicate.true_ X) (𝟙 X))

abbrev classifierOver.Over_char {S A : Over X} (m : S ⟶ A) [Mono m] : A ⟶ Over_Ω := homMk (lift (χ_ m.left) (A.hom))

lemma classifierOver.isPullback_lift_condition {S A : Over X} (m : S ⟶ A) [Mono m] (s : PullbackCone (Over_char m) (Over_t_)) : s.fst.left ≫ χ_ m.left = ((s.snd ≫ terminalIso.hom).left ≫ (Limits.prod.leftUnitor X).inv ≫ prod.fst) ≫ c.t := by {
  have help' := s.condition
  rw [OverMorphism.ext_iff, comp_left] at help'
  simp at help'; simp
  rw [← prod.lift_fst (s.fst.left ≫ c.char m.left) s.pt.hom, ← prod.lift_fst (terminal.from s.pt.left ≫ c.t) (s.snd.left ≫ (mkIdTerminal.from (⊤_ Over X)).left)]
  exact congrFun (congrArg CategoryStruct.comp help') prod.fst
}

lemma Over.classifierOver.isPullback_homMk_w (s : PullbackCone (char m) (t c)) : (IsPullback.lift (c.isPullback m.left) s.fst.left ((s.snd ≫ terminalIso.hom).left ≫ (Limits.prod.leftUnitor X).inv ≫ prod.fst) (isPullback_lift_condition s)) ≫ U.hom = s.pt.hom := by {
  rw [← w m, ← assoc, (c.isPullback m.left).lift_fst s.fst.left ((s.snd ≫ terminalIso.hom).left ≫ (Limits.prod.leftUnitor X).inv ≫ prod.fst) (isPullback_lift_condition s), w s.fst]
}

abbrev Over.classifierOver.isPullback_lift (s : PullbackCone (char c m) (t c)) := Over.homMk ((c.isPullback m.left).lift s.fst.left ((s.snd ≫ terminalIso.hom).left ≫ (Limits.prod.leftUnitor X).inv ≫ prod.fst) (isPullback_lift_condition s)) (isPullback_homMk_w s)

variable (c) (m)

lemma Over.classifierOver.isPullback : IsPullback m (terminal.from U) (classifierOver.char c m) (classifierOver.t c) where
  w := by {
    rw [OverMorphism.ext_iff, comp_left, comp_left]; simp
    refine Limits.prod.hom_ext ?_ ?_
    · simp
      exact (c.isPullback m.left).w
    · rw [← comp_left]
      unfold mkIdTerminal
      unfold CostructuredArrow.mkIdTerminal
      unfold IsTerminal.from
      unfold Functor.preimage
      simp
  }
  isLimit' := by {
    apply Nonempty.intro
    apply PullbackCone.IsLimit.mk _ (fun s ↦ isPullback_lift s)
    · intro s
      rw [Over.OverMorphism.ext_iff, comp_left]; simp
    · intro s
      exact terminal.hom_ext (isPullback_lift s ≫ terminal.from U) s.snd
    · intro s m' h₁ h₂
      rw [Over.OverMorphism.ext_iff, comp_left] at h₁ h₂
      rw [Over.OverMorphism.ext_iff]
      apply (c.isPullback m.left).hom_ext
      · aesop_cat
      · aesop_cat
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
