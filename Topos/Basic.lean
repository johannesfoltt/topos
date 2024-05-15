
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Topos.Power
import Topos.SubobjectClassifier

namespace CategoryTheory

open Category Limits Classifier Power

universe u v

variable (C : Type u) [Category.{v} C]

class Topos where
  [has_terminal : HasTerminal C]
  [finite_limits : HasPullbacks C]
  [subobject_classifier : HasSubobjectClassifier C]
  [cartesian_closed : HasPowerObjects C]

attribute [instance] Topos.has_terminal Topos.finite_limits Topos.subobject_classifier Topos.cartesian_closed

variable [Topos C] {C}

namespace Topos

noncomputable section

def Predicate.true_ (B : C) : B ⟶ Ω C := terminal.from B ≫ (t C)

/--
  The equality predicate on `B ⨯ B`.
-/
def Predicate.eq (B : C) : B ⨯ B ⟶ Ω C := ClassifierOf (diag B)

-- B ⟶ P(B)
-- b ↦ {b' ∈ B | (b', b) ↦ 1} = {b' ∈ B | b' = b } = {b}

-- B ⨯ A ⟶ Ω
-- A ⟶ P(B)
-- a ↦ Uₐ

-- B ⨯ {a} ⟶ Ω
--  Uₐ ↣ B

/--
  The "singleton" map {•}_B : B ⟶ Pow B.
  In Set, this map sends b ∈ B to the singleton set {b}.
-/
def singleton (B : C) : B ⟶ Pow B := P_transpose (Predicate.eq B)

-- example (B X : C) (b b' : X ⟶ B) (h : b)

lemma PullbackDiagRightComm {B X : C} (b : X ⟶ B) : b ≫ diag B = prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b := by
  simp only [prod.comp_lift, comp_id, prod.lift_map, id_comp]


lemma PullbackDiagRight {B X : C} (b : X ⟶ B) : IsLimit (PullbackCone.mk b (prod.lift b (𝟙 _)) (PullbackDiagRightComm b)) := by
    apply PullbackCone.IsLimit.mk _ (fun s ↦ (PullbackCone.snd s) ≫ prod.snd)
    -- fac_left
    intro s
    have h₁ : (PullbackCone.snd s ≫ prod.map (𝟙 B) b) ≫ prod.snd = (PullbackCone.fst s ≫ diag B) ≫ prod.snd := by rw [PullbackCone.condition s]
    simp at h₁
    rw [assoc]; exact h₁
    -- fac_right
    intro s
    have h₀ : (PullbackCone.snd s ≫ prod.map (𝟙 B) b) ≫ prod.fst = (PullbackCone.fst s ≫ diag B) ≫ prod.fst := by rw [PullbackCone.condition s]
    have h₁ : (PullbackCone.snd s ≫ prod.map (𝟙 B) b) ≫ prod.snd = (PullbackCone.fst s ≫ diag B) ≫ prod.snd := by rw [PullbackCone.condition s]
    ext
    simp
    simp at h₀
    simp at h₁
    exact h₁.trans h₀.symm
    simp only [prod.comp_lift, assoc, comp_id, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd]
    -- uniq
    intro s m _ h'
    have k₁ : (m ≫ prod.lift b (𝟙 X)) ≫ prod.snd = (PullbackCone.snd s) ≫ prod.snd := by rw [h']
    simp only [prod.comp_lift, comp_id, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd] at k₁
    assumption

lemma _BigSquare_comm {B X : C} (b : X ⟶ B) : (prod.lift b (𝟙 _)) ≫ ((prod.map (𝟙 _) b) ≫ (Predicate.eq B)) = terminal.from X ≫ (t C) := by
  have sq_left_comm_b : b ≫ diag B = prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b := by simp only [prod.comp_lift, comp_id, prod.lift_map, id_comp]
  calc
    prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b ≫ Predicate.eq B
      = b ≫ diag B ≫ Predicate.eq B := by rw [←assoc, ←assoc, sq_left_comm_b]
    _ = b ≫ (terminal.from B) ≫ (t C) := by
      dsimp only [Predicate.eq]
      rw [(Classifies (diag B)).comm]
    _ = terminal.from X ≫ t C := by rw [←assoc, terminal.comp_from b]

lemma _BigSquare_pb {B X : C} (b : X ⟶ B) : IsLimit (PullbackCone.mk (prod.lift b (𝟙 _)) (terminal.from X) (_BigSquare_comm b)) := by
  let BigSquare_pb := bigSquareIsPullback _ _ _ _ _ _ _
    (by simp only [PullbackCone.mk_pt, PullbackCone.mk_π_app, prod.lift_map, comp_id, id_comp, prod.comp_lift]) (Classifies (diag B)).comm
    (Classifies (diag B)).pb (PullbackCone.flipIsLimit (PullbackDiagRight b))
  simp only [Unique.eq_default] at BigSquare_pb; assumption

/-- The singleton map {•}_B : B ⟶ Pow B is a monomorphism. -/
instance singletonMono (B : C) : Mono (singleton B) where
  right_cancellation := by
    intro X b b' h
    rw [singleton] at h
    have h₁ : prod.map (𝟙 _) (b ≫ P_transpose (Predicate.eq B)) ≫ in_ B = prod.map (𝟙 _) (b' ≫ P_transpose (Predicate.eq B)) ≫ in_ B :=
      congrFun (congrArg CategoryStruct.comp (congrArg (prod.map (𝟙 B)) h)) (in_ B)
    rw [prod.map_id_comp, assoc, ←(Pow_powerizes B (Predicate.eq B))] at h₁
    rw [prod.map_id_comp, assoc, ←(Pow_powerizes B (Predicate.eq B))] at h₁
    have sq_left_comm_b : b ≫ diag B = prod.lift b (𝟙 X) ≫ prod.map (𝟙 B) b := by simp only [prod.comp_lift, comp_id, prod.lift_map, id_comp]
    have sq_left_comm_b' : b' ≫ diag B = prod.lift b' (𝟙 X) ≫ prod.map (𝟙 B) b' := by simp only [prod.comp_lift, comp_id, prod.lift_map, id_comp]
    have sq_right := (Classifies (diag B)).pb
    have big_square_b_comm := _BigSquare_comm b
    let cone_b := PullbackCone.mk (prod.lift b (𝟙 _)) (terminal.from X) big_square_b_comm
    let big_square_b := _BigSquare_pb b

    have big_square_b'_comm : (prod.lift b' (𝟙 _)) ≫ ((prod.map (𝟙 _) b) ≫ (Predicate.eq B)) = terminal.from X ≫ (t C) := by
      rw [h₁]
      exact _BigSquare_comm b'
    let cone_b' := PullbackCone.mk (prod.lift b' (𝟙 _)) (terminal.from X) big_square_b'_comm
    have big_square_b' : IsLimit cone_b' := by
      dsimp only [cone_b']
      let answer := _BigSquare_pb b'
      -- (prod.lift b (𝟙 _)) ≫ ((prod.map (𝟙 _) b) ≫ (Predicate.eq B)) = terminal.from X ≫ (t C)
      -- prod.lift b' (𝟙 X) ≫ prod.map (𝟙 B) b ≫ Predicate.eq B = terminal.from X ≫ t C
      fapply PullbackCone.IsLimit.mk
      intro s
      repeat sorry

    let cone_iso := IsLimit.conePointUniqueUpToIso big_square_b big_square_b'

    have triangle : cone_iso.hom ≫ (prod.lift b' (𝟙 _)) = (prod.lift b (𝟙 _)) :=
      IsLimit.conePointUniqueUpToIso_hom_comp big_square_b big_square_b' (some WalkingPair.left)
    rw [prod.comp_lift, comp_id] at triangle
    let t₁ : prod.lift (cone_iso.hom ≫ b') cone_iso.hom ≫ prod.fst = prod.lift b (𝟙 X) ≫ prod.fst := by rw [triangle]; rfl
    let t₂ : prod.lift (cone_iso.hom ≫ b') cone_iso.hom ≫ prod.snd = prod.lift b (𝟙 X) ≫ prod.snd := by rw [triangle]; rfl
    simp at t₁
    simp at t₂
    rw [t₂] at t₁
    -- for some reason this doesn't work??
    -- rw [id_comp] at t₁
    have id' : 𝟙 X ≫ b' = b' := by rw [id_comp]
    rw [id'] at t₁
    exact t₁.symm

def Predicate.isSingleton (B : C) : Pow B ⟶ Ω C := ClassifierOf (singleton B)

/-- The name ⌈φ⌉ : ⊤_ C ⟶ Pow B of a predicate `φ : B ⟶ Ω C`. -/
def Name {B} (φ : B ⟶ Ω C) : ⊤_ C ⟶ Pow B := P_transpose ((prod.rightUnitor B).hom ≫ φ)

def Predicate.fromName {B} (φ' : ⊤_ C ⟶ Pow B) := (prod.map (𝟙 _) φ') ≫ in_ B

def Predicate.NameDef {B} (φ : B ⟶ Ω C) : (prod.rightUnitor B).hom ≫ φ = (prod.map (𝟙 _) (Name φ)) ≫ (in_ B) :=
  Pow_powerizes _ _

-- TODO: prove equivalence of the types (B ⟶ Ω C), (T_ C ⟶ Pow B), and (Subobject B).



end
end Topos
end CategoryTheory
