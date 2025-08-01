import Mathlib.CategoryTheory.Closed.Cartesian
import Topos.NewDefinitions.NewPower

open CategoryTheory Category Limits MonoidalCategory ChosenTerminalObject Classifier PowerObject ChosenPowerObjects CartesianMonoidalCategory CartesianClosed

namespace CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [Classifier C]

def PowerObject.ofExponentiable (X : C) [Exponentiable X] : PowerObject X where
  pow := Ω ^^ X
  in_ := (exp.ev X).app Ω
  transpose {Y : C} (f : (X ⊗ Y) ⟶ Ω) := CartesianClosed.curry f
  comm := by {
    intros Y f
    convert_to (tensorLeft X).map (CartesianClosed.curry f) ≫ (exp.ev X).app Ω = f
    · simp
    change CartesianClosed.uncurry (CartesianClosed.curry f) = f
    simp
  }
  uniq := by {
    intros Y f hat' h
    convert_to (tensorLeft X).map hat' ≫ (exp.ev X).app Ω = f at h
    · simp
    change CartesianClosed.uncurry hat' = f at h
    rw [← h]
    simp
  }

def ChosenPowerObjects.ofCartesianClosed [CartesianClosed C] : ChosenPowerObjects C where
  powerObject (X : C) := ofExponentiable X

namespace ChosenPowerObjects

variable [HasPullbacks C] [ChosenPowerObjects C]

noncomputable section

def expObj (A B : C) : C :=
  pullback
    ((((associator _ _ _).inv ≫ (in_ : (B ⊗ A) ⊗ _ ⟶ _))^ ≫ Predicate.isSingleton B)^)
    ⌜Predicate.true_ A⌝

def expObjToGraph (A B : C) : expObj A B ⟶ pow (B ⊗ A) := pullback.fst _ _

instance expObjToGraphMono {A B : C} : Mono (expObjToGraph A B) := pullback.fst_of_mono

lemma exp_cone_snd (A B : C) :
    pullback.snd _ _ = toUnit (expObj A B) := toUnit_unique _ _

/-- Convenience lemma used in `EvalDef_comm`. -/
lemma expObj_comm (A B : C) :
    expObjToGraph A B ≫ ((((associator _ _ _).inv ≫ (in_ : (B ⊗ A) ⊗ _ ⟶ _))^ ≫ Predicate.isSingleton B)^)
    = toUnit (expObj A B) ≫ ⌜Predicate.true_ A⌝ := by
  rw [←exp_cone_snd]; exact pullback.condition

lemma eval_def_comm (A B : C) :
  (((𝟙 A) ⊗ (expObjToGraph A B)) ≫ ((associator _ _ _).inv ≫ (in_ : (B ⊗ A) ⊗ _ ⟶ _))^) ≫ Predicate.isSingleton B
  = Predicate.true_ (A ⊗ expObj A B) := by {
    let id_m : A ⊗ expObj A B ⟶ A ⊗ pow (B ⊗ A) := (𝟙 _) ⊗ (expObjToGraph A B)
    let v := (((associator _ _ _).inv ≫ (in_ : (B ⊗ A) ⊗ _ ⟶ _))^)
    let σ_B := Predicate.isSingleton B
    let u := ((v ≫ σ_B)^)
    let id_u := (𝟙 A) ⊗ u
    have comm_middle : v ≫ σ_B = id_u ≫ in_ := (comm (v ≫ σ_B)).symm
    have comm_left : id_m ≫ id_u = ((𝟙 A) ⊗ (toUnit _)) ≫ ((𝟙 _) ⊗ ⌜Predicate.true_ A⌝) := by
      rw [← tensor_comp, ← tensor_comp]
      ext
      · simp
      · rw [tensorHom_snd, tensorHom_snd, expObj_comm]
    have h_terminal : (((𝟙 A) ⊗ (toUnit (expObj A B))) ≫ (fst _ _)) ≫ toUnit A = toUnit _ := toUnit_unique _ _
    rw [assoc, comm_middle, ←assoc, comm_left, assoc, Predicate.NameDef]
    dsimp [Predicate.true_]
    rw [←assoc, ←assoc, h_terminal]
}

def eval (A B : C) : A ⊗ (expObj A B) ⟶ B :=
  IsPullback.lift (isPullback _) _ _ (eval_def_comm _ _)

lemma eval_condition (A B : C) :
    eval A B ≫ singleton B
    = ((𝟙 _) ⊗ (expObjToGraph A B)) ≫ ((associator _ _ _).inv ≫ in_)^ :=
  IsPullback.lift_fst (isPullback _) _ _ (eval_def_comm _ _)

  --We use different definition of adjunction

variable {A B X : C} (f : A ⊗ X ⟶ B)

abbrev h_map : X ⟶ pow (B ⊗ A) :=
  ((associator _ _ _).hom ≫ ((𝟙 _) ⊗ f) ≫ Predicate.eq _)^

omit [HasPullbacks C] in
lemma homMap_comm :
    h_map f ≫ (((associator B A (pow (B ⊗ A))).inv
    ≫ in_)^ ≫ Predicate.isSingleton B)^ =
    toUnit X ≫ ⌜Predicate.true_ A⌝ := by
  -- consider (1⨯f) ≫ (eq B) : B ⨯ A ⨯ X ⟶ Ω C.
  let id_f'eq : B ⊗ A ⊗ X ⟶ Ω := ((𝟙 _) ⊗ f) ≫ Predicate.eq _
  -- h is the map that, in `Set`, takes an element of X to the graph of the corresponding function.
  -- We want to lift this to a map X ⟶ Exp A B.
  -- The idea is to show that this map actually "maps elements of X to graphs of functions", which,
  -- in an arbitrary topos, is the same as checking commutativity of the obvious square.
  let h : X ⟶ pow (B ⊗ A) := (((associator _ _ _).hom ≫ id_f'eq)^)
  -- h is by definition a P-transpose
  have h_condition : (associator _ _ _).hom ≫ id_f'eq
  = (((𝟙 B) ⊗ (𝟙 A)) ⊗ h) ≫ in_ := by {
    rw [tensor_id]
    symm
    exact PowerObject.comm _
  }
  -- moving the associator to the rhs of `h_condition`.
  have h_condition₂ : id_f'eq
  = (associator _ _ _).inv ≫ (((𝟙 B) ⊗ (𝟙 A)) ⊗ h) ≫ in_ := by {
    rw [←h_condition, ←assoc, (associator _ _ _).inv_hom_id, id_comp]
  }
  -- this is the map v: A ⨯ P(B⨯A) ⟶ P(B) which was used in the definition of `Exp A B`.
  let v : A ⊗ pow (B ⊗ A) ⟶ pow B := (((associator _ _ _).inv ≫ in_)^)
  -- v is by definition a P-transpose
  have v_condition : (associator _ _ _).inv ≫ in_ = ((𝟙 B) ⊗ v) ≫ in_ := Eq.symm (transpose_left_inv ((α_ B A (pow (B ⊗ A))).inv ≫ in_))

  have lhs : (((𝟙 A) ⊗ h) ≫ v ≫ Predicate.isSingleton B)^
  = h ≫ (v ≫ Predicate.isSingleton B)^ := by
    apply PowerObject.uniq
    rw [id_tensor_comp, assoc _ _ (in_), PowerObject.comm, ←assoc]
  rw [←lhs]
  -- Claim that f ≫ {•}_B = (1⨯h) ≫ v.
  -- This is obtained by showing that both maps are the P-transpose of (1⨯f) ≫ (eq B).
  -- There might be a slightly faster way to do this.
  have transpose₁ : id_f'eq^ = f ≫ singleton _ := by{
    apply PowerObject.uniq
    dsimp only [PowerObject.singleton]
    rw [id_tensor_comp, assoc, (comm (Predicate.eq B))]
  }
  have shuffle_h_around : (associator B A X).inv ≫ (((𝟙 _) ⊗ (𝟙 _)) ⊗ h)
  = ((𝟙 B) ⊗ ((𝟙 A) ⊗ h)) ≫ (associator B A (pow (B ⊗ A))).inv := by simp
  have transpose₂ : id_f'eq^ = ((𝟙 _) ⊗ h) ≫ v := by {
    apply PowerObject.uniq
    rw [h_condition₂, ←assoc, shuffle_h_around, id_tensor_comp, assoc _ _ in_,
    ←v_condition, assoc]
  }
  have eqn₁ : f ≫ singleton _ = ((𝟙 _) ⊗ h) ≫ v := transpose₁.symm.trans transpose₂
  -- now compose by the `isSingleton B` predicate.
  have eqn₂ : f ≫ singleton _ ≫ Predicate.isSingleton _
  = ((𝟙 _) ⊗ h) ≫ v ≫ Predicate.isSingleton _ := by {
    rw [←assoc, ←assoc, eqn₁]
  }
  rw [←eqn₂]
  -- from here, the argument is mostly definition unpacking.
  apply PowerObject.uniq
  dsimp only [name, Predicate.true_, Predicate.isSingleton]
  have f_toUnit : f ≫ toUnit B = toUnit _ := Unique.eq_default _
  have rightUnitor_toUnit : (rightUnitor A).hom ≫ toUnit A = toUnit _ := Unique.eq_default _
  have A_X_toUnit : ((𝟙 A) ⊗ (toUnit X)) ≫ toUnit (A ⊗ 𝟙_ C) = toUnit _ := Unique.eq_default _
  have obv : toUnit (A ⊗ 𝟙_ C) ≫ t_
  = ((𝟙 A) ⊗ ((toUnit (A ⊗ 𝟙_ C) ≫ t_)^)) ≫ in_ := (PowerObject.comm _).symm
  have map_def : (rightUnitor A).hom = fst _ _ := rightUnitor_hom A
  rw [Classifier.comm (singleton _), ←assoc, ←map_def, from_eq_toUnit, rightUnitor_toUnit, ←assoc, from_eq_toUnit, f_toUnit, id_tensor_comp, assoc, ←obv, ←assoc, A_X_toUnit]

def expObjMap : X ⟶ expObj A B :=
  pullback.lift (h_map f) (toUnit X) (homMap_comm f)

@[simp]
lemma expObjMap_condition : expObjMap f ≫ (expObjToGraph A B) = h_map f :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem expObj_exponentiates : ((𝟙 _ ) ⊗ (expObjMap f)) ≫ eval A B = f := by
  rw [←cancel_mono (singleton B), assoc, eval_condition, ←assoc, ← tensor_comp, id_comp, expObjMap_condition]
  have h : transposeInv (f ≫ singleton B)
      = transposeInv (((𝟙 A) ⊗ (h_map f)) ≫ transpose ((associator B A (pow (B ⊗ A))).inv ≫ in_)) := by
    rw [transposeInv, transposeInv, id_tensor_comp, assoc, PowerObject.singleton,
      PowerObject.comm, id_tensor_comp, assoc, PowerObject.comm, ←assoc]
    have h' : (((𝟙 B) ⊗ ((𝟙 A) ⊗ (h_map f)))
        ≫ (associator B A (pow (B ⊗ A))).inv) = (associator B A X).inv ≫ ((𝟙 _) ⊗ (h_map f)) := by simp
    rw [h', assoc, h_map, PowerObject.comm, ←assoc, Iso.inv_hom_id, id_comp]
  have h₀ := congrArg (fun k => transpose k) h
  have t₁ : ((f ≫ singleton B)^)^ = f ≫ singleton B := (transposeEquiv _ _).right_inv _
  have t₂ : (((((𝟙 A) ⊗ (h_map f)) ≫ ((associator B A (pow (B ⊗ A))).inv ≫ in_)^))^)^
    = (((𝟙 A) ⊗ (h_map f)) ≫ ((associator B A (pow (B ⊗ A))).inv ≫ in_)^) :=
      transpose_right_inv _
  simp only [t₁, t₂] at h₀
  exact h₀.symm

theorem expObjMap_Unique {exp' : X ⟶ expObj A B} (h : ((𝟙 _) ⊗ exp') ≫ (eval A B) = f) :
    expObjMap f = exp' := by
  have h_singleton := congrArg (fun k ↦ k ≫ singleton B) h
  simp only at h_singleton
  let v : A ⊗ pow (B ⊗ A) ⟶ pow B := (((associator _ _ _).inv ≫ in_)^)
  -- want to rewrite (1⨯g) ≫ eval A B ≫ singleton B = (1⨯(g≫m)) ≫ v
  have rhs : eval A B ≫ singleton B = ((𝟙 _) ⊗ (expObjToGraph A B)) ≫ v := by
    apply PullbackCone.IsLimit.lift_fst
  rw [assoc, rhs, ←assoc, ← id_tensor_comp] at h_singleton
  let id_f'eq : B ⊗ A ⊗ X ⟶ Ω := ((𝟙 _) ⊗ f) ≫ Predicate.eq _
  have h₁ : id_f'eq^ = f ≫ singleton B := by
    apply PowerObject.uniq
    dsimp only [id_f'eq, PowerObject.singleton]
    rw [id_tensor_comp, assoc, PowerObject.comm (Predicate.eq B)]
  have h₂ : (((𝟙 _) ⊗ ((𝟙 _) ⊗ (exp' ≫ expObjToGraph A B)))
      ≫ (associator _ _ _).inv ≫ in_)^
      = ((𝟙 _) ⊗ (exp' ≫ expObjToGraph A B)) ≫ v := by
    apply PowerObject.uniq
    rw [id_tensor_comp, assoc, PowerObject.comm]
  have h₃ := PowerObject.comm ((((𝟙 B) ⊗ ((𝟙 A) ⊗ (exp' ≫ expObjToGraph A B)))
      ≫ (associator B A (pow (B ⊗ A))).inv ≫ in_))
  rw [h₂, h_singleton, ←h₁, PowerObject.comm id_f'eq, ←assoc] at h₃
  have h' := expObj_exponentiates f
  have h'_singleton := congrArg (fun k ↦ k ≫ singleton B) h'
  simp only at h'_singleton
  rw [assoc, rhs, ←assoc, ←id_tensor_comp] at h'_singleton
  have h₂' : (((𝟙 _) ⊗ ((𝟙 _) ⊗ (expObjMap f ≫ expObjToGraph A B)))
      ≫ (associator _ _ _).inv ≫ in_)^
      = ((𝟙 _) ⊗ (expObjMap f ≫ expObjToGraph A B)) ≫ v := by
    apply PowerObject.uniq
    rw [id_tensor_comp, assoc, PowerObject.comm]
  have h₃' := PowerObject.comm ((((𝟙 B) ⊗ ((𝟙 A) ⊗ (expObjMap f ≫ expObjToGraph A B)))
    ≫ (associator B A (pow (B ⊗ A))).inv ≫ in_))
  rw [h₂', h'_singleton, ←h₁, PowerObject.comm id_f'eq, ←assoc] at h₃'

  have hx := h₃'.symm.trans h₃
  have c₀ : ((𝟙 B) ⊗ ((𝟙 A) ⊗ (exp' ≫ expObjToGraph A B))) ≫ (associator _ _ _).inv
    = (associator _ _ _).inv ≫ ((𝟙 _) ⊗ (exp' ≫ expObjToGraph A B)) := by simp
  have c₁ : ((𝟙 B) ⊗ ((𝟙 A) ⊗ (expObjMap f ≫ expObjToGraph A B)))
      ≫ (associator _ _ _).inv
      = (associator _ _ _).inv ≫ ((𝟙 _) ⊗ (expObjMap f ≫ expObjToGraph A B)) := by simp
  rw [c₀, c₁] at hx
  have hy := congrArg (fun k ↦ (associator B A X).hom ≫ k) hx
  simp only at hy
  rw [←assoc, ←assoc, Iso.hom_inv_id, id_comp, ←assoc, ←assoc, Iso.hom_inv_id, id_comp] at hy
  have hz := congrArg (fun k ↦ transpose k) hy
  simp only at hz
  rw [transpose_right_inv, transpose_right_inv] at hz
  rw [cancel_mono] at hz
  assumption


abbrev expObjMapInv {Y Z : C} (f : X ⟶ expObj Y Z) : Y ⊗ X ⟶ Z := ((𝟙 _) ⊗ f) ≫ eval _ _

def expAdjEquiv (A B X : C) : (A ⊗ X ⟶ B) ≃ (X ⟶ expObj A B) where
  toFun := expObjMap
  invFun := expObjMapInv
  left_inv := fun f => expObj_exponentiates f
  right_inv := by
    intro f
    apply expObjMap_Unique; rfl

def expHom {X Y : C} (A : C) (f : X ⟶ Y) : expObj A X ⟶ expObj A Y := expObjMap (eval A _ ≫ f)

def expFunctor (A : C) : C ⥤ C where
  obj := fun B ↦ expObj A B
  map := fun {X Y} f ↦ expHom A f
  map_id := by
    intro X
    dsimp only [expHom]
    rw [comp_id]
    apply expObjMap_Unique
    rw [tensor_id, id_comp]
  map_comp := by
    intro X Y Z f g
    --change ExpHom A (f ≫ g) = ExpHom A f ≫ ExpHom A g
    dsimp only [expHom]
    apply expObjMap_Unique
    rw [@id_tensor_comp, assoc, expObj_exponentiates, expObj_exponentiates_assoc, assoc]

def tensorExpAdjunction (A : C) : tensorLeft A ⊣ expFunctor A := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  · intro X B
    exact expAdjEquiv A B X

  · intro X X' Y f g
    convert_to (expAdjEquiv A Y X).symm (f ≫ g) = ((𝟙 A) ⊗ f) ≫ (expAdjEquiv A Y X').symm g
    · congr; simp
    change ((𝟙 A) ⊗ (f ≫ g)) ≫ eval _ _ = ((𝟙 A) ⊗ f) ≫ ((𝟙 A) ⊗ g) ≫ eval _ _
    simp

  · intro X Y Y' f g
    change expObjMap (f ≫ g) = expObjMap f ≫ expHom A g
    apply expObjMap_Unique
    dsimp only [expHom]
    rw [id_tensor_comp, assoc, expObj_exponentiates, expObj_exponentiates_assoc]

def exponentiable (A : C) : Exponentiable A where
  rightAdj := expFunctor A
  adj := tensorExpAdjunction A

def cartesianClosed : CartesianClosed C where
  closed (A : C) := exponentiable A
