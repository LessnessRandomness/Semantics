import Mathlib

-- IMP language

inductive AExp: Type where
| N: ℤ → AExp
| V: String → AExp
| Plus: AExp → AExp → AExp

def State := String → ℤ

def aval (a: AExp) (s: State): ℤ :=
  match a with
  | AExp.N n => n
  | AExp.V x => s x
  | AExp.Plus a1 a2 => aval a1 s + aval a2 s

def zero_state: State := fun _ => 0

def update {A B} [DecidableEq A] (f: A → B) (key: A) (new_value: B): A → B :=
  fun x => if x = key then new_value else f x

inductive BExp: Type where
| Bc: Bool → BExp
| Not: BExp → BExp
| And: BExp → BExp → BExp
| Less: AExp → AExp → BExp

def bval (b: BExp) (s: State): Bool :=
  match b with
  | BExp.Bc v => v
  | BExp.Not b' => not (bval b' s)
  | BExp.And b1 b2 => (bval b1 s) ∧ (bval b2 s)
  | BExp.Less a1 a2 => (aval a1 s) < (aval a2 s)

inductive Com: Type where
| SKIP
| Assign: String → AExp → Com
| Seq: Com → Com → Com
| If: BExp → Com → Com → Com
| While: BExp → Com → Com

-- Big-Step semantics

inductive BigStep: State → Com → State → Prop where
| SKIP: ∀ (s: State),
    BigStep s Com.SKIP s
| Assign: ∀ (s: State) (x: String) (a: AExp),
    BigStep s (Com.Assign x a) (update s x (aval a s))
| Seq: ∀ (s1 s2 s3: State) (c1 c2: Com),
    BigStep s1 c1 s2 → BigStep s2 c2 s3 → BigStep s1 (Com.Seq c1 c2) s3
| IfTrue: ∀ (s t: State) (b: BExp) (c1 c2: Com),
    bval b s → BigStep s c1 t → BigStep s (Com.If b c1 c2) t
| IfFalse: ∀ (s t: State) (b: BExp) (c1 c2: Com),
    (¬ bval b s) → BigStep s c2 t → BigStep s (Com.If b c1 c2) t
| WhileFalse: ∀ (s: State) (b: BExp) (c: Com),
    (¬ bval b s) → BigStep s (Com.While b c) s
| WhileTrue: ∀ (s1 s2 s3: State) (b: BExp) (c: Com),
    bval b s1 → BigStep s1 c s2 → BigStep s2 (Com.While b c) s3 → BigStep s1 (Com.While b c) s3

def equivalent_commands (c1 c2: Com): Prop :=
  ∀ (s t: State), BigStep s c1 t ↔ BigStep s c2 t

lemma L_7_3 (b: BExp) (c: Com):
  equivalent_commands
    (Com.While b c)
    (Com.If b (Com.Seq c (Com.While b c)) Com.SKIP) := by
  intros s t; constructor <;> intros H
  . cases H with
    | WhileFalse s b c H =>
      apply BigStep.IfFalse
      . assumption
      . apply BigStep.SKIP
    | WhileTrue s1 s2 s3 b c H H0 H1 =>
      apply BigStep.IfTrue
      . assumption
      . apply BigStep.Seq
        . assumption
        . assumption
  . cases H with
    | IfTrue s t b c1 c2 H H0 =>
      cases H0 with
      | Seq s1 s2 s3 c1 c2 H0 H1 =>
        apply BigStep.WhileTrue <;> assumption
    | IfFalse s t b c1 c2 H H0 =>
      cases H0
      apply BigStep.WhileFalse; assumption

lemma L_7_4 (b: BExp) (c: Com):
    equivalent_commands c (Com.If b c c) := by
  intros s t; constructor <;> intros H
  . obtain H0 | H0 := em (bval b s)
    . apply BigStep.IfTrue <;> assumption
    . apply BigStep.IfFalse <;> assumption
  . cases H <;> assumption

-- thanks to Henrik Böving for the hint about 'generalize'
lemma L_7_5 (b: BExp) (c1 c2: Com) (Hc: equivalent_commands c1 c2):
    equivalent_commands (Com.While b c1) (Com.While b c2) := by
  intros s t; constructor <;> intro H
  . generalize hfoo : (Com.While b c1) = foo at H
    induction H with
    | WhileFalse s' b' c H0 =>
      simp at hfoo
      obtain ⟨H1, H2⟩ := hfoo; subst H1 H2
      apply BigStep.WhileFalse
      assumption
    | WhileTrue s1 s2 s3 b' c H1 H2 H3 H4 H5 =>
      simp at hfoo
      obtain ⟨H1, H2⟩ := hfoo; subst H1 H2; simp at H5
      apply BigStep.WhileTrue s1 s2 s3 _ _ H1
      . rw [<- Hc]
        exact H2
      . exact H5
    | _ => tauto
  . generalize hfoo : (Com.While b c2) = foo at H
    induction H with
    | WhileFalse s' b' c H0 =>
      simp at hfoo
      obtain ⟨H1, H2⟩ := hfoo; subst H1 H2
      apply BigStep.WhileFalse
      assumption
    | WhileTrue s1 s2 s3 b' c H1 H2 H3 H4 H5 =>
      simp at hfoo
      obtain ⟨H1, H2⟩ := hfoo; subst H1 H2; simp at H5
      apply BigStep.WhileTrue s1 s2 s3 _ _ H1
      . rw [Hc]
        exact H2
      . exact H5
    | _ => tauto

lemma L_7_8: Equivalence equivalent_commands := by
  unfold equivalent_commands
  refine ⟨?_, ?_, ?_⟩
  . tauto
  . intros x y H s t
    rw [H]
  . intros x y z H H0 s t
    rw [H, H0]


--- IMP is deterministic

lemma L_7_9 (c: Com) (s t1 t2: State): BigStep s c t1 → BigStep s c t2 → t1 = t2 := by
  intros H1 H2; revert t2
  induction H1 with
  | SKIP s' =>
    intro t2 H2; cases H2; rfl
  | Assign s x a =>
    intro t2 H2; cases H2; rfl
  | Seq s1 s2 s3 c1 c2 H1 H2 H3 H4 =>
    intros t2 H5
    cases H5 with | Seq _ s2' _ _ _ H5 H6 =>
    have H7: s2 = s2' := by
      apply H3; assumption
    subst H7
    apply H4 at H6; assumption
  | IfTrue s' t b c1 c2 H1 H2 H3 =>
    intros t2 H4
    cases H4 with
    | IfTrue s t b c1 c2 H5 H6 =>
      apply H3; assumption
    | IfFalse s t b c1 c2 H5 H6 =>
      tauto
  | IfFalse s' t b c1 c2 H1 H2 H3 =>
    intros t2 H4
    cases H4 with
    | IfTrue s t b c1 c2 H5 H6 =>
      tauto
    | IfFalse s t b c1 c2 H5 H6 =>
      apply H3; assumption
  | WhileFalse s' b c' H1 =>
    intros t2 H2
    cases H2 with
    | WhileFalse s b c H2 =>
      rfl
    | WhileTrue s1 s2 s3 b c H2 H3 H4 =>
      tauto
  | WhileTrue s1 s2 s3 b c' H1 H2 H3 H4 H5 =>
    intros t2 H6
    cases H6 with
    | WhileFalse s b c H6 =>
      tauto
    | WhileTrue s1 s2' s3 b c H6 H7 H8 =>
      apply H5
      have H9: s2 = s2' := by
        apply H4; exact H7
      subst H9; assumption

--- Small-Step Semantics

inductive SmallStep: State → Com → State → Com → Prop where
| Assign: ∀ (x: String) (a: AExp) (s: State),
    SmallStep s (Com.Assign x a) (update s x (aval a s)) Com.SKIP
| Seq1: ∀ (c2: Com) (s: State),
    SmallStep s (Com.Seq Com.SKIP c2) s c2
| Seq2: ∀ (c1 c1' c2: Com) (s s': State),
    SmallStep s c1 s' c1' → SmallStep s (Com.Seq c1 c2) s' (Com.Seq c1' c2)
| IfTrue: ∀ (b: BExp) (s: State) (c1 c2: Com),
    bval b s → SmallStep s (Com.If b c1 c2) s c1
| IfFalse: ∀ (b: BExp) (s: State) (c1 c2: Com),
    (¬ bval b s) → SmallStep s (Com.If b c1 c2) s c2
| While: ∀ (b: BExp) (s: State) (c: Com),
    SmallStep s (Com.While b c) s (Com.If b (Com.Seq c (Com.While b c)) Com.SKIP)

inductive refl_trans_closure: State → Com → State → Com → Prop where
| step: ∀ {s1 s2: State} {c1 c2: Com},
    SmallStep s1 c1 s2 c2 →
    refl_trans_closure s1 c1 s2 c2
| refl: ∀ {s: State} {c: Com},
    refl_trans_closure s c s c
| trans: ∀ {s1 s2 s3: State} {c1 c2 c3: Com},
    refl_trans_closure s1 c1 s2 c2 →
    refl_trans_closure s2 c2 s3 c3 →
    refl_trans_closure s1 c1 s3 c3

lemma L_7_11 (s s1 s2: State) (c c1 c2: Com):
    SmallStep s c s1 c1 → SmallStep s c s2 c2 → (s1 = s2 ∧ c1 = c2) := by
  intros H1 H2; revert s2 c2
  induction H1 with
  | Assign x a s =>
    intros s2 c2 H2
    cases H2; tauto
  | Seq1 c2 s' =>
    intros s2 c2 H2
    cases H2
    . tauto
    . rename_i H; cases H
  | Seq2 c1' c1'' c2 s' s'' H1 H2 =>
    intros s2 c2 H2
    cases H2
    . tauto
    . rename_i H3; apply H2 at H3; tauto
  | IfTrue b s c1 c2 H =>
    intros s2 c2 H2
    cases H2 <;> tauto
  | IfFalse b s c1 c2 H =>
    intros s2 c2 H2
    cases H2 <;> tauto
  | While b s c =>
    intros s2 c2 H2
    cases H2; tauto

lemma L_7_13 (s1 s2: State) (c c1 c2: Com):
    refl_trans_closure s1 c1 s2 c → refl_trans_closure s1 (Com.Seq c1 c2) s2 (Com.Seq c c2) := by
  intros H; induction H
  . apply refl_trans_closure.step
    apply SmallStep.Seq2
    assumption
  . apply refl_trans_closure.refl
  . rename_i H1 H2 H3 H4
    apply refl_trans_closure.trans H3 H4

lemma L_7_12 (s t: State) (c: Com):
    BigStep s c t → refl_trans_closure s c t Com.SKIP := by
  intro H; induction H with
  | SKIP s =>
    apply refl_trans_closure.refl
  | Assign s x a =>
    apply refl_trans_closure.step
    apply SmallStep.Assign
  | Seq s1 s2 s3 c1 c2 H1 H2 H3 H4 =>
    apply L_7_13 (c2:=c2) at H3
    have H5: refl_trans_closure s2 (Com.Seq Com.SKIP c2) s2 c2 := by
      apply refl_trans_closure.step
      constructor
    apply refl_trans_closure.trans H3 (refl_trans_closure.trans H5 H4)
  | IfTrue s t b c1 c2 H1 H2 H3 =>
    apply refl_trans_closure.trans
    . apply refl_trans_closure.step
      apply SmallStep.IfTrue _ _ _ _ H1
    . exact H3
  | IfFalse s t b c1 c2 H1 H2 H3 =>
    apply refl_trans_closure.trans
    . apply refl_trans_closure.step
      apply SmallStep.IfFalse _ _ _ _ H1
    . exact H3
  | WhileFalse s b c H1 =>
    apply refl_trans_closure.trans
    . apply refl_trans_closure.step
      apply SmallStep.While
    . apply refl_trans_closure.step
      apply SmallStep.IfFalse; assumption
  | WhileTrue s1 s2 s3 b c H1 H2 H3 H4 H5 =>
    have H6: refl_trans_closure s1 (Com.While b c) s1 (Com.If b (Com.Seq c (Com.While b c)) Com.SKIP) := by
      apply refl_trans_closure.step; constructor
    have H7: refl_trans_closure s1 (Com.If b (Com.Seq c (Com.While b c)) Com.SKIP) s1 (Com.Seq c (Com.While b c)) := by
      apply refl_trans_closure.step; constructor; assumption
    have H8: refl_trans_closure s1 (Com.Seq c (Com.While b c)) s2 (Com.Seq Com.SKIP (Com.While b c)) := by
      apply L_7_13; assumption
    have H9: refl_trans_closure s2 (Com.Seq Com.SKIP (Com.While b c)) s2 (Com.While b c) := by
      apply refl_trans_closure.step; constructor
    apply refl_trans_closure.trans H6 (refl_trans_closure.trans H7 (refl_trans_closure.trans H8 _))
    apply refl_trans_closure.trans H9 H5
