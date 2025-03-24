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

-- thanks to Henrik Böving for his hint with 'generalize'
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
  intros H1 H2
  cases H1 with
  | SKIP s' =>
    cases H2
    rfl
  | Assign s' x a =>
    cases H2
    rfl
  | Seq s1 s2 s3 c1 c2 H3 H4 =>
    cases H2 with | Seq s1 s2' s3 c1 c2 H5 H6 =>
    have H7: s2 = s2' := by apply L_7_9 _ _ _ _ H3 H5
    subst H7
    apply L_7_9 _ _ _ _ H4 H6
  | IfTrue s t b c1 c2 H3 H4 =>
    cases H2 with
    | IfTrue s' t' b' c1' c2' H5 H6 =>
      apply L_7_9 _ _ _ _ H4 H6
    | IfFalse _ _ _ _ _ _ _ =>
      tauto
  | IfFalse s t b c1 c2 H3 H4 =>
    cases H2 with
    | IfTrue _ _ _ _ _ _ _ =>
      tauto
    | IfFalse s' t' b' c1' c2' H5 H6 =>
      apply L_7_9 _ _ _ _ H4 H6
  | WhileFalse s b c H3 =>
    cases H2 with
    | WhileTrue _ _ _ _ _ _ _ =>
      tauto
    | WhileFalse s' b' c' H4 =>
      rfl
  | WhileTrue s1 s2 s3 b c H3 H4 H5 =>
    cases H2 with
    | WhileFalse _ _ _ _ =>
      tauto
    | WhileTrue s1' s2' s3' b' c' H6 H7 H8 =>
      have H9: s2 = s2' := by apply L_7_9 _ _ _ _ H4 H7
      subst H9
      apply L_7_9 _ _ _ _ H5 H8
  decreasing_by
    · subst c; simp; linarith
    · subst c; simp
    · subst c; simp; linarith
    · subst c; simp
    · simp [*] --- subst c not working for some reason
    · sorry --- if seems that goal is impossible to prove or False

lemma L_7_9' (c: Com) (s t1 t2: State): BigStep s c t1 → BigStep s c t2 → t1 = t2 := by
  revert s t1 t2
  induction c with
  | SKIP =>
    intros s t1 t2 H1 H2; cases H1; cases H2; rfl
  | Assign v a =>
    intros s t1 t2 H1 H2; cases H1; cases H2; rfl
  | Seq c1 c2 H3 H4 =>
    intros s t1 t2 H1 H2
    cases H1 with | Seq s1 s2 s3 c1 c2 H5 H6 =>
    cases H2 with | Seq s1' s2' s3' c1' c2' H7 H8 =>
    rw [H3 _ _ _ H5 H7] at *
    apply (H4 _ _ _ H6 H8)
  | If b c1 c2 H3 H4 =>
    intros s t1 t2 H1 H2
    cases H1 with
    | IfTrue s' t' b' c1' c2' H5 H6 =>
      cases H2 with
      | IfTrue s'' t'' b'' c1'' c2'' H7 H8 =>
        apply (H3 _ _ _ H6 H8)
      | _ => tauto
    | IfFalse s' t' b' c1' c2' H5 H6 =>
      cases H2 with
      | IfFalse s'' t'' b'' c1'' c2'' H7 H8 =>
        apply (H4 _ _ _ H6 H8)
      | _ => tauto
  | While b c H3 =>
    intros s t1 t2 H1 H2
    sorry -- no success here for me :(
