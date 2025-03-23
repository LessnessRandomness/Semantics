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
