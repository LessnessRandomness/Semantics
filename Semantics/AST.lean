import Mathlib

inductive UnaryOp: Type where
| opposite
| negation

inductive BinaryOp: Type where
| multiplication
| division
| remainder
| addition
| subtraction
| lt
| le
| eq
| ne
| and
| or
| has_property
| get_property
| set_property
| delete_property
| array_get
| array_set

inductive Literal: Type where
| null
| undefined
| boolean: Bool → Literal
| string: String → Literal
| integer: ℤ → Literal

mutual
  inductive Expr: Type where
  | identifier: String → Expr
  | literal: Literal → Expr
  | object: List (String × Expr) → Expr
  | array: List Expr → Expr
  | function: List String → List Stat → Expr
  | fun_apply: Expr → List Expr → Expr
  | unary_op: UnaryOp → Expr → Expr
  | binary_op: BinaryOp → Expr → Expr
  | if_then_else: Expr → Expr → Expr → Expr
  | assignment: Expr → Expr → Expr

  inductive Stat: Type where
  | expr: Expr → Stat
  | block: List Stat → Stat
  | var_decl: String → Option Expr → Stat
  | conditional: Expr → Stat → Option Stat → Stat
  | while: Expr → Stat → Stat
  | fun_return: Option Expr → Stat
  | error: Expr → Stat
end
