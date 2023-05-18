Require Import String.
Require Import ssreflect.
From Coq Require Import
  Lists.List
  Streams.
From stdpp Require Import gmap.

(** Language - Syntax *)
Inductive op :=
| Add | Sub | Mul | Eq | Neq | Leq | Lt | Geq | Gt.

Notation var := string.
Notation value := nat.

Inductive expr :=
| ELit : value -> expr
| EVar : var -> expr
| EOp : expr -> op -> expr -> expr.

Inductive channel :=
  Public | Secret.

Inductive command :=
| CSkip : command
| CAssign : var -> expr -> command
| CSeq : command -> command -> command
| CIfThenElse : expr -> command -> command -> command
| CWhile : expr -> command -> command
| CInput : channel -> var -> command
| COutput : channel -> expr -> command
| CJoin : command (* Used only inside proofs (see augmented.v) *)
.

Coercion ELit: value >-> expr.
Coercion EVar: var >-> expr.

Notation "'SKIP'" := CSkip.
Notation "x '::=' e" :=(CAssign x e) (at level 60).
Notation "c1 ;;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIfThenElse c1 c2 c3) (at level 80, right associativity).
Notation "'INPUT' x '@' c" := (CInput c x) (at level 60).
Notation "'OUTPUT' e '@' c" := (COutput c e) (at level 60).


(** Language - Operational Semantic *)

Definition memory := gmap var value.
(* Initial memory *)
Definition minit : memory := gmap_empty.

Definition apply_op (l : value) op r : value :=
  match op with
  | Add => l + r
  | Sub => l - r
  | Mul => l * r
  | Eq => if Nat.eqb l r then 1 else 0
  | Neq => if Nat.eqb l r then 0 else 1
  | Leq => if Nat.leb l r then 1 else 0
  | Lt => if Nat.ltb l r then 1 else 0
  | Geq => if Nat.leb r l then 1 else 0
  | Gt => if Nat.ltb r l then 1 else 0
  end .


Inductive eval_expr : expr -> memory -> value -> Prop :=
| Lit : forall n m, eval_expr (ELit n) m n
| Var : forall x m v, m !! x = Some v -> eval_expr (EVar x) m v
| Op : forall e1 op e2 v1 v2 m, eval_expr e1 m v1 -> eval_expr e2 m v2 ->
                           eval_expr (EOp e1 op e2) m (apply_op v1 op v2)
.

Notation "e ';' m '⇓' v" := (eval_expr e m v) (at level 85).
Notation "x :::: c" := (Streams.Cons x c) (at level 85).

Inductive event :=
| EvInput : channel -> value -> event
| EvOutput : channel -> value -> event
| Write : var -> value -> event (* Used only in proofs (see augmented.v) *)
.
Definition trace := list event.
(* In the state, Some c represents a command, and None represents a Stop *)
Definition config : Type :=
  (option command) * (Stream value) * (Stream value) * memory * trace.

Reserved Notation "cfg '--->' cfg'" (at level 95).
Inductive exec_command : config -> config -> Prop :=
| Skip : forall S P m t,
  ( Some SKIP, S, P, m, t ) ---> ( None, S, P, m, t )

| Assign : forall S P m t x e v,
  e ; m ⇓ v ->
  ( Some (x ::= e), S, P, m, t) ---> ( None, S, P, <[ x := v ]> m, t)

| Seq1 : forall S P m t c1 c2 S' P' m' t' c1',
  ( Some c1, S, P, m, t ) ---> ( Some c1', S', P', m', t' ) ->
  ( Some (c1 ;;; c2), S, P, m, t ) ---> ( Some (c1' ;;; c2), S', P', m', t' )

| Seq2 : forall S P m t c1 c2 S' P' m' t',
  ( Some c1, S, P, m, t ) ---> ( None , S', P', m', t' ) ->
  ( Some (c1 ;;; c2), S, P, m, t ) ---> ( Some c2 , S', P', m', t' )

| If : forall S P m t (c1 c2 : command) e v,
  e ; m ⇓ v ->
  ( Some (IFB e THEN c1 ELSE c2 FI), S, P, m, t ) --->
    ( Some (if Nat.eqb v 0 then c2 else c1), S, P, m, t )
| While : forall S P m t e c,
  ( Some (WHILE e DO c END) , S, P, m , t ) --->
  ( Some (IFB e THEN (c ;;; WHILE e DO c END) ELSE SKIP FI), S, P, m, t )

| InputPublic : forall S P m t x v,
  ( Some (INPUT x @Public) , S, v::::P, m, t )  --->
  ( None , S, P, <[ x := v ]> m, EvInput Public v :: t)

| InputSecret : forall S P m t x v,
  ( Some (INPUT x @Secret), v::::S, P, m, t ) --->
  ( None , S, P, <[ x := v ]> m, EvInput Secret v :: t)

| Output : forall S P m t ch e v,
  e ; m ⇓ v ->
  ( Some (OUTPUT e @ch), S, P, m, t) --->
  ( None , S, P, m, EvOutput ch v :: t)
where "cfg '--->' cfg'" := (exec_command cfg cfg').

(* at most n execution steps: *)
Definition exec_n : nat -> config -> config -> Prop := bsteps exec_command.
Notation "cfg '--->[' n ']' cfg'" := (exec_n n cfg cfg') (at level 40).

(* reflexive and transitive closure of the execution relation: *)
Definition exec_trans : config -> config -> Prop := rtc exec_command.
Notation "cfg '--->*' cfg'" := (exec_trans cfg cfg') (at level 40).
