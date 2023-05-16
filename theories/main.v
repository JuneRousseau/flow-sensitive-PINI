Require Import String.
From Coq Require Import Streams.
From Coq Require Import Lists.List.
From stdpp Require Import gmap.
(* Import ListNotations. *)
Open Scope string_scope.
Require Import ssreflect.
From fspini Require Import map_simpl.


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

(* This type will be used for both memories and contexts *)
(* Inductive varmap (A : Type) := *)
(* | Empty : varmap A *)
(* | Cons : var -> A -> varmap A -> varmap A *)
(* . *)

(* Fixpoint find_var {A} x (m : varmap A) := *)
(*   match m with *)
(*   | Empty _ => None *)
(*   | Cons _ y v m => if String.eqb y x then Some v else find_var x m *)
(*   end. *)

(* Fixpoint find_and_remove {A} x (m : varmap A) := *)
(*   match m with *)
(*   | Empty _ => None *)
(*   | Cons _ y v m => if String.eqb y x then Some (v, m) else *)
(*                      match find_and_remove x m with *)
(*                      | None => None *)
(*                      | Some (vx, m) => Some (vx, Cons _ y v m) *)
(*                      end *)
(*   end. *)

(* Fixpoint set_var {A} x (v : A) m := *)
(*   match m with *)
(*   | Empty _ => Cons _ x v m *)
(*   | Cons _ y vy m => if String.eqb y x then Cons _ x v m else Cons _ y vy (set_var x v m) *)
(*   end. *)

(* Notation "'[' x ':=' v ']' m" := (Cons _ x v m) (at level 40). *)
(* Notation "'∅'" := (Empty _) (at level 40). *)

Definition memory := gmap var value.

Fixpoint apply_op (l : value) op r : value :=
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

Notation "e ';' m '⇓' v" := (eval_expr e m v) (at level 20).
Notation "x :::: c" := (Streams.Cons x c) (at level 20).

Inductive event :=
| EvInput : channel -> value -> event
| EvOutput : channel -> value -> event.
Definition trace := list event.
(* In the state, Some c represents a command, and None represents a Skip *)
Definition state : Type := (Stream value) * (Stream value) * memory * trace.
Inductive config := Config (c : option command) ( st : state).
Notation "'⟪' c ',' st '⟫'" := (Config c st) (at level 10, c at level 20, st at level 20).

Reserved Notation "cfg '--->' cfg'" (at level 40).
Inductive exec_command : config -> config -> Prop :=
| Skip : forall st,
  ⟪ Some SKIP , st ⟫ ---> ⟪ None , st ⟫

| Assign : forall S P x e v m t,
  e ; m ⇓ v ->
  ⟪ Some (x ::= e), (S, P, m, t) ⟫ ---> ⟪ None , (S, P, <[ x := v ]> m, t) ⟫

| Seq1 : forall st c1 c2 st' c1',
  ⟪ Some c1 , st ⟫ ---> ⟪ Some c1' , st' ⟫ ->
  ⟪ Some (c1 ;;; c2) , st ⟫ ---> ⟪ Some (c1' ;;; c2) , st' ⟫

| Seq2 : forall st c1 c2 st',
  ⟪ Some c1 , st ⟫ ---> ⟪ None , st' ⟫ ->
  ⟪ Some (c1 ;;; c2) , st ⟫ ---> ⟪ Some c2 , st' ⟫

| If : forall S P e (c1 c2 : command) m t v (c: command),
  e ; m ⇓ v ->
  c = (if Nat.eqb v 0 then c2 else c1) ->
  ⟪ Some (IFB e THEN c1 ELSE c2 FI), (S, P, m, t) ⟫ ---> ⟪ Some c, (S, P, m, t) ⟫

| While : forall st c e,
  ⟪ Some (WHILE e DO c END) , st ⟫ --->
  ⟪ Some (IFB e THEN (c ;;; WHILE e DO c END) ELSE SKIP FI) , st ⟫

| InputPublic : forall S v P x m t,
  ⟪ Some (INPUT x @Public) , (S, v::::P, m, t) ⟫ --->
  ⟪ None , (S, P, <[ x := v ]> m, EvInput Public v :: t) ⟫

| InputSecret : forall v S P x m t,
  ⟪ Some (INPUT x @Secret) , (v::::S, P, m, t) ⟫ --->
  ⟪ None , (S, P, <[ x := v ]> m, EvInput Secret v :: t) ⟫

| Output : forall S P ch e m t v,
  e ; m ⇓ v ->
  ⟪ Some (OUTPUT e @ch) , (S, P, m, t) ⟫ --->
  ⟪ None , (S, P, m, EvOutput ch v :: t) ⟫
where "cfg '--->' cfg'" := (exec_command cfg cfg').


(* reflexive and transitive closure of the execution relation: *)
Definition exec_trans : config -> config -> Prop := rtc exec_command.
Notation "cfg '--->*' cfg'" := (exec_trans cfg cfg') (at level 40).
(* | exec_empty : forall s, exec_trans s s *)
(* | exec_step : forall s1 s2 s3, exec_command s1 s2 -> exec_trans s2 s3 -> exec_trans s1 s3 *)
(* . *)

(* Initial memory *)
Definition minit : memory := gmap_empty.

Fixpoint public_projection (t: trace) : trace :=
  match t with
  | [] => []
  | (EvInput Public v) :: q => (EvInput Public v :: public_projection q)
  | (EvOutput Public v) :: q => (EvOutput Public v :: public_projection q)
  | _ :: q => (public_projection q)
  end.


(* knowledge P c d S means that S is in the Set K(P,c,d) *)
Inductive knowledge: (Stream value) -> command -> trace -> (Stream value) -> Prop :=
| Know : forall P c d S,
    (exists S' P' c' m' t',
        ⟪ Some c, (S, P, minit, nil) ⟫ --->* ⟪ c' ,  (S', P', m', t') ⟫
        /\ public_projection t' = d)
    -> knowledge P c d S
.

Definition PSNI c :=
  forall P a d t,
    (exists S S' P' c' m',
        ⟪ Some c, (S, P, minit, nil) ⟫ --->* ⟪ c' ,  (S', P', m', t) ⟫
        /\ public_projection t = a :: d) ->
    (* Set equality is described with an iff *)
    (forall S, knowledge P c (a :: d) S <-> knowledge P c d S).

(* progress_knowledge P c d S means that S is in the Set K->(P,c,d) *)
Inductive progress_knowledge: (Stream value) -> command -> trace -> (Stream value) -> Prop :=
| PKnow : forall P c d S,
    (exists S' P' c' m' t' a,
        ⟪ Some c, (S, P, minit, nil) ⟫ --->* ⟪ c' ,  (S', P', m', t') ⟫
        /\ public_projection t' = a :: d) ->
    progress_knowledge P c d S
.

Definition PINI c :=
  forall P a d t,
    (exists S S' P' c' m',
        ⟪ Some c, (S, P, minit, nil) ⟫ --->* ⟪ c' ,  (S', P', m', t) ⟫
        /\ public_projection t = a :: d) ->
    (* Set equality is described with an iff *)
    (forall S, knowledge P c (a :: d) S <-> progress_knowledge P c d S).


Inductive confidentiality :=
  LPublic | LSecret.

Definition join l1 l2 :=
  match l1, l2 with
  | LPublic, LPublic => LPublic
  | _, _ => LSecret
  end.

Definition flows l1 l2 :=
  match l1, l2 with
  | LSecret, LPublic => False
  | _, _ => True
  end.

#[export] Instance sqsubseteq_confidentiality : SqSubsetEq confidentiality.
Proof. exact flows. Defined.

#[export] Instance join_confidentiality : Join confidentiality.
Proof. exact join. Defined.

(* Notation "l1 '⊔' l2" := (join l1 l2) (at level 40). *)
(* Notation "l1 '⊑' l2" := (flows l1 l2) (at level 40). *)

Definition context := gmap var confidentiality.
Definition gamma0 : context := gmap_empty.

(* A memory and a context have the same support if the same variables are defined in them *)
Definition same_support (m : memory) (gamma : context) : Prop :=
  forall x, match m !! x, gamma !! x with
       | Some _, Some _ | None, None => True
       | _, _ => False
       end.


(* Joining two contexts, to be used after an If-statement *)
(* Fixpoint join_context (gamma1 gamma2 : context) : context := *)
(*   match gamma1 with *)
(*   | Empty _ => gamma2 *)
(*   | Cons _ x v gamma1 => *)
(*       match find_and_remove x gamma2 with *)
(*       | Some (v', gamma2) => Cons _ x (join v v') (join_context gamma1 gamma2) *)
(*       | None => Cons _ x v (join_context gamma1 gamma2) *)
(*       end *)
(*   end. *)

Definition join_context (gamma1 gamma2 : context) : context :=
  gmap_merge _ _ _
    (fun opt1 opt2 =>
       match opt1, opt2 with
       | Some l1, Some l2 => Some (l1 ⊔ l2)
       | None, _ => opt2
       | _, None => opt1
       end
    )
    gamma1 gamma2.
Notation "g1 '⊔g' g2" := (join_context g1 g2) (at level 40).

Reserved Notation "'{{' Γ '⊢' e ':' ℓ '}}'" (at level 10, Γ at level 50, e at level 99).

Inductive typecheck_expr : context -> expr -> confidentiality -> Prop :=
| TLit : forall Γ n, {{ Γ ⊢ (ELit n) : LPublic }}
| TVar : forall l Γ x,
     Γ !! x = Some l ->
    {{ Γ ⊢ (EVar x) : l }}
| TOp : forall l1 l2 Γ e1 op e2 l,
    {{ Γ ⊢ e1 : l1 }} ->
    {{ Γ ⊢ e2 : l2 }} ->
    l = (l1 ⊔ l2) ->
    {{ Γ ⊢ (EOp e1 op e2) : l }}
where "{{ Γ '⊢' e ':' ℓ }}" := (typecheck_expr Γ e ℓ)
.

Definition confidentiality_of_channel ch :=
  match ch with
  | Secret => LSecret
  | Public => LPublic
  end.

Reserved Notation "-{ Γ ',' pc '⊢' e '~>' Γ2 }-"
  (at level 10, Γ at level 55, Γ2 at level 50, pc at level 35, e at level 99).
Inductive typecheck : context -> confidentiality -> command -> context -> Prop :=
| TSkip : forall Γ pc,
  -{ Γ, pc ⊢ CSkip ~> Γ }-

| TAssign : forall le Γ pc x e Γ',
  {{ Γ ⊢ e : le }} ->
  Γ' = <[ x := (le ⊔ pc) ]> Γ ->
  -{ Γ, pc ⊢ (CAssign x e) ~> Γ' }-

| TSeq : forall (Γ1 Γ2 Γ3 : context) pc c1 c2,
  -{ Γ1, pc ⊢ c1 ~> Γ2 }- ->
  -{ Γ2, pc ⊢ c2 ~> Γ3 }- ->
  -{ Γ1, pc ⊢ (CSeq c1 c2) ~> Γ3 }-

| TIf : forall l Γ Γ1 Γ2 Γ' pc e c1 c2,
  {{ Γ ⊢ e : l }} ->
  -{ Γ, pc ⊔ l ⊢ c1 ~> Γ1 }- ->
  -{ Γ, pc ⊔ l ⊢ c2 ~> Γ2 }- ->
  Γ' = (Γ1 ⊔g Γ2) ->
  -{ Γ, pc ⊢ (CIfThenElse e c1 c2) ~> Γ' }-

(* Does not change the environment *)
| TWhile1 : forall l Γ pc e c,
  {{ Γ ⊢ e : l }} ->
  -{ Γ, pc ⊔ l ⊢ c ~> Γ }- ->
  -{ Γ, pc ⊢ (CWhile e c) ~> Γ }-

(* Does change the environment *)
| TWhile2 : forall l Γ pc e c Γ' Γ'',
  {{ Γ ⊢ e : l }} ->
  -{ Γ, pc ⊔ l ⊢ c ~> Γ'' }- ->
  -{ Γ'', pc ⊢ (CWhile e c) ~> Γ' }- ->
  -{ Γ, pc ⊢ (CWhile e c) ~> Γ' }-

| TInput : forall Γ pc x ch Γ',
  (pc ⊑ confidentiality_of_channel ch) ->
  Γ' = <[ x := ((confidentiality_of_channel ch) ⊔ pc) ]> Γ ->
  -{ Γ, pc ⊢ (CInput ch x) ~> Γ' }-

| TOutput : forall le Γ pc e ch,
  {{ Γ ⊢ e : le }} ->
  ((pc ⊔ le) ⊑ confidentiality_of_channel ch) ->
  -{ Γ, pc ⊢ (COutput ch e) ~> Γ }-
where "-{ Γ ',' pc '⊢' e '~>' Γ2 }-" := (typecheck Γ pc e Γ2)
.


(** Examples *)
Definition example_typecheck example := exists gamma, -{ ∅ , LPublic ⊢ example ~> gamma}-.
(* /* Program 1 -- should be well-typed as it satisfies PINI (and PSNI) */ *)
(* input(secret, x) *)
(* x = 0 *)
(* output(public, x) *)
Definition example1 :=
 (INPUT "x" @Secret) ;;;
   ("x" ::= 0) ;;;
   (OUTPUT "x" @Public).

Lemma example1_typecheck : example_typecheck example1.
Proof.
  eexists.
  repeat econstructor.
Qed.

(* /* Program 2 -- must be ill-typed as it violates PINI */ *)
(* input(secret, x) *)
(* output(public, x) *)
Definition example2 :=
  (INPUT "x" @Secret) ;;; (OUTPUT "x" @Public).
Lemma example2_not_typecheck : not (example_typecheck example2).
Proof.
  intro.
  inversion H.
  inversion H0; subst.
  inversion H5; subst.
  inversion H7; subst.
  inversion H8; subst.
  inversion H3; subst.
  cbn in H10.
  assumption.
Qed.

(* /* Program 3 -- must be ill-typed because of the implicit flow */ *)
(* input(secret, x) *)
(* y = 0 *)
(* if x then *)
(* y = 1 *)
(* else *)
(* skip *)
(* output(public, y) *)

Definition example3 :=
  INPUT "x" @Secret ;;;
  "y" ::= 0 ;;;
  IFB "x" THEN "y" ::= 1 ELSE SKIP FI ;;;
  OUTPUT "y" @Public.

Lemma example3_not_typecheck : not (example_typecheck example3).
Proof.
  intro.
  inversion H;subst.
  inversion H0;subst.
  inversion H5;subst. clear H5 H6.
  inversion H7;subst. clear H7.
  inversion H5;subst; clear H5.
  inversion H6;subst; clear H6.
  inversion H8;subst; clear H8.
  inversion H5;subst; clear H5.
  inversion H4;subst.
  cbn in H3; inversion H3 ; subst ; clear H3.
  inversion H4;subst; clear H4.
  cbn in H3; inversion H3 ; subst ; clear H3.
  inversion H11;subst; clear H11.
  inversion H9;subst; clear H9.
  inversion H7;subst; clear H7.
  cbn in *.
  inversion H6;subst.
  cbn in H3; inversion H3 ; subst ; clear H3.
  inversion H5;subst.
  by cbn in H9.
Qed.

(* /* Program 4 -- should be well-typed as it satisfies PINI (and PSNI) */ *)
(* input(secret, x) *)
(* if x then *)
(* y = 1 *)
(* else *)
(* skip *)
(* output(secret, y) *)
(* y = 0 *)
(* output(public, y) *)
Definition example4 :=
  INPUT "x" @Secret ;;;
  IFB "x" THEN "y" ::= 1 ELSE SKIP FI ;;;
  OUTPUT "y" @Secret ;;;
  "y" ::= 0 ;;;
  OUTPUT "y" @Public.
Lemma example4_typecheck : example_typecheck example4.
Proof.
  repeat econstructor.
Qed.

(* /* Program 5 -- should be well-typed as it satisfies PINI */ *)
(* input(secret, x) *)
(* while x do *)
(*    x = x - 1 *)
(*    input(secret, y) *)
(* output(public, 0) *)
Definition example5 :=
  INPUT "x" @Secret ;;;
  ( WHILE "x"
      DO
      "x" ::= (EOp "x" Sub 1);;;
      INPUT "y" @Secret
      END
  ) ;;;
  OUTPUT 0 @Public.

Lemma example5_typecheck : example_typecheck example5.
Proof.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  eauto.
  econstructor.
  eapply TWhile2.
  all : (repeat econstructor).
  cbn.
  by repeat (symmetry; map_simpl).
Qed.

(* /* Program 6 -- must be ill-typed as it violates PINI */ *)
(* input(secret, x) *)
(* while x do *)
(* x = x - 1 *)
(* input(secret, y) *)
(* output(public, x) *)
Definition example6 :=
    INPUT "x" @Secret ;;;
    ( WHILE "x"
        DO
        "x" ::= (EOp "x" Sub 1);;;
        INPUT "y" @Secret
        END
    ) ;;;
    OUTPUT "x" @Public.
Lemma example6_typecheck : not (example_typecheck example6).
Proof.
  intro.
  inversion H;subst.
  inversion H0;subst; clear H0.
  inversion H5;subst; cbn in H4; clear H5 H4; cbn in *.
  inversion H7;subst; clear H7.
  inversion H6;subst; clear H6.

  inversion H4;subst; clear H4.
  - inversion H9;subst; clear H9.
    inversion H4;subst; clear H4.
    inversion H7;subst; clear H7.
    inversion H10;subst; clear H10.
    inversion H5;subst; clear H5.
    inversion H6;subst; clear H6.
    inversion H4;subst; clear H4.
    inversion H11;subst; clear H11.
    cbn in *. inversion H3; inversion H5 ; subst.
    cbn in H2; inversion H2; subst.
    by cbn in H8.
  - admit.
Admitted.

(* /* Program 7 -- must be well-typed  */ *)
(* input(secret, x) *)
(* input(public, x) *)
(* output(public, x) *)
Definition example7 :=
  INPUT "x" @Secret ;;;
  INPUT "x" @Public ;;;
  OUTPUT "x" @Public
  .
Lemma example7_typecheck : example_typecheck example7.
Proof.
  repeat econstructor.
Qed.


(* /* Program 8 -- must be ill-typed  */ *)
(* input(public, x); *)
(* while x: *)
(*   output(public, x); *)
(*   input(secret, x) *)

Definition example8 :=
  INPUT "x" @Public ;;;
  ( WHILE "x"
      DO
      OUTPUT "x" @Public;;;
      INPUT "x" @Secret
      END
  ).
Lemma example8_typecheck : not (example_typecheck example8).
Proof.
Admitted.

(* Inductive pevent : Type := *)
(* | EmptyEvent *)
(* | AssignEvent (x : var) (v : value) *)
(* | InputEvent (v : value) *)
(* | OutputEvent (v : value) *)
(* . *)

(* Inductive event_step : state -> context -> confidentiality -> pevent -> state -> context -> confidentiality -> Prop:= *)
(* | PSkip : forall S P m t gamma pc, *)
(*   exec_command (S, P, Some CSkip, m, t) (S, P, None, m, t) -> *)
(*   event_step (S, P, Some CSkip, m, t) gamma pc EmptyEvent (S, P, None, m, t) gamma pc *)

(* | PAssignPublic : forall S P x e v m t gamma pc gamma' l, *)
(*   exec_command (S, P, Some (CAssign x e), m, t) (S, P, None, set_var x v m, t) -> *)
(*   eval_expr e m v -> *)
(*   find_var x gamma = Some l -> (* We REQUIRE that x has the right label *) *)
(*   gamma' = set_var x (l ⊔ pc) gamma -> *)
(*   event_step (S, P, Some (CAssign x e), m, t) gamma pc *)
(*     (AssignEvent x v) (S, P, None, set_var x v m, t) gamma' pc *)

(* (* TODO When doing the sequence, the level of the pc never change... *)
(*    Only when we enter enter in a block, but seq stays at the same level *) *)
(* | PSeq1 : forall S P c1 c2 m t S' P' c1' m' t' ev gamma pc gamma', *)
(*   exec_command (S, P, Some (CSeq c1 c2), m, t) (S', P', Some (CSeq c1' c2), m', t') -> *)
(*   event_step *)
(*     (S, P, Some c1, m, t) gamma pc *)
(*     ev *)
(*     (S', P', Some c1', m', t') gamma' pc -> *)
(*   event_step *)
(*     (S, P, Some (CSeq c1 c2), m, t) gamma pc *)
(*     ev *)
(*     (S', P', Some (CSeq c1' c2), m', t') *)
(*     gamma' pc *)

(* | PSeq2 : forall S P c1 c2 m t S' P' m' t' ev gamma gamma' pc, *)
(*   exec_command (S, P, Some (CSeq c1 c2), m, t) (S', P', Some c2, m', t') -> *)
(*   event_step (S, P, Some c1, m, t) gamma pc ev (S', P', None, m', t') gamma' pc -> *)
(*   event_step (S, P, Some (CSeq c1 c2), m, t) gamma pc ev (S', P', Some c2, m', t') gamma' pc *)

(* | PIf : forall S P e (c1 : command) c2 m t v (c: command) l gamma pc, *)
(*   exec_command *)
(*     (S, P, Some (CIfThenElse e c1 c2), m, t) *)
(*     (S, P, Some c, m, t) -> *)
(*   eval_expr e m v -> *)
(*   typecheck_expr gamma e l -> *)
(*   c = (if Nat.eqb v 0 then c2 else c1) -> *)
(*   event_step *)
(*     (S, P, Some (CIfThenElse e c1 c2), m, t) gamma pc *)
(*     EmptyEvent *)
(*     (S, P, Some c, m, t) gamma (pc ⊔ l) *)

(* | PWhile : forall S P e c m t, *)
(*   exec_command *)
(*     (S, P, Some (CWhile e c), m, t) *)
(*     (S, P, Some (CIfThenElse e (CSeq c (CWhile e c)) CSkip), m, t) -> *)
(*   event_step *)
(*     (S, P, Some (CWhile e c), m, t) *)
(*     EmptyEvent *)
(*     (S, P, Some (CIfThenElse e (CSeq c (CWhile e c)) CSkip), m, t) *)

(* | PInputPublic : forall S v P x m t, *)
(*   exec_command *)
(*     (S, Streams.Cons v P, Some (CInput Public x), m, t) *)
(*     (S, P, None, set_var x v m, EvInput Public v :: t) -> *)
(*   event_step *)
(*     (S, Streams.Cons v P, Some (CInput Public x), m, t) *)
(*     (InputEvent v) *)
(*     (S, P, None, set_var x v m, EvInput Public v :: t) *)

(* | PInputSecret : forall v S P x m t, *)
(*   exec_command *)
(*     (Streams.Cons v S, P, Some (CInput Secret x), m, t) *)
(*     (S, P, None, set_var x v m, EvInput Secret v :: t) -> *)
(*   event_step *)
(*     (Streams.Cons v S, P, Some (CInput Secret x), m, t) *)
(*     EmptyEvent *)
(*     (S, P, None, set_var x v m, EvInput Secret v :: t) *)

(* | POutputPublic : forall S P e m t v, *)
(*   exec_command (S, P, Some (COutput Public e), m, t) (S, P, None, m, EvOutput Public v :: t) -> *)
(*   eval_expr e m v -> *)
(*   event_step (S, P, Some (COutput Public e), m, t) (OutputEvent v) *)
(*     (S, P, None, m, EvOutput Public v :: t) *)

(* | POutputSecret : forall S P e m t v, *)
(*   exec_command (S, P, Some (COutput Secret e), m, t) (S, P, None, m, EvOutput Secret v :: t) -> *)
(*   eval_expr e m v -> *)
(*   event_step (S, P, Some (COutput Secret e), m, t) EmptyEvent (S, P, None, m, EvOutput Secret v :: t) *)
(* . *)

(* Lemma exec_command_iff_event_step : *)
(*   forall st st', exec_command st st' <-> exists ev, event_step st ev st'. *)
(* Proof. *)
(*   intros; split;intros; cycle 1. *)
(*   - destruct H; induction H; assumption. *)
(*   - induction H; try (eexists; (econstructor; eauto); (econstructor; eauto)). *)
(*     + destruct IHexec_command as [ev IHexec_command]. *)
(*       exists ev ; (econstructor; auto) ; (econstructor; auto). *)
(*     + destruct IHexec_command as [ev IHexec_command]. *)
(*       exists ev ; (econstructor; auto) ; (econstructor; auto). *)
(*     + destruct ch; (eexists; (econstructor; eauto); (econstructor; eauto)). *)
(* Qed. *)

(* Attempt at defining a statement that intertwines execution and typechecking *)
(* Reserved Notation "cfg gamma pc '===>' cfg' gamma' pc'" (at level 10). *)
Inductive exec_with_gamma : config -> context -> confidentiality -> config -> context -> confidentiality -> Prop :=
| GSkip : forall st Γ pc,
  exec_with_gamma
      (⟪ Some SKIP, st ⟫) Γ pc
      (⟪ None , st ⟫) Γ pc

| GAssign : forall S P x e v m t Γ pc l Γ',
  e ; m ⇓ v ->
  {{ Γ ⊢ e : l }} ->
  Γ' = <[ x := l ⊔ pc ]> Γ ->
  exec_with_gamma
    (⟪ Some (x ::= e), (S, P, m, t) ⟫) Γ pc
    (⟪ None, (S, P, <[ x := v ]> m, t) ⟫) Γ' pc

| GSeq1 : forall st c1 c2 st' c1' Γ pc Γ' pc',
    exec_with_gamma
      (⟪ Some c1, st ⟫) Γ pc
      (⟪ Some c1', st' ⟫) Γ' pc'
    ->
    exec_with_gamma
      (⟪ Some (c1 ;;; c2), st ⟫) Γ pc
      (⟪ Some (c1' ;;; c2), st' ⟫) Γ' pc' (* Should this last one be pc? pc'? *)

| GSeq2 : forall st c1 c2 st' Γ pc Γ' pc' ,
    exec_with_gamma
      (⟪ Some c1, st ⟫) Γ pc
      (⟪ None, st' ⟫) Γ' pc'
    ->
    exec_with_gamma
      (⟪ Some (c1 ;;; c2), st ⟫) Γ pc
      (⟪ Some c2, st' ⟫) Γ' pc'
      (* This should not be pc', since we are done with c1 and should revert to what we had before *)

| GIf : forall S P e (c1 c2 : command) m t v (c: command) Γ pc l,
  e ; m ⇓ v ->
  {{ Γ ⊢ e : l }} ->
  c = (if Nat.eqb v 0 then c2 else c1) ->
  exec_with_gamma
      (⟪ Some (IFB e THEN c1 ELSE c2 FI),  (S, P, m, t)⟫) Γ pc
      (⟪ Some c,  (S, P, m, t)⟫) Γ (pc ⊔ l)

| GWhile : forall st e c Γ pc,
    exec_with_gamma
      (⟪ Some (WHILE e DO c END), st ⟫) Γ pc
      (⟪ Some (IFB e THEN (c ;;; WHILE e DO c END) ELSE SKIP FI), st ⟫) Γ pc

| GInputPublic : forall S v P x m t Γ pc Γ',
    Γ' = <[ x := pc ]> Γ ->
    exec_with_gamma
      (⟪ Some (INPUT x @Public), (S, v::::P, m, t) ⟫) Γ pc
      (⟪ None, (S, P, <[x := v ]> m, EvInput Public v :: t) ⟫) Γ' pc

| GInputSecret : forall S v P x m t Γ pc Γ',
    Γ' = <[ x := LSecret ]> Γ ->
    exec_with_gamma
      (⟪ Some (INPUT x @Secret), (v::::S, P, m, t) ⟫) Γ pc
      (⟪ None, (S, P, <[x := v ]> m, EvInput Secret v :: t) ⟫) Γ' pc

| GOutput : forall S P ch e m t v Γ pc,
  e ; m ⇓ v ->
    exec_with_gamma
      (⟪ Some (OUTPUT e @ch), (S, P, m, t) ⟫) Γ pc
      (⟪ None, (S, P, m, EvOutput ch v :: t) ⟫) Γ pc
.

Inductive exec_with_gamma_trans : config -> context -> confidentiality -> config -> context -> confidentiality -> Prop :=
| Gexec_empty : forall s gamma pc, exec_with_gamma_trans s gamma pc s gamma pc
| Gexec_step : forall s1 gamma1 pc1 s2 gamma2 pc2 s3 gamma3 pc3,
    exec_with_gamma s1 gamma1 pc1 s2 gamma2 pc2 ->
    exec_with_gamma_trans s2 gamma2 pc2 s3 gamma3 pc3 ->
    exec_with_gamma_trans s1 gamma1 pc1 s3 gamma3 pc3
.


(* Two memories have the same values for the public variables *)
Definition agree_on_public (Γ : context) (m1 m2 : memory) : Prop :=
  forall x,
    match m1 !! x, m2 !! x, Γ !! x with
    | Some v1, Some v2, Some LPublic => v1 = v2
    | _, _, Some LSecret => True
    | None, None, None => True
    | _, _, _ => False
    end
.

(* If a memory agrees on public variable values, all public expressions evaluated in it
   are equal *)
 Lemma eval_expr_public gamma e m1 m2 v1 v2:
   typecheck_expr gamma e LPublic ->
   agree_on_public gamma m1 m2 ->
   eval_expr e m1 v1 ->
   eval_expr e m2 v2 ->
   v1 = v2.
 Proof.
   generalize dependent v1. generalize dependent v2.
   induction e; intros v2 v1 Ht Hagree Hv1 Hv2.
   - inversion Hv1; subst. inversion Hv2; subst. done.
   - inversion Hv1; subst. inversion Hv2; subst. inversion Ht; subst.
     specialize (Hagree s). rewrite H0 H1 H3 in Hagree. done.
   - inversion Hv1; subst. inversion Hv2; subst.
     inversion Ht; subst. destruct l1 => //. destruct l2 => //.
     rewrite (IHe1 v1 v0 H3 Hagree H4 H6).
     rewrite (IHe2 _ _ H9 Hagree H5 H7). done.
 Qed.


(* executing implies executing with gammas *)
Lemma can_exec_with_gamma Γ0 pc0 P0 S0 c0 m0 t0 s1 :
  same_support m0 Γ0 ->
  (⟪ c0 , (P0, S0, m0, t0) ⟫) ---> s1 ->
  exists Γ1 pc1,
    exec_with_gamma
      (⟪ c0 , (P0, S0, m0, t0) ⟫) Γ0 pc0
      s1 Γ1 pc1.
Proof.
  intros Hwf Hstep.
  destruct c0 as [c0|]; [|by inversion Hstep].
  induction Hstep; subst
  ; try ( eexists _,_; econstructor ; eauto; done).
  - admit.
    (* destruct H6. *)
    (* + exists (<[ x := pc0 ]> Γ0), pc0. *)
    (*   repeat econstructor. by destruct pc0 ; cbn. *)
    (* + admit. (* need more information about m *) *)
    (* + admit. *)
  - destruct IHHstep as (Γ1 & pc1 & IH).
    eexists _,_; econstructor ; eauto.
  - destruct IHHstep as (Γ1 & pc1 & IH).
    eexists _,_; econstructor ; eauto.
  - (* need more information about m *)
    admit.
Admitted.

(* executing implies executing with gammas *)
Lemma can_exec_with_gamma_trans Γ0 pc0 P0 S0 c0 m0 t0 s1 :
  same_support m0 Γ0 ->
  (⟪ c0 , (P0, S0, m0, t0) ⟫) --->* s1 ->
  exists Γ1 pc1,
    exec_with_gamma_trans
      (⟪ c0 , (P0, S0, m0, t0) ⟫) Γ0 pc0
      s1 Γ1 pc1.
Proof.
  intros Hwf Hstep.
  induction Hstep.
  - eexists; eexists; econstructor.
  - destruct IHHstep as (Γ1 & pc1 & IH).
    (* destruct x,st. as (S & P & m & t). *)
    destruct x,st,p,p.
    eapply can_exec_with_gamma in Hwf.
    + admit.
    + admit.
Admitted.

Lemma type_preservation :
  forall c gamma pc gammaf gamma' P S m t P' S' c' m' t' pc',
  -{ gamma, pc ⊢ c ~> gammaf }- ->
  exec_with_gamma
    (⟪ Some c , (S, P, m, t) ⟫) gamma pc
    (⟪ c' , (S', P', m', t') ⟫) gamma' pc' ->
  match c' with
  | Some c' => -{ gamma', pc' ⊢ c' ~> gammaf }-
  | None => gamma' = gammaf
  end .
Proof.
  induction c; intros gamma pc gammaf gamma' P S m t P' S' c' m' t' pc' Ht Hex;
    inversion Hex; subst => //.
  - inversion Ht; subst. done.
  - inversion Ht; subst. replace l with le => //.
    admit.
  - inversion Ht; subst.
    (* specialize (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3). *)
    (* eapply TSeq. exact IHc1. *)

(* For the end of this proof to work, we need to tweak our definition of
   exec_with_gamma *)


(* exact H5.
  - inversion Ht; subst.
    specialize (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 H14) as ->. done.
  - inversion Ht; subst.
    destruct (Nat.eqb v 0) eqn:Hv => //.
    + specialize (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H16). *)

Admitted.



(*
Lemma type_preservation :
  forall c gamma pc gammaf gamma' P S m t P' S' c' m' t' pc',
  typecheck gamma pc c gammaf ->
  exec_with_gamma (P, S, Some c, m, t) gamma pc (P', S', Some c', m', t') gamma' pc' ->
  typecheck gamma' pc c' gammaf.
Proof.
  induction c; intros gamma pc gammaf gamma' P S m t P' S' c' m' t' pc' Ht Hex;
    inversion Hex; subst => //.
  - inversion Ht; subst.
    specialize (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 H14).
    eapply TSeq. exact IHc1. exact H5.
  - inversion Ht; subst.

Admitted. *)

(* One can separate an execution into its last event, everything that happens before,
and everything that happens after *)
Lemma separate_last_event S0 P0 c0 m0 t0 gamma0 pc0 S1 P1 c1 m1 a t1 gamma1 pc1 :
  exec_with_gamma_trans
    (⟪ Some c0 , (S0, P0, m0, t0) ⟫) gamma0 pc0
    (⟪ c1 , (S1, P1, m1, a::t1) ⟫) gamma1 pc1 ->
  exists S2 P2 c2 m2 gamma2 pc2 S3 P3 c3 m3 gamma3 pc3,
    exec_with_gamma_trans
    (⟪ Some c0 , (S0, P0, m0, t0) ⟫) gamma0 pc0
    (⟪ Some c2 , (S2, P2, m2, t1) ⟫) gamma2 pc2
    /\ exec_with_gamma
        (⟪ Some c2 , (S2, P2, m2, t1) ⟫) gamma2 pc2
        (⟪ c3 , (S3, P3, m3, a::t1) ⟫) gamma3 pc3
    /\ exec_with_gamma_trans
        (⟪ c3 , (S3, P3, m3, a::t1) ⟫) gamma3 pc3
        (⟪ c1 , (S1, P1, m1, a::t1) ⟫) gamma1 pc1.
Proof.
Admitted.

(* Same as the previous lemma, but with public events only *)
Lemma separate_last_public_event S0 P0 c0 m0 t0 gamma0 pc0 S1 P1 c1 m1 t1 a d gamma1 pc1:
  exec_with_gamma_trans
    (⟪ Some c0 , (S0, P0, m0, t0) ⟫) gamma0 pc0
    (⟪ c1 , (S1, P1, m1, t1) ⟫) gamma1 pc1 ->
  public_projection t1 = a :: d ->
  exists S2 P2 c2 m2 t2 gamma2 pc2 S3 P3 c3 m3 gamma3 pc3,
    exec_with_gamma_trans
    (⟪ Some c0 , (S0, P0, m0, t0) ⟫) gamma0 pc0
    (⟪ Some c2 , (S2, P2, m2, t2) ⟫) gamma2 pc2
    /\ public_projection t2 = d
    /\ exec_with_gamma
        (⟪ Some c2 , (S2, P2, m2, t2) ⟫) gamma2 pc2
        (⟪ c3 , (S3, P3, m3, a::t2) ⟫) gamma3 pc3
    /\ exec_with_gamma_trans
        (⟪  c3 , (S3, P3, m3, a::t2) ⟫) gamma3 pc3
        (⟪ c1 , (S1, P1, m1, t1) ⟫) gamma1 pc1.
Proof.
Admitted.

(* One can add a public event to both sides of a public projection *)
Lemma public_projection_cons t a d t' d':
  public_projection t = a :: d ->
  public_projection t' = d' ->
  public_projection (a :: t') = a :: d'.
Proof.
  intros Ht Ht'.
  induction t => //.
  destruct a0, c; simpl in Ht.
  inversion Ht; subst => //=.
  by apply IHt.
  inversion Ht; subst => //=.
  by apply IHt.
Qed.



Lemma list_is_finite {A} (a : A) l : l = a :: l -> False.
Proof.
  generalize dependent a. induction l => //=. intros. inversion H. by apply (IHl a0).
Qed.


(* if c executes to Some c', then it cannot execute to None *)
Lemma exec_both_some S1 P1 c m1 t1 gamma1 pc1 S1' P1' c1' m1' t1' gamma1' pc1'
  S2 P2 m2 t2 gamma2 pc2 S2' P2' c2' m2' t2' gamma2' pc2':
  exec_with_gamma
    (⟪ Some c , (S1, P1, m1, t1) ⟫) gamma1 pc1
    (⟪ c1' , (S1', P1', m1', t1') ⟫) gamma1' pc1' ->

  exec_with_gamma
    (⟪ Some c , (S2, P2, m2, t2) ⟫) gamma2 pc2
    (⟪ c2' , (S2', P2', m2', t2') ⟫) gamma2' pc2' ->

  match c1', c2' with | Some _, Some _ | None, None => True | _,_ => False end.
Proof.
  intros Hex1 Hex2.
  inversion Hex1; subst;
    inversion Hex2; subst => //.
Qed.

Lemma set_var_agree gamma (m1 m2 : memory) x v l :
  agree_on_public gamma m1 m2 ->
  agree_on_public (<[ x := l ]> gamma)
    (<[ x := v ]> m1)
    (<[ x := v ]> m2).
Proof.
  unfold agree_on_public.
  intros Hagree y.
  destruct (x =? y) eqn:Hxy.
  - apply String.eqb_eq in Hxy as ->.
    simpl_map; by destruct l.
  - apply String.eqb_neq in Hxy.
    repeat (rewrite lookup_insert_ne => //).
    apply Hagree.
Qed.

(* If a step produces a public event, then it is observationally deterministic *)
Lemma public_event_is_same :
  forall c gamma pc gamma' t1 t2 d a1 a2 S1 P m1 S1' P1' c1' m1' gamma1 pc1
    S2 m2 S2' P2' c2' m2' gamma2 pc2,
  typecheck gamma pc c gamma' ->
  public_projection t1 = d ->
  public_projection t2 = d ->
  public_projection (a1 :: t1) = a1 :: d ->
  public_projection (a2 :: t2) = a2 :: d ->
  agree_on_public gamma m1 m2 ->
  exec_with_gamma
    (⟪ Some c , (S1, P, m1, t1) ⟫) gamma pc
    (⟪ c1' , (S1', P1', m1', a1 :: t1) ⟫) gamma1 pc1 ->
  exec_with_gamma
    (⟪ Some c , (S2, P, m2, t2) ⟫) gamma pc
    (⟪ c2' , (S2', P2', m2', a2:: t2) ⟫) gamma2 pc2 ->
  gamma1 = gamma2 /\ pc1 = pc2 /\ P1' = P2' /\ c1' = c2' /\ agree_on_public gamma1 m1' m2' /\ a1 = a2.
Proof.
  induction c;
    intros gamma pc gamma' t1 t2 d a1 a2 S1 P m1 S1' P1' c1' m1' gamma1 pc1 S2 m2
    S2' P2' c2' m2' gamma2 pc2 Ht Ht1 Ht2 Ha1 Ha2 Hmem Hex1 Hex2;
    try by inversion Hex1; subst; exfalso; apply (list_is_finite a1 t1).
  - inversion Hex1; subst.
    + inversion Hex2; subst.
      * inversion Ht.
        assert (public_projection t1 = public_projection t1) as Htriv => //.
        edestruct (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                     H3 Htriv Ht2 Ha1 Ha2 Hmem H8 H9)
          as (-> & -> & -> & ? & ? & ->).
        inversion H6; subst. by repeat split.
      * eapply exec_both_some in H8; try exact H9. done.
    + inversion Hex2; subst.
      * eapply exec_both_some in H8; try exact H9. done.
      * inversion Ht.
        assert (public_projection t1 = public_projection t1) as Htriv => //.
        edestruct (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                     H3 Htriv Ht2 Ha1 Ha2 Hmem H8 H9)
          as (-> & -> & -> & ? & ? & ->).
        done.
  - inversion Hex1; subst.
    + inversion Hex2; subst. repeat split => //.
      by apply set_var_agree.
    + by apply list_is_finite in Ha1.
  - inversion Hex1; subst.
    inversion Hex2; subst. repeat split => //.
    destruct c.
    + inversion Ht; subst. destruct pc2 => //. destruct le => //.
      replace v0 with v => //.
      eapply eval_expr_public.
      exact H3. exact Hmem. done. done.
    + by apply list_is_finite in Ha1.
Qed.

Lemma public_projection_is_public_input t v d :
  public_projection t = EvInput Secret v :: d -> False.
Proof.
  induction t => //=. destruct a, c => //=.
Qed.

Lemma public_projection_is_public_output t v d :
  public_projection t = EvOutput Secret v :: d -> False.
Proof.
  induction t => //=. destruct a, c => //=.
Qed.

Lemma public_projection_inj a t d :
  public_projection (a :: t) = a :: d ->
  public_projection t = d.
Proof.
  destruct a => //=; destruct c => //=.
  intro H; by inversion H.
  intro H; by apply public_projection_is_public_input in H.
  intro H; by inversion H.
  intro H; by apply public_projection_is_public_output in H.
Qed.

(* for any two runs, if the initial state is the same except possibly for the stream
   of secret inputs, then for all integers n, the state of the program right before the
   nth public event is observationally the same *)
Lemma identical_after_nth_public_event :
  forall d1 a1 a2 d2 c gamma Sinit1 P S1 P1 c1 m1 t1 gamma1 pc1 S1' P1' c1' m1' gamma1' pc1'
    Sinit2 S2 P2 c2 m2 t2 gamma2 pc2 S2' P2' c2' m2' gamma2' pc2',
    length d1 = length d2 ->
    -{ gamma0 , LPublic ⊢ c ~> gamma }- ->
    (* typecheck gamma0 LPublic c gamma -> *)
    exec_with_gamma_trans
      (⟪ Some c , (Sinit1, P, minit, []) ⟫) gamma0 LPublic
      (⟪ Some c1 , (S1, P1, m1, t1) ⟫) gamma1 pc1 ->
    public_projection t1 = d1 ->
    exec_with_gamma
      (⟪ Some c1 , (S1, P1, m1, t1) ⟫) gamma1 pc1
      (⟪ c1' , (S1', P1', m1', a1 :: t1) ⟫) gamma1' pc1' ->
    public_projection (a1 :: t1) = a1 :: d1 ->
    exec_with_gamma_trans
      (⟪ Some c , (Sinit2, P, minit, []) ⟫) gamma0 LPublic
      (⟪ Some c2 , (S2, P2, m2, t2) ⟫) gamma2 pc2 ->
    public_projection t2 = d2 ->
    exec_with_gamma
      (⟪ Some c2 , (S2, P2, m2, t2) ⟫) gamma2 pc2
      (⟪ c2' , (S2', P2', m2', a2 :: t2) ⟫) gamma2' pc2' ->
    public_projection (a2 :: t2) = a2 :: d2 ->
    gamma1 = gamma2 /\ pc1 = pc2 /\ P1 = P2 /\ c1 = c2 /\ agree_on_public gamma1 m1 m2 /\ a1 = a2 /\ d1 = d2.
Proof.
  induction d1.
  - intros a1 a2 d2 c gamma Sinit1 P S1 P1 c1 m1 t1 gamma1 pc1 S1' P1' c1' m1' gamma1' pc1'
      Sinit2 S2 P2 c2 m2 t2 gamma2 pc2 S2' P2' c2' m2' gamma2' pc2'
      Hlen Ht Hex1 Ht1 Hex1' Ha1 Hex2 Ht2 Hex2' Ha2.
    destruct d2 => //.
    admit.
  - intros a1 a2 d2 c gamma Sinit1 P S1 P1 c1 m1 t1 gamma1 pc1 S1' P1' c1' m1' gamma1' pc1'
      Sinit2 S2 P2 c2 m2 t2 gamma2 pc2 S2' P2' c2' m2' gamma2' pc2'
      Hlen Ht Hex1 Ht1 Hex1' Ha1 Hex2 Ht2 Hex2' Ha2.
    destruct d2 => //.
    destruct (separate_last_public_event _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hex1 Ht1)
      as (S1m & P1m & c1m & m1m & t1m & gamma1m & pc1m &
            S1p & P1p & c1p & m1p & gamma1p & pc1p & Hex1m & Ht1m & Hex1c & Hex1p).
    destruct (separate_last_public_event _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hex2 Ht2)
      as (S2m & P2m & c2m & m2m & t2m & gamma2m & pc2m &
            S2p & P2p & c2p & m2p & gamma2p & pc2p & Hex2m & Ht2m & Hex2c & Hex2p).
    inversion Hlen.
    specialize (IHd1 a e d2 c gamma Sinit1 P S1m P1m c1m m1m t1m gamma1m pc1m
                  S1p P1p c1p m1p gamma1p pc1p
                  Sinit2 S2m P2m c2m m2m t2m gamma2m pc2m S2p P2p c2p m2p gamma2p pc2p
                  H0 Ht Hex1m Ht1m Hex1c (public_projection_cons _ _ _ _ _ Ht1 Ht1m)
                  Hex2m Ht2m Hex2c (public_projection_cons _ _ _ _ _ Ht2 Ht2m)
               ) as (-> & -> & -> & -> & Hmem & -> & ->).
    specialize (public_projection_inj _ _ _ Ha2) as He.
    specialize (public_projection_inj _ _ _ Ha1) as Ha.
    edestruct public_event_is_same as (? & ? & ? & ? & ? & ?).
    admit.
(*    exact Ht1m. exact Ht2m. exact Ha1. exact Ha2. exact Hmem. exact Hex1c. *)
Admitted.






Lemma typecheck_is_sound :
  forall c gamma, typecheck gamma0 LPublic c gamma -> PINI c.
Proof.
  intros c gamma Ht.
  unfold PINI.
  intros P a d t Had.
  split.
  { intro Hk.
    apply PKnow. inversion Hk; subst.
    destruct H as (S' & P' & c' & m' & t' & H).
    exists S', P', c', m', t', a.
    exact H. }
  intro Hpk.
  apply Know.
  inversion Hpk; subst.
  destruct H as (S' & P' & c' & m' & t' & a0 & Hexec & Hp0).
  destruct Had as (S0 & S1 & P1 & c1 & m1 & Hexec0 & Hp).
  replace a with a0. exists S', P',c', m', t'. split => //.
  apply (can_exec_with_gamma_trans gamma0 LPublic) in Hexec0 as (gamma1 & pc1 & Hexec0);
    last done.
  destruct (separate_last_public_event _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec0 Hp)
    as (S1m & P1m & c1m & m1m & t1m & gamma1m & pc1m &
          S1p & P1p & c1p & m1p & gamma1p & pc1p & Hex1m & Ht1m & Hex1c & Hex1p).
  apply (can_exec_with_gamma_trans gamma0 LPublic) in Hexec as (gamma2 & pc2 & Hexec);
    last done.
  destruct (separate_last_public_event _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec Hp0)
    as (S2m & P2m & c2m & m2m & t2m & gamma2m & pc2m &
          S2p & P2p & c2p & m2p & gamma2p & pc2p & Hex2m & Ht2m & Hex2c & Hex2p).
  symmetry.
  eapply (identical_after_nth_public_event d a a0 d).
  done.
  exact Ht.
  exact Hex1m.
  exact Ht1m.
  exact Hex1c.
  by apply (public_projection_cons _ _ _ _ _ Hp Ht1m).
  exact Hex2m.
  exact Ht2m.
  exact Hex2c.
  by apply (public_projection_cons _ _ _ _ _ Hp0 Ht2m).
Qed.
