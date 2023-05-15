
Require Import String.
From Coq Require Import Streams.
From Coq Require Import Lists.List.
Open Scope string_scope.
Require Import ssreflect.


Inductive op :=
| Add | Sub | Mul | Eq | Neq | Leq | Lt | Geq | Gt.

Definition var := string.
Definition value := nat.

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


(* This type will be used for both memories and contexts *)
Inductive varmap (A : Type) :=
| Empty : varmap A
| Cons : var -> A -> varmap A -> varmap A
.



Fixpoint find_var {A} x (m : varmap A) :=
  match m with
  | Empty _ => None
  | Cons _ y v m => if String.eqb y x then Some v else find_var x m
  end.

Fixpoint find_and_remove {A} x (m : varmap A) :=
  match m with
  | Empty _ => None
  | Cons _ y v m => if String.eqb y x then Some (v, m) else
                     match find_and_remove x m with
                     | None => None
                     | Some (vx, m) => Some (vx, Cons _ y v m)
                     end
  end.

Fixpoint set_var {A} x (v : A) m :=
  match m with
  | Empty _ => Cons _ x v m
  | Cons _ y vy m => if String.eqb y x then Cons _ x v m else Cons _ y vy (set_var x v m)
  end.



Definition memory := varmap value.


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
| Var : forall x m v, find_var x m = Some v -> eval_expr (EVar x) m v
| Op : forall e1 op e2 v1 v2 m, eval_expr e1 m v1 -> eval_expr e2 m v2 ->
                           eval_expr (EOp e1 op e2) m (apply_op v1 op v2)
.

Inductive event :=
| EvInput : channel -> value -> event
| EvOutput : channel -> value -> event.
Definition trace := list event.
(* In the state, Some c represents a command, and None represents a Skip *)
Definition state : Type := (Stream value) * (Stream value) * (option command) * memory * trace.


Inductive exec_command : state -> state -> Prop :=
| Skip : forall S P m t,
    exec_command (S, P, Some CSkip, m, t) (S, P, None, m, t)
| Assign : forall S P x e v m t,
    eval_expr e m v ->
    exec_command (S, P, Some (CAssign x e), m, t) (S, P, None, set_var x v m, t)
| Seq1 : forall S P c1 c2 m t S' P' c1' m' t',
    exec_command (S, P, Some c1, m, t) (S', P', Some c1', m', t') ->
    exec_command (S, P, Some (CSeq c1 c2), m, t) (S', P', Some (CSeq c1' c2), m', t')
| Seq2 : forall S P c1 c2 m t S' P' m' t',
    exec_command (S, P, Some c1, m, t) (S', P', None, m', t') ->
    exec_command (S, P, Some (CSeq c1 c2), m, t) (S', P', Some c2, m', t')
| If : forall S P e (c1 : command) c2 m t v (c: command),
    eval_expr e m v ->
    c = (if Nat.eqb v 0 then c2 else c1) ->
    exec_command (S, P, Some (CIfThenElse e c1 c2), m, t) (S, P, Some c, m, t)
| While : forall S P e c m t,
    exec_command (S, P, Some (CWhile e c), m, t)
      (S, P, Some (CIfThenElse e (CSeq c (CWhile e c)) CSkip), m, t)
| InputPublic : forall S v P x m t,
    exec_command (S, Streams.Cons v P, Some (CInput Public x), m, t)
      (S, P, None, set_var x v m, EvInput Public v :: t)
| InputSecret : forall v S P x m t,
    exec_command (Streams.Cons v S, P, Some (CInput Secret x), m, t)
      (S, P, None, set_var x v m, EvInput Secret v :: t)
| Output : forall S P ch e m t v,
    eval_expr e m v ->
    exec_command (S, P, Some (COutput ch e), m, t) (S, P, None, m, EvOutput ch v :: t)
.


(* reflexive and transitive closure of the execution relation: *)
Inductive exec_trans : state -> state -> Prop :=
| exec_empty : forall s, exec_trans s s
| exec_step : forall s1 s2 s3, exec_command s1 s2 -> exec_trans s2 s3 -> exec_trans s1 s3
.

(* Initial memory *)
Definition minit := Empty value.

Fixpoint public_projection (t: trace) :=
  match t with
  | nil => nil
  | EvInput Public v :: q => EvInput Public v :: public_projection q
  | EvOutput Public v ::q => EvOutput Public v :: public_projection q
  | _ :: q => public_projection q
  end.


(* knowledge P c d S means that S is in the Set K(P,c,d) *)
Inductive knowledge: (Stream value) -> command -> trace -> (Stream value) -> Prop :=
| Know : forall P c d S,
    (exists S' P' c' m' t', exec_trans (S, P, Some c, minit, nil) (S', P', c', m', t') /\
                         public_projection t' = d) ->
    knowledge P c d S
.


Definition PSNI c :=
  forall P a d t,
    (exists S S' P' c' m', exec_trans (S, P, Some c, minit, nil) (S', P', c', m', t) /\
                        public_projection t = a :: d) ->
    (* Set equality is described with an iff *)
    (forall S, knowledge P c (a :: d) S <-> knowledge P c d S).


(* progress_knowledge P c d S means that S is in the Set K->(P,c,d) *)
Inductive progress_knowledge: (Stream value) -> command -> trace -> (Stream value) -> Prop :=
| PKnow : forall P c d S,
    (exists S' P' c' m' t' a, exec_trans (S, P, Some c, minit, nil) (S', P', c', m', t') /\
                           public_projection t' = a :: d) ->
    progress_knowledge P c d S
.


Definition PINI c :=
  forall P a d t,
    (exists S S' P' c' m', exec_trans (S, P, Some c, minit, nil) (S', P', c', m', t) /\
                        public_projection t = a :: d) ->
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

Definition context := varmap confidentiality.
Definition gamma0 := Empty confidentiality.

(* A memory and a context have the same support if the same variables are defined in them *)
Definition same_support (m : memory) (gamma : context) : Prop :=
  forall x, match find_var x m, find_var x gamma with
       | Some _, Some _ | None, None => True
       | _, _ => False
       end.



(* Joining two contexts, to be used after an If-statement *)
Fixpoint join_context (gamma1 gamma2 : context) : context :=
  match gamma1 with
  | Empty _ => gamma2
  | Cons _ x v gamma1 =>
      match find_and_remove x gamma2 with
      | Some (v', gamma2) => Cons _ x (join v v') (join_context gamma1 gamma2)
      | None => Cons _ x v (join_context gamma1 gamma2)
      end
  end.

Inductive typecheck_expr : context -> expr -> confidentiality -> Prop :=
| TLit : forall gamma n,
    typecheck_expr gamma (ELit n) LPublic
| TVar : forall l gamma x,
    find_var x gamma = Some l ->
    typecheck_expr gamma (EVar x) l
| TOp : forall l1 l2 gamma e1 op e2 l,
    typecheck_expr gamma e1 l1 ->
    typecheck_expr gamma e2 l2 ->
    l = join l1 l2 ->
    typecheck_expr gamma (EOp e1 op e2) l
.


Definition confidentiality_of_channel ch :=
  match ch with
  | Secret => LSecret
  | Public => LPublic
  end.

Inductive typecheck : context -> confidentiality -> command -> context -> Prop :=
| TSkip : forall gamma pc,
    typecheck gamma pc CSkip gamma
| TAssign : forall le gamma pc x e gamma',
    typecheck_expr gamma e le ->
    gamma' = set_var x (join le pc) gamma ->
    typecheck gamma pc (CAssign x e) gamma'
| TSeq : forall gamma1 gamma2 gamma3 pc c1 c2,
    typecheck gamma1 pc c1 gamma2 ->
    typecheck gamma2 pc c2 gamma3 ->
    typecheck gamma1 pc (CSeq c1 c2) gamma3
| TIf : forall l gamma gamma1 gamma2 gamma' pc e c1 c2,
    typecheck_expr gamma e l ->
    typecheck gamma (join pc l) c1 gamma1 ->
    typecheck gamma (join pc l) c2 gamma2 ->
    gamma' = join_context gamma1 gamma2 ->
    typecheck gamma pc (CIfThenElse e c1 c2) gamma'
| TWhile : forall l gamma pc e c gamma',
    typecheck_expr gamma e l ->
    typecheck gamma (join pc l) c gamma' ->
    typecheck gamma pc (CWhile e c) gamma'
| TInput : forall gamma pc x ch gamma',
    flows pc (confidentiality_of_channel ch) ->
    gamma' = set_var x (join (confidentiality_of_channel ch) pc) gamma ->
    typecheck gamma pc (CInput ch x) gamma'
| TOutput : forall le gamma pc e ch,
    typecheck_expr gamma e le ->
    flows (join pc le) (confidentiality_of_channel ch) ->
    typecheck gamma pc (COutput ch e) gamma
.



(* /* Program 1 -- should be well-typed as it satisfies PINI (and PSNI) */ *)
(* input(secret, x) *)
(* x = 0 *)
(* output(public, x) *)
Definition example1 :=
  CSeq (CInput Secret "x")
       (CSeq (CAssign "x" (ELit 0)) (COutput Public (EVar "x"))).

Definition example_typecheck example := exists gamma, typecheck (Empty _) LPublic example gamma.
Lemma example1_typecheck : example_typecheck example1.
Proof.
  eexists.
  repeat econstructor.
Qed.

(* /* Program 2 -- must be ill-typed as it violates PINI */ *)
(* input(secret, x) *)
(* output(public, x) *)
Definition example2 :=
  CSeq (CInput Secret "x") (COutput Public (EVar "x")).
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
  CSeq
    (CInput Secret "x")
    (CSeq
       (CAssign "y" (ELit 0))
       (CSeq
       (CIfThenElse
          (EVar "x")
          (CAssign "y" (ELit 1))
          (CSkip)
       )
       (COutput Public (EVar "y"))
       )
    ).
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
  CSeq
    (CInput Secret "x")
    (CSeq
       (CIfThenElse
          (EVar "x")
          (CAssign "y" (ELit 1))
          (CSkip)
       )
       (CSeq
          (COutput Secret (EVar "y"))
          (CSeq
             (CAssign "y" (ELit 0))
             (COutput Public (EVar "y"))
          )
       )
    ).
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
  CSeq
    (CInput Secret "x")
    (CSeq
       (CWhile
          (EVar "x")
          (CSeq
             (CAssign "x" (EOp (EVar "x") Sub (ELit 1)))
             (CInput Secret "y")
          )
       )
       (COutput Public (ELit 0))
    ).
Lemma example5_typecheck : example_typecheck example5.
Proof.
  repeat econstructor.
Qed.

(* /* Program 6 -- must be ill-typed as it violates PINI */ *)
(* input(secret, x) *)
(* while x do *)
(* x = x - 1 *)
(* input(secret, y) *)
(* output(public, x) *)
Definition example6 :=
  CSeq
    (CInput Secret "x")
    (CSeq
       (CWhile
          (EVar "x")
          (CSeq
             (CAssign "x" (EOp (EVar "x") Sub (ELit 1)))
             (CInput Secret "y")
          )
       )
       (COutput Public (EVar "x"))
    ).
Lemma example6_typecheck : not (example_typecheck example6).
Proof.
  intro.
  inversion H;subst.
  inversion H0;subst; clear H0.
  inversion H5;subst; cbn in H4; clear H5 H4; cbn in *.
  inversion H7;subst; clear H7.
  inversion H6;subst; clear H6.

  inversion H4;subst; clear H4.
  inversion H9;subst; clear H9.
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
Qed.

(* /* Program 7 -- must be well-typed  */ *)
(* input(secret, x) *)
(* input(public, x) *)
(* output(public, x) *)
Definition example7 :=
  (CSeq
     (CInput Secret "x")
     (CSeq
        (CInput Public "x")
        (COutput Public (EVar "x"))
     )
  ).
Lemma example7_typecheck : example_typecheck example7.
Proof.
  repeat econstructor.
Qed.












(* Attempt at defining a statement that intertwines execution and typechecking *)
Inductive exec_with_gamma : state -> context -> confidentiality -> state -> context -> confidentiality -> Prop :=
| GSkip : forall S P m t gamma pc,
    exec_with_gamma (S, P, Some CSkip, m, t) gamma pc (S, P, None, m, t) gamma pc
| GAssign : forall S P x e v m t gamma pc l gamma',
    eval_expr e m v ->
    typecheck_expr gamma e l ->
    gamma' = set_var x (join l pc) gamma ->
    exec_with_gamma (S, P, Some (CAssign x e), m, t) gamma pc
      (S, P, None, set_var x v m, t) gamma' pc
| GSeq1 : forall S P c1 c2 m t S' P' c1' m' t' gamma pc gamma' pc',
    exec_with_gamma (S, P, Some c1, m, t) gamma pc (S', P', Some c1', m', t') gamma' pc' ->
    exec_with_gamma (S, P, Some (CSeq c1 c2), m, t) gamma pc
      (S', P', Some (CSeq c1' c2), m', t') gamma' pc' (* Should this last one be pc? pc'? *)
| GSeq2 : forall S P c1 c2 m t S' P' m' t' gamma pc gamma' pc' ,
    exec_with_gamma (S, P, Some c1, m, t) gamma pc (S', P', None, m', t') gamma' pc' ->
    exec_with_gamma (S, P, Some (CSeq c1 c2), m, t) gamma pc
      (S', P', Some c2, m', t') gamma' pc (* This should not be pc', since we are done with c1 and should revert to what we had before *)
| GIf : forall S P e (c1 : command) c2 m t v (c: command) gamma pc l,
    eval_expr e m v -> typecheck_expr gamma e l ->
    c = (if Nat.eqb v 0 then c2 else c1) ->
    exec_with_gamma (S, P, Some (CIfThenElse e c1 c2), m, t) gamma pc
      (S, P, Some c, m, t) gamma (join pc l)
| GWhile : forall S P e c m t gamma pc,
    exec_with_gamma (S, P, Some (CWhile e c), m, t) gamma pc
      (S, P, Some (CIfThenElse e (CSeq c (CWhile e c)) CSkip), m, t) gamma pc
| GInputPublic : forall S v P x m t gamma pc gamma',
    gamma' = set_var x pc gamma ->
    exec_with_gamma (S, Streams.Cons v P, Some (CInput Public x), m, t) gamma pc
      (S, P, None, set_var x v m, EvInput Public v :: t) gamma' pc
| GInputSecret : forall v S P x m t gamma pc gamma',
    gamma' = set_var x LSecret gamma ->
    exec_with_gamma (Streams.Cons v S, P, Some (CInput Secret x), m, t) gamma pc
      (S, P, None, set_var x v m, EvInput Secret v :: t) gamma' pc
| GOutput : forall S P ch e m t v gamma pc,
    eval_expr e m v ->
    exec_with_gamma (S, P, Some (COutput ch e), m, t) gamma pc
      (S, P, None, m, EvOutput ch v :: t) gamma pc
.


Inductive exec_with_gamma_trans : state -> context -> confidentiality -> state -> context -> confidentiality -> Prop :=
| Gexec_empty : forall s gamma pc, exec_with_gamma_trans s gamma pc s gamma pc
| Gexec_step : forall s1 gamma1 pc1 s2 gamma2 pc2 s3 gamma3 pc3,
    exec_with_gamma s1 gamma1 pc1 s2 gamma2 pc2 ->
    exec_with_gamma_trans s2 gamma2 pc2 s3 gamma3 pc3 ->
    exec_with_gamma_trans s1 gamma1 pc1 s3 gamma3 pc3
.


(* Two memories have the same values for the public variables *)
Definition agree_on_public (gamma : context) (m1 m2 : memory) : Prop :=
  forall x,
    match find_var x m1, find_var x m2, find_var x gamma with
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
     specialize (Hagree v). rewrite H0 H1 H3 in Hagree. done.
   - inversion Hv1; subst. inversion Hv2; subst.
     inversion Ht; subst. destruct l1 => //. destruct l2 => //.
     rewrite (IHe1 v1 v0 H3 Hagree H4 H6).
     rewrite (IHe2 _ _ H9 Hagree H5 H7). done.
 Qed.


(* executing implies executing with gammas *)
Lemma can_exec_with_gamma gamma0 pc0 P0 S0 c0 m0 t0 s1 :
  same_support m0 gamma0 ->
  exec_trans (P0, S0, c0, m0, t0) s1 ->
  exists gamma1 pc1, exec_with_gamma_trans (P0, S0, c0, m0, t0) gamma0 pc0 s1 gamma1 pc1.
Proof.
Admitted.





Lemma type_preservation :
  forall c gamma pc gammaf gamma' P S m t P' S' c' m' t' pc',
  typecheck gamma pc c gammaf ->
  exec_with_gamma (P, S, Some c, m, t) gamma pc (P', S', c', m', t') gamma' pc' ->
  match c' with
    Some c' => typecheck gamma' pc' c' gammaf
  | None => gamma' = gammaf
  end .
Proof.
  induction c; intros gamma pc gammaf gamma' P S m t P' S' c' m' t' pc' Ht Hex;
    inversion Hex; subst => //.
  - inversion Ht; subst. done.
  - inversion Ht; subst. replace l with le => //.
    admit.
  - inversion Ht; subst.
    specialize (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 H14).
    eapply TSeq. exact IHc1.

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
  exec_with_gamma_trans (S0, P0, Some c0, m0, t0) gamma0 pc0
    (S1, P1, c1, m1, a :: t1) gamma1 pc1 ->
  exists S2 P2 c2 m2 gamma2 pc2 S3 P3 c3 m3 gamma3 pc3,
    exec_with_gamma_trans (S0, P0, Some c0, m0, t0) gamma0 pc0
      (S2, P2, Some c2, m2, t1) gamma2 pc2 /\
      exec_with_gamma (S2, P2, Some c2, m2, t1) gamma2 pc2
        (S3, P3, c3, m3, a :: t1) gamma3 pc3 /\
      exec_with_gamma_trans (S3, P3, c3, m3, a :: t1) gamma3 pc3
        (S1, P1, c1, m1, a :: t1) gamma1 pc1.
Proof.
Admitted.


(* Same as the previous lemma, but with public events only *)
Lemma separate_last_public_event S0 P0 c0 m0 t0 gamma0 pc0 S1 P1 c1 m1 t1 a d gamma1 pc1:
  exec_with_gamma_trans (S0, P0, Some c0, m0, t0) gamma0 pc0
    (S1, P1, c1, m1, t1) gamma1 pc1 ->
  public_projection t1 = a :: d ->
  exists S2 P2 c2 m2 t2 gamma2 pc2 S3 P3 c3 m3 gamma3 pc3,
    exec_with_gamma_trans (S0, P0, Some c0, m0, t0) gamma0 pc0
      (S2, P2, Some c2, m2, t2) gamma2 pc2 /\
      public_projection t2 = d /\
      exec_with_gamma  (S2, P2, Some c2, m2, t2) gamma2 pc2
        (S3, P3, c3, m3, a :: t2) gamma3 pc3 /\
      exec_with_gamma_trans (S3, P3, c3, m3, a :: t2) gamma3 pc3
        (S1, P1, c1, m1, t1) gamma1 pc1.
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
  exec_with_gamma (S1, P1, Some c, m1, t1) gamma1 pc1
    (S1', P1', c1', m1', t1') gamma1' pc1' ->
  exec_with_gamma (S2, P2, Some c, m2, t2) gamma2 pc2
    (S2', P2', c2', m2', t2') gamma2' pc2' ->
  match c1', c2' with | Some _, Some _ | None, None => True | _,_ => False end.
Proof.
  intros Hex1 Hex2.
  inversion Hex1; subst;
    inversion Hex2; subst => //.
Qed.


Lemma find_set_var {A} x (v : A) l :
  find_var x (set_var x v l) = Some v.
Proof.
  induction l => //=. rewrite String.eqb_refl. done.
  destruct (v0 =? x) eqn:Hvx => //=. rewrite String.eqb_refl. done.
  rewrite Hvx. done.
Qed.

Lemma find_set_var_diff {A} x y (v : A) l :
  x <> y ->
  find_var y (set_var x v l) = find_var y l.
Proof.
  intro Hxy. apply String.eqb_neq in Hxy.
  induction l => //=. by rewrite Hxy.
  destruct (v0 =? x) eqn:Hvx => //=.
  rewrite Hxy.   destruct (v0 =? y) eqn:Hvy => //=.
  apply String.eqb_eq in Hvy, Hvx; subst. rewrite String.eqb_neq in Hxy. done.
  by rewrite IHl.
Qed.



 Lemma set_var_agree gamma (m1 m2 : memory) x v l :
  agree_on_public gamma m1 m2 ->
  agree_on_public (set_var x l gamma) (set_var x v m1) (set_var x v m2).
 Proof.
   unfold agree_on_public.
   intros Hagree y.
   destruct (x =? y) eqn:Hxy.
   - apply String.eqb_eq in Hxy as ->.
     repeat rewrite find_set_var. by destruct l.
   - apply String.eqb_neq in Hxy.
     rewrite find_set_var_diff => //.
     rewrite find_set_var_diff => //.
     rewrite find_set_var_diff => //.
     by apply Hagree.
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
  exec_with_gamma (S1, P, Some c, m1, t1) gamma pc
    (S1', P1', c1', m1', a1 :: t1) gamma1 pc1 ->
  exec_with_gamma (S2, P, Some c, m2, t2) gamma pc
    (S2', P2', c2', m2', a2 :: t2) gamma2 pc2 ->
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
                     H3 Htriv Ht2 Ha1 Ha2 Hmem H14 H15)
          as (-> & -> & -> & ? & ? & ->).
        inversion H6; subst. by repeat split.
      * eapply exec_both_some in H14; try exact H15. done.
    + inversion Hex2; subst.
      * eapply exec_both_some in H14; try exact H15. done.
      * inversion Ht.
        assert (public_projection t1 = public_projection t1) as Htriv => //.
        edestruct (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                     H3 Htriv Ht2 Ha1 Ha2 Hmem H14 H15)
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
    typecheck gamma0 LPublic c gamma ->
    exec_with_gamma_trans (Sinit1, P, Some c, minit, nil) gamma0 LPublic
      (S1, P1, Some c1, m1, t1) gamma1 pc1 ->
    public_projection t1 = d1 ->
    exec_with_gamma (S1, P1, Some c1, m1, t1) gamma1 pc1
      (S1', P1', c1', m1', a1 :: t1) gamma1' pc1' ->
    public_projection (a1 :: t1) = a1 :: d1 ->
    exec_with_gamma_trans (Sinit2, P, Some c, minit, nil) gamma0 LPublic
      (S2, P2, Some c2, m2, t2) gamma2 pc2 ->
    public_projection t2 = d2 ->
    exec_with_gamma (S2, P2, Some c2, m2, t2) gamma2 pc2
      (S2', P2', c2', m2', a2 :: t2) gamma2' pc2' ->
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
  apply (can_exec_with_gamma gamma0 LPublic) in Hexec0 as (gamma1 & pc1 & Hexec0);
    last done.
  destruct (separate_last_public_event _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec0 Hp)
    as (S1m & P1m & c1m & m1m & t1m & gamma1m & pc1m &
          S1p & P1p & c1p & m1p & gamma1p & pc1p & Hex1m & Ht1m & Hex1c & Hex1p).
  apply (can_exec_with_gamma gamma0 LPublic) in Hexec as (gamma2 & pc2 & Hexec);
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


