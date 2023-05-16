Require Import String.
Require Import ssreflect.
From Coq Require Import
  Lists.List
  Streams.
From stdpp Require Import gmap.
From fspini Require Import
  lang
  types
  security
  map_simpl.

(* Attempt at defining a statement that intertwines execution and typechecking *)
Inductive exec_with_gamma : config -> context -> confidentiality -> config -> context -> confidentiality -> Prop :=
| GSkip : forall S P m t Γ pc,
  exec_with_gamma
      ( Some SKIP, S, P, m, t) Γ pc
      ( None, S, P, m, t) Γ pc

| GAssign : forall S P m t x e v l Γ pc Γ',
  e ; m ⇓ v ->
  {{ Γ ⊢ e : l }} ->
  Γ' = <[ x := l ⊔ pc ]> Γ ->
  exec_with_gamma
    ( Some (x ::= e), S, P, m, t ) Γ pc
    ( None, S, P, <[ x := v ]> m, t) Γ' pc

| GSeq1 : forall S P m t c1 c2 Γ pc S' P' m' t' c1' Γ' pc',
    exec_with_gamma
      ( Some c1, S, P, m, t) Γ pc
      ( Some c1', S', P', m', t') Γ' pc'
    ->
    exec_with_gamma
      ( Some (c1 ;;; c2), S, P, m, t ) Γ pc
      ( Some (c1' ;;; c2), S', P', m', t' ) Γ' pc' (* Should this last one be pc? pc'? *)

| GSeq2 : forall S P m t c1 c2 Γ pc S' P' m' t' Γ' pc' ,
    exec_with_gamma
      ( Some c1, S, P, m , t ) Γ pc
      ( None, S', P', m', t' ) Γ' pc'
    ->
    exec_with_gamma
      ( Some (c1 ;;; c2), S, P, m, t ) Γ pc
      ( Some c2, S', P', m', t') Γ' pc'
      (* This should not be pc', since we are done with c1 and should revert to what we had before *)

| GIf : forall S P m t (c1 c2 : command) e v l Γ pc,
  e ; m ⇓ v ->
  {{ Γ ⊢ e : l }} ->
  exec_with_gamma
      ( Some (IFB e THEN c1 ELSE c2 FI), S, P, m, t ) Γ pc
      ( Some (if Nat.eqb v 0 then c2 else c1), S, P, m, t ) Γ (pc ⊔ l)

| GWhile : forall S P m t c e Γ pc,
    exec_with_gamma
      ( Some (WHILE e DO c END), S, P, m, t ) Γ pc
      ( Some (IFB e THEN (c ;;; WHILE e DO c END) ELSE SKIP FI), S, P, m, t ) Γ pc

| GInputPublic : forall S P m t x v Γ pc Γ',
    Γ' = <[ x := pc ]> Γ ->
    exec_with_gamma
      ( Some (INPUT x @Public), S, v::::P, m, t ) Γ pc
      ( None, S, P, <[x := v ]> m, EvInput Public v :: t ) Γ' pc

| GInputSecret : forall S P m t x v Γ pc Γ',
    Γ' = <[ x := LSecret ]> Γ ->
    exec_with_gamma
      ( Some (INPUT x @Secret), v::::S, P, m, t ) Γ pc
      ( None, S, P, <[x := v ]> m, EvInput Secret v :: t ) Γ' pc

| GOutput : forall S P m t ch e v Γ pc,
  e ; m ⇓ v ->
    exec_with_gamma
      ( Some (OUTPUT e @ch), S, P, m, t ) Γ pc
      ( None, S, P, m, EvOutput ch v :: t) Γ pc
.

Inductive exec_with_gamma_trans :
  config -> context -> confidentiality ->
  config -> context -> confidentiality -> Prop :=
| Gexec_empty : forall s gamma pc, exec_with_gamma_trans s gamma pc s gamma pc
| Gexec_step : forall s1 gamma1 pc1 s2 gamma2 pc2 s3 gamma3 pc3,
    exec_with_gamma s1 gamma1 pc1 s2 gamma2 pc2 ->
    exec_with_gamma_trans s2 gamma2 pc2 s3 gamma3 pc3 ->
    exec_with_gamma_trans s1 gamma1 pc1 s3 gamma3 pc3
.



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
