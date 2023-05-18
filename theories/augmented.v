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


Inductive public_event :=
| Input : value -> public_event
| Output : value -> public_event
| Write : var -> value -> public_event
.

Inductive jcommand :=
| JSkip : jcommand
| JAssign : var -> expr -> jcommand
| JSeq : jcommand -> command -> jcommand
| JIfThenElse : expr -> command -> command -> jcommand
| JWhile : expr -> command -> jcommand
| JInput : channel -> var -> jcommand
| JOutput : channel -> expr -> jcommand
| JThenJoin : command -> jcommand 
.

Fixpoint jcommand_of_command c :=
  match c with
  | CSkip => JSkip
  | CAssign x e => JAssign x e
  | CSeq c1 c2 => JSeq (jcommand_of_command c1) c2
  | CIfThenElse a b c => JIfThenElse a b c
  | CWhile e c => JWhile e c
  | CInput c x => JInput c x
  | COutput c e => JOutput c e
  end.

Fixpoint command_of_jcommand j :=
  match j with
  | JSkip => CSkip
  | JAssign x e => CAssign x e
  | JSeq j1 c2 => CSeq (command_of_jcommand j1) c2
  | JIfThenElse a b c => CIfThenElse a b c
  | JWhile e c => CWhile e c
  | JInput c x => CInput c x
  | JOutput c e => COutput c e
  | JThenJoin c => c
  end.

Lemma command_id : forall c, command_of_jcommand (jcommand_of_command c) = c.
Proof. intros. induction c => //=. by rewrite IHc1. Qed. 

Definition jconfig : Type :=
  (option jcommand) * (Stream value) * (Stream value) * memory * trace.


(* Attempt at defining a statement that intertwines execution and typechecking *)
Inductive exec_with_gamma : jconfig -> context -> list confidentiality -> option public_event -> jconfig -> context -> list confidentiality -> Prop :=
| GSkip : forall S P m t Γ ls,
  exec_with_gamma
    ( Some JSkip, S, P, m, t) Γ ls
    None
    ( None, S, P, m, t) Γ ls

| GAssign : forall S P m t ev x e v l Γ ls Γ',
  e ; m ⇓ v ->
  {{ Γ ⊢ e : l }} ->
  Γ' = <[ x := fold_left join ls l ]> Γ ->
  ev = match l with
       | LPublic => Some (Write x v)
       | LSecret => None end ->
  exec_with_gamma
    ( Some (JAssign x e), S, P, m, t ) Γ ls
    ev
    ( None, S, P, <[ x := v ]> m, t) Γ' ls

| GSeq1 : forall S P m t c1 c2 Γ ls S' P' m' t' c1' Γ' ls' ev,
    exec_with_gamma
      ( Some c1, S, P, m, t) Γ ls
      ev
      ( Some c1', S', P', m', t') Γ' ls'
    ->
    exec_with_gamma
      ( Some (JSeq c1 c2), S, P, m, t ) Γ ls
      ev
      ( Some (JSeq c1' c2), S', P', m', t' ) Γ' ls'

| GSeq2 : forall S P m t c1 c2 Γ ls ls' S' P' m' t' Γ' ev,
    exec_with_gamma
      ( Some c1, S, P, m , t ) Γ ls
      ev
      ( None, S', P', m', t' ) Γ' ls'
    ->
    exec_with_gamma
      ( Some (JSeq c1 c2), S, P, m, t ) Γ ls
      ev
      ( Some (jcommand_of_command c2), S', P', m', t') Γ' []

| GIf : forall S P m t (c1 c2 : command) e v l Γ ls,
  e ; m ⇓ v ->
  {{ Γ ⊢ e : l }} ->
  exec_with_gamma
    ( Some (JIfThenElse e c1 c2), S, P, m, t ) Γ ls
    None
    ( Some (JThenJoin (if Nat.eqb v 0 then c2 else c1)), S, P, m, t ) Γ (l :: ls)

| GJoin : forall S P m t Γ l ls c,
    exec_with_gamma
      ( Some (JThenJoin c), S, P, m, t ) Γ (l :: ls)
      None
      ( Some (jcommand_of_command c), S, P, m, t ) Γ ls

| GWhile : forall S P m t c e Γ ls,
    exec_with_gamma
      ( Some (JWhile e c), S, P, m, t ) Γ ls
      None
      ( Some (JIfThenElse e (c ;;; WHILE e DO c END) SKIP), S, P, m, t ) Γ ls

| GInputPublic : forall S P m t x v Γ ls Γ',
    Γ' = <[ x := fold_left join ls LPublic ]> Γ ->
    exec_with_gamma
      ( Some (JInput Public x), S, v::::P, m, t ) Γ ls
      ( Some (Input v))
      ( None, S, P, <[x := v ]> m, EvInput Public v :: t ) Γ' ls

| GInputSecret : forall S P m t x v Γ ls Γ',
    Γ' = <[ x := LSecret ]> Γ ->
    exec_with_gamma
      ( Some (JInput Secret x), v::::S, P, m, t ) Γ ls
      None 
      ( None, S, P, <[x := v ]> m, EvInput Secret v :: t ) Γ' ls

| GOutput : forall S P m t ch e v Γ ls ev,
    e ; m ⇓ v ->
        ev = match ch with Public => Some (Output v) | Secret => None end -> 
    exec_with_gamma
      ( Some (JOutput ch e), S, P, m, t ) Γ ls
      ev
      ( None, S, P, m, EvOutput ch v :: t) Γ ls
.

(*
Inductive exec_with_gamma_trans :
  config -> context -> list confidentiality -> nat ->
  config -> context -> list confidentiality -> Prop :=
| Gexec_empty : forall s gamma ls, exec_with_gamma_trans s gamma ls 0 s gamma ls
| Gexec_step : forall s1 gamma1 ls1 s2 gamma2 ls2 s3 gamma3 ls3 n,
    exec_with_gamma s1 gamma1 ls1 s2 gamma2 ls2 ->
    exec_with_gamma_trans s2 gamma2 ls2 n s3 gamma3 ls3 ->
    exec_with_gamma_trans s1 gamma1 ls1 (n+1) s3 gamma3 ls3
. *)
(*
Definition isPublic ev :=
  match ev with
  | EvInput Public _
  | EvOutput Public _
  | Write _ _ => True
  | _ => False
  end.  *)

Inductive bridge : jconfig -> context -> list confidentiality -> nat -> option public_event -> jconfig -> context -> list confidentiality -> Prop :=
| BridgeStop : forall c S P m t Γ ls S' P' m' t' Γ' ls',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      None
      ( None, S', P', m', t' ) Γ' ls' ->
    bridge
      ( Some c, S, P, m, t ) Γ ls
      0 None
      ( None, S', P', m', t' ) Γ' ls'
| BridgePublic : forall c S P m t t' Γ ls c' S' P' m' ev Γ' ls',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      (Some ev)
      ( c', S', P', m', t') Γ' ls' ->
    bridge
      ( Some c, S, P, m, t) Γ ls
      0 (Some ev)
      ( c', S', P', m', t') Γ' ls'
| BridgeMulti : forall c S P m t Γ ls c' S' P' m' t' Γ' ls' n e c'' S'' P'' m'' t'' Γ'' ls'',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      None
      ( Some c', S', P', m', t' ) Γ' ls' ->
    bridge
      ( Some c', S', P', m', t' ) Γ' ls'
      n e
      ( c'', S'', P'', m'', t'' ) Γ'' ls'' ->
    bridge
      ( Some c, S, P, m, t ) Γ ls
      (Datatypes.S n) e
      ( c'', S'', P'', m'', t'' ) Γ'' ls''
.

Inductive incomplete_bridge : jconfig -> context -> list confidentiality -> nat -> jconfig -> context -> list confidentiality -> Prop :=
| IBridgeStop : forall c S P m t Γ ls,
    incomplete_bridge
      ( Some c, S, P, m, t ) Γ ls
      0
      ( Some c, S, P, m, t ) Γ ls
| IBridgeMulti : forall c S P m t Γ ls c' S' P' m' t' Γ' ls' n c'' S'' P'' m'' t'' Γ'' ls'',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      None
      ( Some c', S', P', m', t' ) Γ' ls' ->
    incomplete_bridge
      ( Some c', S', P', m', t' ) Γ' ls'
      n
      ( c'', S'', P'', m'', t'' ) Γ'' ls'' ->
    incomplete_bridge
      ( Some c, S, P, m, t ) Γ ls
      (Datatypes.S n)
      ( c'', S'', P'', m'', t'' ) Γ'' ls''
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
