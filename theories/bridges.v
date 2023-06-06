(* Require Import String. *)
Require Import ssreflect.
(* From Coq Require Import *)
(*   Lists.List *)
  (* Streams *)
(* . *)
From stdpp Require Import gmap.
From fspini Require Import
  lang
  types
  augmented
  security
  properties
.

(* Basic-bridge relation that relates two states emitting no event for n-1 steps,
   then finally any public event *)
Inductive basic_bridge : jconfig -> context -> list confidentiality -> nat -> public_event -> jconfig -> context -> list confidentiality -> Prop :=
| BBridgePublic : forall c S P m t t' Γ ls c' S' P' m' ev Γ' ls',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      (Some ev)
      ( c', S', P', m', t') Γ' ls' ->
    basic_bridge
      ( Some c, S, P, m, t) Γ ls
      0 ev
      ( c', S', P', m', t') Γ' ls'
| BBridgeMulti : forall c S P m t Γ ls c' S' P' m' t' Γ' ls' n e c'' S'' P'' m'' t'' Γ'' ls'',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      None
      ( Some c', S', P', m', t' ) Γ' ls' ->
    basic_bridge
      ( Some c', S', P', m', t' ) Γ' ls'
      n e
      ( c'', S'', P'', m'', t'' ) Γ'' ls'' ->
    basic_bridge
      ( Some c, S, P, m, t ) Γ ls
      (Datatypes.S n) e
      ( c'', S'', P'', m'', t'' ) Γ'' ls''
.

(* Transitive cloture of basic-brigde, which end with a non-write event *)
Inductive final_nw_bridges : jconfig -> context -> list confidentiality -> nat -> list public_event -> jconfig -> context -> list confidentiality -> Prop :=
| LastNWBridge : forall jc Γ ls ev jc' Γ' ls' n,
    match ev with | Input _ | Output _ => True | _ => False end ->
    basic_bridge jc Γ ls n ev jc' Γ' ls' ->
    final_nw_bridges jc Γ ls 0 [ev] jc' Γ' ls'
| MoreNWBridge : forall jc Γ ls jc' Γ' ls' k jc'' Γ'' ls'' n ev evs,
    basic_bridge jc Γ ls n ev jc' Γ' ls' ->
    final_nw_bridges jc' Γ' ls' k evs jc'' Γ'' ls'' ->
    final_nw_bridges jc Γ ls (Datatypes.S k) (ev :: evs) jc'' Γ'' ls''
.


(* Write-bridge relation that relates two states emitting no event for n-1 steps,
   then finally a write event *)
Inductive write_bridge : jconfig -> context -> list confidentiality -> nat -> public_event -> jconfig -> context -> list confidentiality -> Prop :=
| WBridgeWrite : forall c S P m t t' Γ ls c' S' P' m' ev Γ' ls',
    match ev with WritePublic _ _ | BecameSecret _ => True | _ => False end ->
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      (Some ev)
      ( c', S', P', m', t') Γ' ls' ->
    write_bridge
      ( Some c, S, P, m, t) Γ ls
      0 ev
      ( c', S', P', m', t') Γ' ls'
| WBridgeMulti : forall c S P m t Γ ls c' S' P' m' t' Γ' ls' n e c'' S'' P'' m'' t'' Γ'' ls'',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      None
      ( Some c', S', P', m', t' ) Γ' ls' ->
    write_bridge
      ( Some c', S', P', m', t' ) Γ' ls'
      n e
      ( c'', S'', P'', m'', t'' ) Γ'' ls'' ->
    write_bridge
      ( Some c, S, P, m, t ) Γ ls
      (Datatypes.S n) e
      ( c'', S'', P'', m'', t'' ) Γ'' ls''.

(* Transitive cloture of write-brigde *)
Inductive write_bridges : jconfig -> context -> list confidentiality -> nat -> list public_event -> jconfig -> context -> list confidentiality -> Prop :=
| NoWBridge : forall jc Γ ls,
  write_bridges jc Γ ls 0 [] jc Γ ls
| MoreWBridge : forall jc Γ ls jc' Γ' ls' k jc'' Γ'' ls'' n ev evs,
  write_bridge jc Γ ls n ev jc' Γ' ls' ->
  write_bridges jc' Γ' ls' k evs jc'' Γ'' ls'' ->
  write_bridges jc Γ ls (Datatypes.S k) (ev :: evs) jc'' Γ'' ls''
.

(* Silent-bridge relation that relates two states emitting no event for n steps *)
Inductive silent_bridge : jconfig -> context -> list confidentiality -> nat -> jconfig -> context -> list confidentiality -> Prop :=
| IBridgeStop : forall jc Γ ls,
    silent_bridge
      jc Γ ls
      0
      jc Γ ls
| IBridgeMulti : forall c S P m t Γ ls c' S' P' m' t' Γ' ls' n c'' S'' P'' m'' t'' Γ'' ls'',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      None
      ( c', S', P', m', t' ) Γ' ls' ->
    silent_bridge
      ( c', S', P', m', t' ) Γ' ls'
      n
      ( c'', S'', P'', m'', t'' ) Γ'' ls'' ->
    silent_bridge
      ( Some c, S, P, m, t ) Γ ls
      (Datatypes.S n)
      ( c'', S'', P'', m'', t'' ) Γ'' ls''
.

(* TODO I'm not sure about what represent the number of steps *)
Inductive bridge : jconfig -> context -> list confidentiality -> list public_event -> jconfig -> context -> list confidentiality -> Prop :=
| BridgesAndEpilogue: forall jc0 Γ0 ls0 k0 jc1 Γ1 ls1 k1 jc2 Γ2 ls2 k2 evs0 evs1 jc3 Γ3 ls3,
  (* Takes k0-1 basic_bridges, then one non-write basic_bridge *)
  final_nw_bridges jc0 Γ0 ls0 k0 evs0 jc1 Γ1 ls1 ->
  (* Takes k1 write_bridges *)
  write_bridges jc1 Γ1 ls1 k1 evs1 jc2 Γ2 ls2 ->
  (* Takes k2 silent_bridges *)
  silent_bridge jc2 Γ2 ls2 k2 jc3 Γ3 ls3 ->
  bridge jc0 Γ0 ls0 evs0 jc3 Γ3 ls3
| NoPublicEvents: forall jc0 Γ0 ls0 jc1 Γ1 ls1 jc2 Γ2 ls2 k1 evs k2,
  (* Takes k0 write_bridges *)
  write_bridges jc0 Γ0 ls0 k1 evs jc1 Γ1 ls1 ->
  (* Takes k2 silent_bridges *)
  silent_bridge jc1 Γ1 ls1 k2 jc2 Γ2 ls2 ->
  bridge jc0 Γ0 ls0 [] jc2 Γ2 ls2.


(** Monotonicity of the trace *)

(* The trace only grows if we follow one basic bridge *)
Lemma trace_monotone_basic_bridge :
  forall k c S P m t c' S' P' m' t' Γ pc ev Γ' pc',
  basic_bridge (c, S, P, m, t) Γ pc k ev (c', S', P', m', t') Γ' pc' ->
  exists nw, t' = app nw t.
Proof.
  destruct c as [c|]; last by inversion 1.
  generalize dependent c.
  induction k; intros * Hstep; inversion Hstep; subst;
    try by eapply trace_monotone_with_gamma.
  eapply trace_monotone_with_gamma in H15 as [nw ->].
  eapply IHk in H16 as [nw' ->].
  exists (nw' ++ nw)%list.
  by rewrite app_assoc.
Qed.

(* The trace only grows if we follow one final_nw_bridge *)
Lemma trace_monotone_final_nw_bridges :
  forall k c S P m t c' S' P' m' t' Γ pc Γ' pc' ev,
  final_nw_bridges (c, S, P, m, t) Γ pc k ev (c', S', P', m', t') Γ' pc' ->
  exists nw, t' = app nw t.
Proof.
  induction k; intros * Hstep; inversion Hstep; subst.
  - by eapply trace_monotone_basic_bridge.
  - destruct jc' as [[[[??]?]?]?]. apply trace_monotone_basic_bridge in H0 as [nw ->].
    eapply IHk in H4 as [nw' ->].
    exists (nw' ++ nw)%list.
    by rewrite app_assoc.
Qed.



(* The trace only grows if we follow only write-bridges *)
Lemma trace_monotone_write_bridge :
  forall k c S P m t c' S' P' m' t' Γ pc ev Γ' pc',
  write_bridge (c, S, P, m, t) Γ pc k ev (c', S', P', m', t') Γ' pc' ->
  exists nw, t' = app nw t.
Proof.
  destruct c as [c|]; last by inversion 1.
  generalize dependent c.
  induction k; intros * Hstep; inversion Hstep; subst;
    try by eapply trace_monotone_with_gamma.
  eapply trace_monotone_with_gamma in H15 as [nw ->].
  eapply IHk in H16 as [nw' ->].
  exists (nw' ++ nw)%list.
  by rewrite app_assoc.
Qed.

Lemma trace_monotone_write_bridges :
  forall k c S P m t c' S' P' m' t' Γ pc Γ' pc' ev,
  write_bridges (c, S, P, m, t) Γ pc k ev (c', S', P', m', t') Γ' pc' ->
  exists nw, t' = app nw t.
Proof.
  induction k; intros * Hstep; inversion Hstep; subst.
  - by eexists nil.
  - destruct jc' as [[[[??]?]?]?]. apply trace_monotone_write_bridge in H0 as [nw ->].
    eapply IHk in H4 as [nw' ->].
    exists (nw' ++ nw)%list.
    by rewrite app_assoc.
Qed.

(* The trace only grows if we follow a silent-bridge *)
Lemma trace_monotone_silent_bridge :
  forall k c S P m t c' S' P' m' t' Γ pc Γ' pc',
  silent_bridge (c, S, P, m, t) Γ pc k (c', S', P', m', t') Γ' pc' ->
  exists nw, t' = app nw t.
Proof.
  induction k; intros * Hstep; inversion Hstep; subst.
  - by eexists nil.
  - apply trace_monotone_with_gamma in H14 as [nw ->].
    eapply IHk in H15 as [nw' ->].
    exists (nw' ++ nw)%list.
    by rewrite app_assoc.
Qed.

(* The trace only grows if we follow a brigde *)
Lemma trace_monotone_bridge :
  forall c S P m t c' S' P' m' t' Γ pc Γ' pc' evs,
  bridge (c, S, P, m, t) Γ pc evs (c', S', P', m', t') Γ' pc' ->
  exists nw, t' = app nw t.
Proof.
  intros * Hstep; inversion Hstep; subst.
  - destruct jc1 as [[[[??]?]?]?].
    destruct jc2 as [[[[??]?]?]?].
    eapply trace_monotone_final_nw_bridges in H as [nw ->].
    eapply trace_monotone_write_bridges in H0 as [nw' ->].
    eapply trace_monotone_silent_bridge in H1 as  [nw'' ->].
    exists (nw'' ++ nw' ++ nw)%list.
    by repeat rewrite app_assoc.
  - destruct jc1 as [[[[??]?]?]?].
    eapply trace_monotone_write_bridges in H as [nw ->].
    eapply trace_monotone_silent_bridge in H0 as [nw' ->].
    exists (nw' ++ nw)%list. by rewrite app_assoc.
Qed.

(* TODO explain lemma *)
Lemma basic_bridge_grow_trace j S P m t Γ pc k ev j' S' P' m' t' Γ' pc':
  basic_bridge (j, S, P, m, t) Γ pc k ev (j', S', P', m', t') Γ' pc' ->
  (⟦ t' ⟧p) = match ev with
              | Input v => EvInput Public v :: (⟦ t ⟧p)
              | Output v => EvOutput Public v :: (⟦ t ⟧p)
              | _ => (⟦ t ⟧p) end.
Proof.
  intros Hbr.
  destruct j; last by inversion Hbr.
  generalize dependent j; generalize dependent S; generalize dependent P;
    generalize dependent m; generalize dependent t; generalize dependent Γ;
    generalize dependent pc.
  induction k; intros; inversion Hbr; subst.
  - eapply exec_grow_trace in H14. done.
  - eapply IHk in H16. apply exec_with_gamma_no_event in H15 as ->. done. done.
Qed.


Lemma final_nw_bridges_none S P m t Γ pc k evs jc Γ' pc' :
  final_nw_bridges (None, S, P, m, t) Γ pc k evs jc Γ' pc' ->
  False.
Proof.
  intros Hbr. inversion Hbr; subst. inversion H0. inversion H.
Qed.

(* TODO explain lemma *)
Lemma final_nw_bridges_grow_trace j S P m t Γ pc k evs j' S' P' m' t' Γ' pc':
  final_nw_bridges (j, S, P, m, t) Γ pc k evs (j', S', P', m', t') Γ' pc' ->
  length (⟦ t' ⟧p) > length (⟦ t ⟧p).
Proof.
  intros Hbr.
  destruct j; last by apply final_nw_bridges_none in Hbr.
  generalize dependent j; generalize dependent S; generalize dependent P;
    generalize dependent m; generalize dependent t; generalize dependent Γ;
    generalize dependent pc; generalize dependent evs.
  induction k; intros; inversion Hbr; subst.
  - apply basic_bridge_grow_trace in H0. destruct ev ; rewrite H0 => //=; lia.
  - destruct jc' as [[[[??]?]?]?]. destruct o; last by apply final_nw_bridges_none in H4.
    apply IHk in H4. apply basic_bridge_grow_trace in H0.
    rewrite H0 in H4. destruct ev; simpl in H4; lia.
Qed.

(** Type preservation *)

(* Well-typed command is still well-typed after taking a basic_bridge *)
Lemma preservation_basic_bridge j0 P0 S0 m0 t0 Γ0 pc0 j1 P1 S1 m1 t1 Γ1 pc1 ev Γf pcf k:
  wf_memory m0 Γ0 ->
  jtypecheck Γ0 pc0 j0 Γf pcf ->
  basic_bridge
    ( Some j0 , P0, S0, m0, t0 ) Γ0 pc0
    k ev
    ( j1 , P1, S1, m1, t1 ) Γ1 pc1 ->
  wf_memory m1 Γ1 /\ match j1 with Some j1 => jtypecheck Γ1 pc1 j1 Γf pcf | None => True end.
Proof.
  intros Hm0 Hj0 Hexec.
  generalize dependent j0; generalize dependent P0; generalize dependent S0;
    generalize dependent m0; generalize dependent t0; generalize dependent Γ0;
    generalize dependent pc0.
  induction k; intros; inversion Hexec; subst.
  - by eapply jtype_preservation.
  - eapply jtype_preservation in H15 as [??] => //.
    eapply IHk in H16 => //.
Qed.
