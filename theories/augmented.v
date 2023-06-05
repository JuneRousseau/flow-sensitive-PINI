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
| WritePublic : var -> value -> public_event
| BecameSecret : var -> public_event
.

Inductive jcommand :=
| JSkip : jcommand
| JAssign : var -> expr -> jcommand
| JSeq : jcommand -> jcommand -> jcommand
| JIfThenElse : expr -> jcommand -> jcommand -> jcommand
| JWhile : expr -> jcommand -> jcommand
| JInput : channel -> var -> jcommand
| JOutput : channel -> expr -> jcommand
| JThenJoin : jcommand -> jcommand 
.


(* Fixpoint level j :=
  match j with
  | JSkip | JAssign _ => 0
  |  *)




Fixpoint jcommand_of_command c :=
  match c with
  | CSkip => JSkip
  | CAssign x e => JAssign x e
  | CSeq c1 c2 => JSeq (jcommand_of_command c1) (jcommand_of_command c2)
  | CIfThenElse a b c => JIfThenElse a (JThenJoin (jcommand_of_command b))
                          (JThenJoin (jcommand_of_command c))
  | CWhile e c => JWhile e (jcommand_of_command c)
  | CInput c x => JInput c x
  | COutput c e => JOutput c e
  end.

Fixpoint command_of_jcommand j :=
  match j with
  | JSkip => CSkip
  | JAssign x e => CAssign x e
  | JSeq j1 c2 => CSeq (command_of_jcommand j1) (command_of_jcommand c2)
  | JIfThenElse a b c => CIfThenElse a (command_of_jcommand b) (command_of_jcommand c)
  | JWhile e c => CWhile e (command_of_jcommand c)
  | JInput c x => CInput c x
  | JOutput c e => COutput c e
  | JThenJoin j => command_of_jcommand j
  end.

Lemma command_id : forall c, command_of_jcommand (jcommand_of_command c) = c.
Proof. intros. induction c => //=; try by rewrite IHc1 IHc2. by rewrite IHc. Qed.

Definition jconfig : Type :=
  (option jcommand) * (Stream value) * (Stream value) * memory * trace.

Fixpoint flows_pc pc1 pc2 :=
  match pc1, pc2 with
  | l1 :: pc1, l2 :: pc2 => flows l1 l2 /\ flows_pc pc1 pc2
  | [], [] => True
  | _, _ => False end.
Notation "pc1 '⊑pc' pc2" := (flows_pc pc1 pc2) (at level 40).

#[export] Instance reflexive_flows_pc : Reflexive flows_pc.
Proof. intros pc. induction pc => //=. Defined.

#[export] Instance transitive_flows_pc : Transitive flows_pc.
Proof.
  intros pc0 pc1 pc2 H1 H2.
  generalize dependent pc2; generalize dependent pc1.
  induction pc0; intros => //=.
  - destruct pc2 => //. destruct pc1 => //.
  - destruct pc2 => //. destruct pc1 => //.
    destruct pc1 => //.
    destruct H1 as [? H1].
    destruct H2 as [? H2].
    split; first by destruct a, c0, c.
    eapply IHpc0 => //.
Defined.

Fixpoint join_pc pc1 pc2 :=
  match pc1, pc2 with
  | l1 :: pc1, l2 :: pc2 =>
      match join_pc pc1 pc2 with
      | Some pc => Some (join l1 l2 :: pc)
      | None => None
      end
  | [], [] => Some []
  | _, _ => None
  end.
Notation "pc1 '⊔pc' pc2" := (join_pc pc1 pc2) (at level 40).

Lemma join_pc_comm pc1 pc2: pc1 ⊔pc pc2 = pc2 ⊔pc pc1.
Proof. generalize dependent pc2. induction pc1; intros; destruct pc2 => //=.
       rewrite IHpc1. destruct (join_pc pc2 pc1), a, c => //. Qed.

Lemma join_pc_idem pc : pc ⊔pc pc = Some pc.
Proof. induction pc => //=. rewrite IHpc. destruct a => //. Qed.

Lemma flows_join_pc pc0 pc1 pc2 pcj :
  pc0 ⊑pc pc1 ->
  pc0 ⊑pc pc2 ->
  (pc1 ⊔pc pc2) = Some pcj ->
  pc0 ⊑pc pcj.
Proof.
  intros Hpc1 Hpc2 Hpcj.
  generalize dependent pc1; generalize dependent pc2; generalize dependent pcj.
  induction pc0; intros => //=.
  - destruct pc1, pc2, pcj => //.
  - destruct pc1, pc2, pcj => //.
    simpl in Hpcj. destruct (join_pc pc1 pc2) => //.
    destruct Hpc2 as [??]. destruct Hpc1 as [??].
    simpl in Hpcj.
    destruct (join_pc pc1 pc2) eqn:Hpc => //.
    inversion Hpcj; subst.
    split. destruct a,c,c0 => //.
    eapply IHpc0. 3:exact Hpc. done. done.
Qed.

Lemma flows_pc_join pc pc' pcj:
  pc ⊔pc pc' = Some pcj ->
  pc ⊑pc pcj.
Proof.
  intros Hpc.
  generalize dependent pc'; generalize dependent pcj.
  induction pc; intros => //=; destruct pcj, pc' => //.
  - simpl in Hpc. destruct (join_pc pc pc') => //.
  - simpl in Hpc. destruct (join_pc pc pc') eqn:Hpc' => //.
    inversion Hpc; subst.
    split; first by destruct a, c0.
    eapply IHpc => //.
Qed.

Lemma flows_pc_fold pc0 pc1 :
  flows_pc pc0 pc1 ->
  flows (fold_left join pc0 LPublic) (fold_left join pc1 LPublic).
Proof.
  intros Hpc.
  generalize dependent pc1.
  induction pc0; intros => //=.
  destruct pc1 => //=.
  destruct Hpc as [Hac Hpc].
  rewrite - fold_start.
  rewrite - (fold_start pc1 _).
  apply IHpc0 in Hpc.
  destruct (fold_left join pc0 _), (fold_left join pc1 _), a, c => //.
 Qed.

 Lemma flows_fold pcs0 pcs1 pc0 pc1 :
   flows pc0 pc1 ->
   flows_pc pcs0 pcs1 ->
   flows (fold_left join pcs0 pc0) (fold_left join pcs1 pc1).
 Proof.
   intros Hpc Hpcs.
   rewrite - fold_start.
   rewrite - (fold_start pcs1 pc1).
   apply flows_pc_fold in Hpcs.
   destruct (fold_left join pcs0 LPublic), (fold_left join pcs1 LPublic), pc0, pc1 => //.
 Qed.

 Lemma flows_add Γ0 Γ1 x pc0 pc1 :
   flows_context Γ0 Γ1 ->
   flows pc0 pc1 ->
   flows_context (<[ x := pc0 ]> Γ0) (<[ x := pc1 ]> Γ1).
 Proof.
   intros Hcontext Hpc y.
   destruct (x =? y) eqn:Hxy.
   - apply String.eqb_eq in Hxy as ->.
     repeat rewrite lookup_insert. done.
   - apply String.eqb_neq in Hxy.
     rewrite lookup_insert_ne => //.
     specialize (Hcontext y).
     destruct (Γ0 !! y) eqn:Hy; rewrite Hy;
       rewrite lookup_insert_ne => //.
 Qed.

Inductive jtypecheck : context -> list confidentiality -> jcommand -> context -> list confidentiality -> Prop :=

| JTSkip : forall Γ pc Γf pcf,
    flows_context Γ Γf ->
    pc ⊑pc pcf ->
    jtypecheck Γ pc JSkip Γf pcf

| JTAssign : forall le Γ pc x e Γf pcf,
    {{ Γ ⊢ e : le }} ->
    flows_context (<[ x := fold_left join pc le ]> Γ) Γf ->
    pc ⊑pc pcf ->
    jtypecheck Γ pc (JAssign x e) Γf pcf

| JTSeq : forall (Γ1 Γ2 Γ3 : context) pc1 pc2 pc3 c1 c2,
    jtypecheck Γ1 pc1 c1 Γ2 pc2 ->
  jtypecheck Γ2 pc2 c2 Γ3 pc3 ->
  jtypecheck Γ1 pc1 (JSeq c1 c2) Γ3 pc3

| JTIf : forall l Γ Γ1 Γ2 pc e c1 c2 pc1 pc2 pcf,
  {{ Γ ⊢ e : l }} ->
  jtypecheck Γ (l :: pc) c1 Γ1 pc1 ->
  jtypecheck Γ (l :: pc) c2 Γ2 pc2 ->
  pc1 ⊔pc pc2 = Some pcf ->
  jtypecheck Γ pc (JIfThenElse e c1 c2) (Γ1 ⊔g Γ2) pcf

(* | JTWhile : forall l Γ pc e c Γ' pc', *)
(*     flows_context Γ Γ' -> *)
(*     pc ⊑pc pc' -> *)
(*     {{ Γ' ⊢ e : l }} -> *)
(*     jtypecheck Γ' (l :: pc') c Γ' (l :: pc') -> *)
(*     jtypecheck Γ pc (JWhile e c) Γ' pc' *)

             (*
(* Does not change the environment *)
| JTWhile1 : forall l Γ pc e c,
  {{ Γ ⊢ e : l }} ->
  jtypecheck Γ (l :: pc) c Γ (l :: pc) ->
  jtypecheck Γ pc (JWhile e c) Γ pc

(* Does change the environment *)
| JTWhile2 : forall l Γ pc e c Γ' pc' Γ'' pc'',
  {{ Γ ⊢ e : l }} ->
  jtypecheck Γ (l :: pc) c Γ'' pc'' ->
  jtypecheck Γ'' pc (JWhile e c) Γ' pc' ->
  jtypecheck Γ pc (JWhile e c) Γ' pc'
*)


| JTInput : forall Γ pc x ch Γ' pcf,
  (fold_left join pc LPublic ⊑ confidentiality_of_channel ch) ->
  flows_context ( <[ x := (fold_left join pc (confidentiality_of_channel ch)) ]> Γ) Γ' ->
  pc ⊑pc pcf ->
  jtypecheck Γ pc (JInput ch x) Γ' pcf

| JTOutput : forall le Γ pc e ch Γf pcf,
  {{ Γ ⊢ e : le }} ->
  (fold_left join pc le ⊑ confidentiality_of_channel ch) ->
  flows_context Γ Γf ->
  pc ⊑pc pcf ->
  jtypecheck Γ pc (JOutput ch e) Γf pcf

| JTJoin : forall Γ pc j Γ' l pc',
    jtypecheck Γ pc j Γ' (l :: pc') ->
    jtypecheck Γ pc (JThenJoin j) Γ' pc'
.


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
       | LPublic => Some (WritePublic x v)
       | LSecret => match Γ !! x with
                   | Some LPublic => Some (BecameSecret x)
                   | _ => None end end ->
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
      ( Some c2, S', P', m', t') Γ' (* [] *) ls' (* Note: why was this [] before? *)

| GIf : forall S P m t (c1 c2 : jcommand) e v l Γ ls,
  e ; m ⇓ v ->
  {{ Γ ⊢ e : l }} ->
  exec_with_gamma
    ( Some (JIfThenElse e c1 c2), S, P, m, t ) Γ ls
    None
    ( Some ((* JThenJoin  *) (if Nat.eqb v 0 then c2 else c1)), S, P, m, t ) Γ (l :: ls)

| GJoin1 : forall j S P m t Γ pc j' S' P' m' t' Γ' pc' alpha,
    exec_with_gamma
      ( Some j, S, P, m, t ) Γ pc
      alpha
      ( Some j', S', P', m', t') Γ' pc' ->
    exec_with_gamma
      ( Some (JThenJoin j), S, P, m, t) Γ pc
      alpha
      ( Some (JThenJoin j'), S', P', m', t') Γ' pc'

| GJoin2 : forall j S P m t Γ pc S' P' m' t' Γ' l pc' alpha,
    exec_with_gamma
      ( Some j, S, P, m, t ) Γ pc
      alpha
      ( None, S', P', m', t' ) Γ' (l :: pc') ->
    exec_with_gamma
      ( Some (JThenJoin j), S, P, m, t ) Γ pc
      alpha
      ( None, S', P', m', t') Γ' pc'
(*    
| GJoin : forall S P m t Γ l ls c,
    exec_with_gamma
      ( Some (JThenJoin c), S, P, m, t ) Γ (l :: ls)
      None
      ( Some (jcommand_of_command c), S, P, m, t ) Γ ls *)

| GWhile : forall S P m t c e Γ ls,
    exec_with_gamma
      ( Some (JWhile e c), S, P, m, t ) Γ ls
      None
      ( Some (JIfThenElse e (JSeq c (JWhile e c)) JSkip), S, P, m, t ) Γ ls

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

| GOutput : forall S P m t ch e v Γ ls ev l,
    e ; m ⇓ v ->
        {{ Γ ⊢ e : l }} ->
        (fold_left join ls l) ⊑ confidentiality_of_channel ch ->
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

Inductive bridge : jconfig -> context -> list confidentiality -> nat -> (* option *) public_event -> jconfig -> context -> list confidentiality -> Prop :=
(* | BridgeStop : forall c S P m t Γ ls S' P' m' t' Γ' ls',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      None
      ( None, S', P', m', t' ) Γ' ls' ->
    bridge
      ( Some c, S, P, m, t ) Γ ls
      0 None
      ( None, S', P', m', t' ) Γ' ls' *) 
| BridgePublic : forall c S P m t t' Γ ls c' S' P' m' ev Γ' ls',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      (Some ev)
      ( c', S', P', m', t') Γ' ls' ->
    bridge
      ( Some c, S, P, m, t) Γ ls
      0 ((* Some *) ev)
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

Inductive write_bridge : jconfig -> context -> list confidentiality -> nat -> public_event -> jconfig -> context -> list confidentiality -> Prop :=
| WBridgeWrite : forall c S P m t t' Γ ls c' S' P' m' a b Γ' ls',
    exec_with_gamma
      ( Some c, S, P, m, t ) Γ ls
      (Some (WritePublic a b))
      ( c', S', P', m', t') Γ' ls' ->
    write_bridge
      ( Some c, S, P, m, t) Γ ls
      0 (WritePublic a b)
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

Inductive bridges : jconfig -> context -> list confidentiality -> nat -> list public_event -> jconfig -> context -> list confidentiality -> Prop :=
(* | LastBridge : forall jc Γ ls jc' Γ' ls' n,
    incomplete_bridge jc Γ ls n jc' Γ' ls' -> bridges jc Γ ls 0 jc' Γ' ls' *)
(* | NoBridge : forall jc Γ ls,
    bridges jc Γ ls 0 [] jc Γ ls *)
| LastBridge : forall jc Γ ls ev jc' Γ' ls' n,
    match ev with | Input _ | Output _ => True | _ => False end ->
    bridge jc Γ ls n ev jc' Γ' ls' ->
    bridges jc Γ ls 0 [ev] jc' Γ' ls'
| MoreBridge : forall jc Γ ls jc' Γ' ls' k jc'' Γ'' ls'' n ev evs,
    bridge jc Γ ls n ev jc' Γ' ls' ->
    bridges jc' Γ' ls' k evs jc'' Γ'' ls'' ->
    bridges jc Γ ls (Datatypes.S k) (ev :: evs) jc'' Γ'' ls''
.

Inductive write_bridges : jconfig -> context -> list confidentiality -> nat -> list public_event -> jconfig -> context -> list confidentiality -> Prop :=
(* | LastBridge : forall jc Γ ls jc' Γ' ls' n,
    incomplete_bridge jc Γ ls n jc' Γ' ls' -> bridges jc Γ ls 0 jc' Γ' ls' *)
 | NoWBridge : forall jc Γ ls,
     write_bridges jc Γ ls 0 [] jc Γ ls 
(*| LastBridge : forall jc Γ ls ev jc' Γ' ls' n,
    match ev with | Input _ | Output _ => True | _ => False end ->
    bridge jc Γ ls n ev jc' Γ' ls' ->
    bridges jc Γ ls 0 [ev] jc' Γ' ls' *)
| MoreWBridge : forall jc Γ ls jc' Γ' ls' k jc'' Γ'' ls'' n ev evs,
    write_bridge jc Γ ls n ev jc' Γ' ls' ->
    write_bridges jc' Γ' ls' k evs jc'' Γ'' ls'' ->
    write_bridges jc Γ ls (Datatypes.S k) (ev :: evs) jc'' Γ'' ls''
.




Inductive full_bridges : jconfig -> context -> list confidentiality -> list public_event -> jconfig -> context -> list confidentiality -> Prop :=
| BridgesAndEpilogue: forall jc0 Γ0 ls0 k0 jc1 Γ1 ls1 k1 jc2 Γ2 ls2 k2 evs0 evs1 jc3 Γ3 ls3,
    bridges jc0 Γ0 ls0 k0 evs0 jc1 Γ1 ls1 ->
    write_bridges jc1 Γ1 ls1 k1 evs1 jc2 Γ2 ls2 ->
    silent_bridge jc2 Γ2 ls2 k2 jc3 Γ3 ls3 ->
    full_bridges jc0 Γ0 ls0 evs0 jc3 Γ3 ls3
| NoPublicEvents: forall jc0 Γ0 ls0 jc1 Γ1 ls1 jc2 Γ2 ls2 k1 evs k2,
    write_bridges jc0 Γ0 ls0 k1 evs jc1 Γ1 ls1 ->
    silent_bridge jc1 Γ1 ls1 k2 jc2 Γ2 ls2 ->
    full_bridges jc0 Γ0 ls0 [] jc2 Γ2 ls2.

Fixpoint trace_of_public_trace evs :=
  match evs with
  | [] => []
  | Input v :: evs => EvInput Public v :: trace_of_public_trace evs
  | Output v :: evs => EvOutput Public v :: trace_of_public_trace evs
  | _ :: evs => trace_of_public_trace evs
  end. 

