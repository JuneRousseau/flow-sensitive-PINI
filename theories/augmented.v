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
  properties
  map_simpl.


Inductive public_event :=
| Input : value -> public_event
| Output : value -> public_event
| WritePublic : var -> value -> public_event
| BecameSecret : var -> public_event
.

Fixpoint trace_of_public_trace evs :=
  match evs with
  | [] => []
  | Input v :: evs => EvInput Public v :: trace_of_public_trace evs
  | Output v :: evs => EvOutput Public v :: trace_of_public_trace evs
  | _ :: evs => trace_of_public_trace evs
  end.

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

(* Compile a command into a jcommand *)
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

(* Decompile a jcommand into a command *)
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


(* Operationnal semanctic of the jcommand *)
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

| GInputSecret : forall S P m t x v Γ ls Γ' ev,
    Γ' = <[ x := LSecret ]> Γ ->
    ev = match Γ !! x with
         | Some LPublic => Some (BecameSecret x)
         | _ => None end ->
  exec_with_gamma
    ( Some (JInput Secret x), v::::S, P, m, t ) Γ ls
    ev
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

(* The trace only grows along the reduction in the opsem *)
Lemma trace_monotone_with_gamma :
  forall c S P m t c' S' P' m' t' Γ pc ev Γ' pc',
  exec_with_gamma (c, S, P, m, t) Γ pc ev (c', S', P', m', t') Γ' pc' ->
  exists nw, t' = app nw t.
Proof.
  destruct c as [c|].
  - induction c; intros * Hstep; inversion Hstep; subst
    ; try (eexists []; reflexivity).
    + eapply IHc1; eassumption.
    + eapply IHc1; eassumption.
    + exists ( [EvInput Public v] ) ; reflexivity.
    + exists ( [EvInput Secret v] ) ; reflexivity.
    + exists ( [EvOutput c v] ) ; reflexivity.
    + eapply IHc; eassumption.
    + eapply IHc; eassumption.
  - inversion 1.
Qed.

(* States precisely how the public projection grows when a public event
   is emitted by the execution step *)
Lemma exec_grow_trace j S P m t Γ pc ev j' S' P' m' t' Γ' pc':
  exec_with_gamma (j, S, P, m, t) Γ pc ev (j', S', P', m', t') Γ' pc' ->
  (⟦ t' ⟧p) = match ev with
              | Some (Input v) => EvInput Public v :: (⟦ t ⟧p)
              | Some (Output v) => EvOutput Public v :: (⟦ t ⟧p)
              | _ => (⟦ t ⟧p) end.
Proof.
  intros Hexec.
  destruct j; last by inversion Hexec.
  generalize dependent S; generalize dependent P;
    generalize dependent m; generalize dependent t; generalize dependent Γ;
    generalize dependent pc; generalize dependent j'; generalize dependent pc'.
  induction j; intros; inversion Hexec; subst => //.
  - destruct l => //. destruct (Γ !! s) => //. destruct c => //.
  - by eapply IHj1.
  - by eapply IHj1.
  - destruct (Γ !! s) => //. destruct c => //.
  - destruct c => //.
  - by eapply IHj.
  - by eapply IHj.
Qed.


(* If an execution of one step does not emit any public input/output,
   then the public projection of the trace does not change *)
Lemma exec_with_gamma_no_event j S P m t Γ pc j' S' P' m' t' Γ' pc' ev:
  match ev with | None | Some (WritePublic _ _) | Some (BecameSecret _) => True | _ => False end ->
  exec_with_gamma (j, S, P, m, t) Γ pc ev (j', S', P', m', t') Γ' pc' ->
  (⟦ t ⟧p) = (⟦ t' ⟧p).
Proof.
  intros Hev Hexec.
  destruct j; last by inversion Hexec.
  generalize dependent j'; generalize dependent S'; generalize dependent P';
    generalize dependent m'; generalize dependent t'; generalize dependent Γ';
    generalize dependent pc'.
  induction j; intros; inversion Hexec ; subst => //.
  - by eapply IHj1.
  - by eapply IHj1.
  - destruct c => //.
  - by eapply IHj.
  - by eapply IHj.
Qed.

(* If an execution step does no emit ANY public event, then
   public input stream does not change,
   the memories before and after agree on public,
   and the public projections does not change *)
Lemma exec_with_gamma_event_none j S P m t Γ pc j' S' P' m' t' Γ' pc':
(*  wf_memory m Γ -> *)
  exec_with_gamma (j, S, P, m, t) Γ pc None (j', S', P', m', t') Γ' pc' ->
  context_agree Γ Γ' /\ P = P' /\ agree_on_public Γ' m m' /\ (⟦ t ⟧p) = (⟦ t' ⟧p).
Proof.
  intros (* Hm *) Hexec.
  destruct j; last by inversion Hexec.
  generalize dependent j'; generalize dependent S'; generalize dependent P';
    generalize dependent m'; generalize dependent t'; generalize dependent Γ';
    generalize dependent pc'.
  induction j; intros; inversion Hexec ; subst => //.
  all: try by repeat split => //; try apply agree_refl.
  - destruct l => //. destruct (Γ !! s) eqn:Hs => //.
    + destruct c => //.
      repeat split => //. 
      rewrite fold_secret insert_id => //.
      apply agree_update_secret => //.
      rewrite lookup_insert. rewrite fold_secret. done.
(*      rewrite fold_secret. by apply wf_update_secret. *)
    + repeat split => //. rewrite fold_secret. by apply context_agree_add_secret.
      apply agree_update_secret => //.
      rewrite lookup_insert. rewrite fold_secret => //.
      (* rewrite fold_secret. by apply wf_update_secret. *)
  - by eapply IHj1.
  - by eapply IHj1.
  - destruct (Γ !! s) eqn:Hs => //.
    + destruct c => //. repeat split => //.
      rewrite insert_id => //. apply agree_update_secret => //.
      rewrite lookup_insert => //. (* by apply wf_update_secret. *)
    + repeat split => //. apply context_agree_add_secret => //.
      apply agree_update_secret => //.
      by rewrite lookup_insert. (* by apply wf_update_secret. *)
  - destruct c => //. repeat split => //. by apply agree_refl.
  - by eapply IHj.
  - by eapply IHj.
Qed.





(** Properties on the type system *)
Lemma jtyping_pc_flows Γ0 pc0 c Γf pcf:
  jtypecheck Γ0 pc0 (jcommand_of_command c) Γf pcf ->
  flows_pc pc0 pcf.
Proof.
  intro Hc.
  generalize dependent Γ0; generalize dependent pc0.
  generalize dependent Γf; generalize dependent pcf.
  induction c; intros; inversion Hc; subst => //; try reflexivity.
  - apply IHc1 in H3. apply IHc2 in H6. by etransitivity.
  - inversion H5; subst. inversion H8; subst.
    apply IHc1 in H3. apply IHc2 in H4.
    destruct H3 as [? H3]. destruct H4 as [? H4].
    eapply flows_join_pc; last done ; done.
Qed.

Lemma expr_type_flows Γ0 Γ1 e l1:
  Γ0 ⊑g Γ1 ->
  {{ Γ1 ⊢ e : l1 }} ->
  exists l0, flows l0 l1 /\ {{ Γ0 ⊢ e : l0 }}.
Proof.
  intros Hflow He1.
  generalize dependent l1.
  induction e; intros.
  - inversion He1; subst. eexists ; split; last econstructor; done.
  - inversion He1; subst. specialize (Hflow s). rewrite H1 in Hflow.
    destruct (Γ0 !! s) eqn:Hs0 => //.
    eexists; split => //. econstructor. done.
  - inversion He1; subst.
    apply IHe1 in H4 as (l1 & Hl1 & H1).
    apply IHe2 in H5 as (l2 & Hl2 & H2).
    eexists ; split; last econstructor => //.
    destruct l1, l2, ℓ1, ℓ2 => //.
Qed.

Lemma expr_type_flows_reverse Γ0 Γ1 e l1:
  flows_context Γ1 Γ0 ->
  {{ Γ1 ⊢ e : l1 }} ->
  exists l0, flows l1 l0 /\ {{ Γ0 ⊢ e : l0 }}.
Proof.
  intros Hflow He1.
  generalize dependent l1.
  induction e; intros.
  - inversion He1; subst. eexists ; split; last econstructor. done.
  - inversion He1; subst. specialize (Hflow s). rewrite H1 in Hflow.
    destruct (Γ0 !! s) eqn:Hs0 => //.
    eexists; split => //. econstructor. done.
  - inversion He1; subst.
    apply IHe1 in H4 as (l1 & Hl1 & H1).
    apply IHe2 in H5 as (l2 & Hl2 & H2).
    eexists ; split; last econstructor => //.
    destruct l1, l2, ℓ1, ℓ2 => //.
Qed.

Lemma typecheck_flow_gen Γ0 Γ1 pc0 pc1 c Γf0 pcf0 Γf1 pcf1 :
  flows_context Γ0 Γ1 ->
  flows_pc pc0 pc1 ->
  flows_context Γf1 Γf0 ->
  flows_pc pcf1 pcf0 ->
  jtypecheck Γ1 pc1 c Γf1 pcf1 ->
  jtypecheck Γ0 pc0 c Γf0 pcf0.
Proof.
  intros Hcontext Hpc Hcontextf Hpcf Hc.
  generalize dependent Γf1; generalize dependent pcf1.
  generalize dependent Γf0; generalize dependent pcf0.
  generalize dependent Γ1; generalize dependent pc1.
  generalize dependent Γ0; generalize dependent pc0.
  induction c; intros; inversion Hc; subst.
  - econstructor ; repeat (etransitivity => //).
  - destruct (expr_type_flows _ _ _ _ Hcontext H1) as (l0 & Hl0 & He).
    econstructor => //.
    + etransitivity.
      eapply flows_add. exact Hcontext.
      eapply flows_fold. exact Hl0. done.
      etransitivity => //.
    + repeat (etransitivity => //).
  - (* Seq *) econstructor.
    eapply IHc1 in H3 => //.
    eapply IHc2 in H6 => //.
  - (* If *)
    destruct (expr_type_flows _ _ _ _ Hcontext H2) as (l0 & Hl0 & He).
    rewrite (join_context_self Γf0). econstructor => //.
    3:{ by apply join_pc_idem. }
    + eapply IHc1. instantiate (1 := l :: _).
      simpl. split => //. done.
      3:exact H5.
      etransitivity ; [ by eapply flows_pc_join | done ].
      etransitivity ; [ by eapply flows_context_join | done ].
    + eapply IHc2. instantiate (1 := l :: _).
      simpl. split => //. done.
      3:exact H8.
      etransitivity; rewrite join_pc_comm in H9
      ; [ by eapply flows_pc_join | done ].
      etransitivity; rewrite join_context_comm in Hcontextf
      ; [by eapply flows_context_join | done ].
  (* - (* While *) *)
  (*   destruct (expr_type_flows_reverse _ _ _ _ Hcontextf H5) as (l0 & Hl0 & He). *)
  (*   econstructor => // ; try (repeat etransitivity => //). *)
  (*   + eapply IHc ; last done ; try done. *)
  (*     admit. *)
  (*     admit. *)
  - (* Input *)
    econstructor => //.
    + clear - H1 Hpc.
      apply flows_pc_fold in Hpc.
      by etransitivity.
    + clear - H4 Hcontext Hcontextf Hpc.
      do 2 (etransitivity; last done).
      apply flows_add ; first done.
      apply flows_fold; done.
    + repeat etransitivity => //.
  - (* Output *)
    destruct (expr_type_flows _ _ _ _ Hcontext H1) as (l0 & Hl0 & He).
    econstructor => //; try (repeat etransitivity => //).
    + clear -H2 Hl0 Hpc.
      do 2 (etransitivity; last done).
      apply flows_fold; done.
  - (* Join *)
    econstructor => //.
    eapply IHc ; last done ; try done.
Qed.

Lemma jtype_adequacy_reverse Γ0 pc0 c0 Γf pcf:
  jtypecheck Γ0 pc0 (jcommand_of_command c0) Γf pcf ->
  typecheck Γ0 (fold_left join pc0 LPublic) c0 Γf.
Proof.
  intros Hc0.
  generalize dependent Γf; generalize dependent pcf.
  generalize dependent Γ0; generalize dependent pc0.
  induction c0; intros; inversion Hc0; subst.
  - econstructor => //.
  - econstructor => //.
    rewrite - (fold_start pc0 le) join_comm in H4; done.
  - econstructor => //.
    eapply IHc0_1 => //. eapply IHc0_2 => //.
    apply jtyping_pc_flows in H3. eapply typecheck_flow_gen in H6; done.
  - inversion H5; subst. inversion H8; subst.
    econstructor => //.
    + apply IHc0_1 in H3; by rewrite fold_join in H3.
    + apply IHc0_2 in H4; by rewrite fold_join in H4.
  (* - econstructor => //. *)
  (*   apply IHc0 in H8. *)
  (*   admit. (* rewrite join, fold_left etc *) *)
  - econstructor => //.
    rewrite - fold_start join_comm in H4; done.
  - econstructor => //.
    rewrite fold_start; done.
Qed.


Lemma final_gamma j0 P0 S0 m0 t0 Γ0 pc0 ev P1 S1 m1 t1 Γ1 pc1 Γf pcf:
  jtypecheck Γ0 pc0 j0 Γf pcf ->
  exec_with_gamma
    ( Some j0 , P0, S0, m0, t0 ) Γ0 pc0
    ev
    ( None , P1, S1, m1, t1 ) Γ1 pc1 ->
  flows_context Γ1 Γf /\ flows_pc pc1 pcf.
Proof.
  intros Hj0 Hexec.
  generalize dependent pcf. generalize dependent pc1.
  induction j0; intros; inversion Hj0; inversion Hexec; subst => //.
  - split => //.
    rewrite (expr_type_unique _ _ _ _ H1 H24) in H4; done.
  - split => //.
    rewrite fold_secret in H4; done.
  - apply (IHj0 _ H19) in H2. destruct H2 as [HΓ Hpc]. split => //.
    by inversion Hpc.
Qed.


(** Preservation *)
Lemma jtype_preservation j0 P0 S0 m0 t0 Γ0 pc0 j1 P1 S1 m1 t1 Γ1 pc1 ev Γf pcf :
  wf_memory m0 Γ0 ->
  jtypecheck Γ0 pc0 j0 Γf pcf ->
  exec_with_gamma
    ( Some j0 , P0, S0, m0, t0 ) Γ0 pc0
    ev
    ( j1 , P1, S1, m1, t1 ) Γ1 pc1 ->
  wf_memory m1 Γ1 /\ match j1 with Some j1 => jtypecheck Γ1 pc1 j1 Γf pcf | None => True end.
Proof.
  intros Hm0 Hj0 Hexec.
  generalize dependent j1. generalize dependent Γf. generalize dependent pcf.
  generalize dependent pc1.
  induction j0; intros.
  - (* Skip *) inversion Hexec; subst => //.
  - (* Assign *) inversion Hexec; subst. split => //. by apply wf_update.
  - (* Seq *) inversion Hj0; subst. inversion Hexec; subst.
    + eapply IHj0_1 in H17 as [Hm1 Hc1'] => //.
      split => //.
      econstructor => //.
    + assert (Hexec' := H17). eapply IHj0_1 in H17 as [Hm1 _] => //.
      split => //.
      eapply final_gamma in Hexec' => //.
      destruct Hexec' as [Hcontextf Hpcf].
      eapply typecheck_flow_gen; try done.
  - (* IfThenElse *) inversion Hexec; subst => //.
    inversion Hj0; subst => //. split => //.
    eapply expr_type_unique in H2 as ->; last exact H17.
    destruct (v =? 0)%nat.
    + eapply typecheck_flow_gen; last done ; try done.
      rewrite join_context_comm; apply flows_context_join.
      rewrite join_pc_comm in H9; by eapply flows_pc_join.
    + eapply typecheck_flow_gen; last done ; try done.
      apply flows_context_join.
      by eapply flows_pc_join.
  - (* While *) inversion Hexec; subst => //. split => //. inversion Hj0; subst => //.
    (* admit. (* TODO is this even true ? *) *)
  - inversion Hexec; subst => //; split => //; by apply wf_update.
  - inversion Hexec; subst => //.
  - inversion Hj0; subst => //. inversion Hexec; subst => //.
    + eapply IHj0 in H15 as [Hm1 Hj'] => //. split => //.
      econstructor; done.
    + split => //. eapply IHj0 in H15 as [Hm1 _] => //.
Qed.

(** Adequacy typing *)
Lemma jtype_adequacy Γ0 pc0 c0 Γf pc:
  typecheck Γ0 pc0 c0 Γf ->
  fold_left join pc LPublic = pc0 ->
  jtypecheck Γ0 pc (jcommand_of_command c0) Γf pc.
Proof.
  intros Htype Hpc0.
  generalize dependent Γ0. generalize dependent Γf. generalize dependent pc.
  generalize dependent pc0.
  induction c0; intros; simpl;
    inversion Htype; subst; econstructor => //; try by apply flows_pc_refl.
  - rewrite - (fold_start pc le) join_comm. done.
  - eapply IHc0_1 => //.
  - eapply IHc0_2 => //.
  - econstructor. eapply IHc0_1. done. rewrite fold_join. done.
  - econstructor. eapply IHc0_2. done. by rewrite fold_join.
  - by apply join_pc_idem.
  (* - eapply IHc0 => //. by rewrite fold_join. *)
  - rewrite - (fold_start pc (confidentiality_of_channel _)). by rewrite join_comm.
  - rewrite - (fold_start pc le). done.
Qed.


(** Adequacy operational semantic *)
Lemma jcommand_adequacy Γ0 pc0 P0 S0 c0 m0 t0 c1 P1 S1 m1 t1 Γf:
  (* executing implies executing with gammas *)
  wf_memory m0 Γ0 ->
  -{ Γ0, pc0  ⊢ c0 ~> Γf }- ->
  ( Some c0 , P0, S0, m0, t0 ) ---> (c1, P1, S1, m1, t1) ->
  exists j1 Γ1 pc1 ev,
    exec_with_gamma
      ( Some (jcommand_of_command c0) , P0, S0, m0, t0 ) Γ0 [pc0]
      ev
      ( j1, P1, S1, m1, t1 ) Γ1 pc1  /\ option_map command_of_jcommand j1 = c1.
Proof.
  intros Hwf Htype Hstep.


  generalize dependent c1; generalize dependent Γf.
  induction c0; intros;
    try by inversion Hstep; subst; repeat eexists; econstructor.
  - inversion Hstep; subst. inversion Htype; subst.
    repeat eexists. econstructor => //. done.
  - inversion Htype; subst. inversion Hstep; subst.
    + eapply IHc0_1 in H0 as (j1 & Γ1 & pc1 & ev & Hexec & Ht).
      destruct j1 => //. repeat eexists. econstructor => //=.
      inversion Ht. simpl. rewrite command_id. done. done.
    + eapply IHc0_1 in H0 as (j1 & Γ1 & pc1 & ev & Hexec & Ht).
      destruct j1 => //. repeat eexists. eapply GSeq2 => //.
      simpl. rewrite command_id. done. done.
  - inversion Hstep; subst. inversion Htype; subst.
    eexists _,_,_,_. split. econstructor => //. simpl.
    destruct (v =? 0)%nat; simpl; rewrite command_id => //.
  - inversion Hstep; subst.
    repeat eexists. econstructor. simpl. rewrite command_id. done.
  - inversion Hstep; subst. inversion Htype; subst.
    repeat eexists. econstructor => //. simpl. rewrite join_comm in H5. done. done.
Qed.
