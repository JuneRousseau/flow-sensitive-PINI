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
  augmented
  map_simpl.

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
     inversion Ht; subst. destruct ℓ1 => //. destruct ℓ2 => //.
     rewrite (IHe1 v1 v0 H2 Hagree H4 H6).
     rewrite (IHe2 _ _ H9 Hagree H5 H7). done.
 Qed.


Lemma trace_monotone :
   forall c S P m t c' S' P' m' t',
     (c, S, P, m, t) ---> (c', S', P', m', t') ->
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
    - inversion 1.
  Qed.

  Lemma trace_grows :
    forall c S P m t c' S' P' m' t',
      (c, S, P, m, t) --->* (c', S', P', m', t') ->
      exists nw, t' = app nw t.
  Proof.
   intros * Hred.
   remember (c, S, P, m, t) as cfg in Hred.
   remember (c', S', P', m', t') as cfg' in Hred.
   induction Hred.
   (* No step -> no new event *)
   - rewrite Heqcfg' in Heqcfg.
     injection Heqcfg; intros ; subst.
     by exists [].
   (* -  *)
   (*   destruct y as [[[[ c''  S'' ]  P''  ] m'' ] t'' ]. *)
   (*   (* subst x. *) *)
   (*   apply trace_monotone in H. *)
   (* Multiple steps ->  *)
   (* - subst x z. *)
   (*   inversion H; subst. *)
   (*   apply IHHred. *)
 Admitted.

  Lemma project_app :
    forall t1 t2,
      ⟦ (t1 ++ t2)%list ⟧p = ((⟦ t1 ⟧p) ++ (⟦ t2 ⟧p))%list.
  Proof.
   intros t1; induction t1; intros.
   - reflexivity.
   - destruct a; cbn
     ; try apply IHt1
     ; destruct c; cbn
     ; try apply IHt1.
     all: rewrite IHt1 ; reflexivity.
 Qed.

 Lemma has_security_level :
   forall e m v Γ,
     e; m ⇓ v -> wf_memory m Γ -> exists l, {{Γ ⊢ e : l }}.
Proof.
  intros * Hv Hm.
  induction Hv.
  - by eexists; econstructor.
  - unfold wf_memory in Hm.
    specialize (Hm x). rewrite H in Hm.
    destruct (Γ !! x) eqn:Hx => //.
    exists c. by econstructor.
  - specialize (IHHv1 Hm) as [l1 He1].
    specialize (IHHv2 Hm) as [l2 He2].
    exists (join l1 l2). by econstructor.
Qed.


(* executing implies executing with gammas *)
Lemma can_exec_with_gamma Γ0 pc0 P0 S0 c0 m0 t0 c1 P1 S1 m1 t1 :
  wf_memory m0 Γ0 ->
  ( c0 , P0, S0, m0, t0 ) ---> (c1, P1, S1, m1, t1) ->
  exists j1 Γ1 pc1 ev,
    exec_with_gamma
      ( option_map jcommand_of_command c0 , P0, S0, m0, t0 ) Γ0 [pc0]
      ev
      ( j1, P1, S1, m1, t1 ) Γ1 pc1  /\ option_map command_of_jcommand j1 = c1.
Proof.
  intros Hwf Hstep.
  destruct c0 as [c0|]; [|by inversion Hstep].

  generalize dependent c1.
  induction c0; intros;
    try by inversion Hstep; subst; repeat eexists; econstructor.
  - inversion Hstep; subst.
    destruct (has_security_level _ _ _ _  H0 Hwf) as [l He].
    repeat eexists. econstructor => //. done.
  - inversion Hstep; subst.
    + apply IHc0_1 in H0 as (j1 & Γ1 & pc1 & ev & Hexec & Ht).
      destruct j1 => //. repeat eexists. econstructor => //=.
      inversion Ht. simpl. rewrite command_id. done.
    + apply IHc0_1 in H0 as (j1 & Γ1 & pc1 & ev & Hexec & Ht).
      destruct j1 => //. repeat eexists. eapply GSeq2 => //.
      simpl. rewrite command_id. done. 
  - inversion Hstep; subst.
    destruct (has_security_level _ _ _ _ H0 Hwf) as [l He].
    eexists _,_,_,_. split. econstructor => //. simpl.
    destruct (v =? 0)%nat; simpl; rewrite command_id => //.
  - inversion Hstep; subst.
    repeat eexists. econstructor. simpl. rewrite command_id. done.
Qed.

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

(*
Lemma jtype_pcf_while Γ0 pc0 e c Γf pcf:
  jtypecheck Γ0 pc0 (jcommand_of_command (WHILE e DO c END)) Γf pcf ->
  pc0 = pcf.
Proof.
  intros Hj.
  remember (jcommand_of_command (WHILE e DO c END)) as j.
  induction Hj; inversion Heqj; subst => //.
  apply IHHj2 => //.
Qed.
*)

Lemma jtype_pcf Γ0 pc0 c Γf pcf:
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

(*
Lemma jtype_adequacy_reverse_while Γ0 pc0 e c Γf pcf:
  jtypecheck Γ0 pc0 (jcommand_of_command (WHILE e DO c END)) Γf pcf ->
  typecheck Γ0 (fold_left join pc0 LPublic) (WHILE e DO c END) Γf.
Proof.
  intros Hj.
  remember (jcommand_of_command (WHILE e DO c END)) as j.
  induction Hj; inversion Heqj; subst => //. *)

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
    apply jtype_pcf in H3. eapply typecheck_flow_gen in H6; done.
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

Lemma expr_type_unique Γ e l1 l2:
  {{ Γ ⊢ e : l1 }} -> {{ Γ ⊢ e : l2 }} -> l1 = l2.
Proof.
  intros He1 He2.
  generalize dependent l1. generalize dependent l2.
  induction e; intros; inversion He1; inversion He2; subst => //.
  - rewrite H1 in H5. by inversion H5.
  - rewrite (IHe1 ℓ0 H11 ℓ1 H4).
    rewrite (IHe2 ℓ3 H12 ℓ2 H5). done.
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

Lemma wf_update m Γ x v vt :
  wf_memory m Γ ->
  wf_memory (<[ x := v ]> m) (<[ x := vt ]> Γ).
Proof.
  intros Hmem.
  destruct m using map_ind
  ; destruct Γ using map_ind
  ; intros ; intro y.
  (* m = ∅ *)
  - destruct (x =? y) eqn:Heq.
    + apply String.eqb_eq in Heq ; subst.
      by repeat (rewrite lookup_insert).
    + apply String.eqb_neq in Heq ; subst.
      by repeat (rewrite lookup_insert_ne).
  - exfalso ; clear -Hmem.
    unfold wf_memory in Hmem.
    specialize (Hmem i). by rewrite lookup_empty lookup_insert in Hmem.
  (* m = <[ x:= v ]> m' *)
  - exfalso ; clear -Hmem.
    unfold wf_memory in Hmem.
    specialize (Hmem i). by rewrite lookup_empty lookup_insert in Hmem.
  - clear IHm IHΓ.
    destruct (x =? y) eqn:Heq.
    + apply String.eqb_eq in Heq ; subst.
      by repeat (rewrite lookup_insert).
    + apply String.eqb_neq in Heq ; subst.
      rewrite lookup_insert_ne; first done.
      destruct (i =? y) eqn:Heqi.
      * apply String.eqb_eq in Heqi ; subst.
        repeat (rewrite lookup_insert).
        rewrite lookup_insert_ne; first done.
        destruct (i0 =? y) eqn:Heqi0.
        apply String.eqb_eq in Heqi0 ; subst.
        by repeat (rewrite lookup_insert).
        apply String.eqb_neq in Heqi0 ; subst.
        rewrite lookup_insert_ne; first done.
        destruct (m0 !! y) eqn:Hm0; first done.
        specialize (Hmem y).
        rewrite lookup_insert in Hmem.
        clear -Hmem Heqi0 Hm0.
        rewrite lookup_insert_ne in Hmem; first done.
        by rewrite Hm0 in Hmem.
      * apply String.eqb_neq in Heqi ; subst.
        rewrite lookup_insert_ne; first done.
        destruct (m !! y) eqn:Hy;
        rewrite lookup_insert_ne; try done.
        ** destruct (i0 =? y) eqn:Heqi0.
        *** apply String.eqb_eq in Heqi0 ; subst.
           by repeat (rewrite lookup_insert).
        *** apply String.eqb_neq in Heqi0 ; subst.
           rewrite lookup_insert_ne; first done.
           destruct (m0 !! y) eqn:Hy0; first done.
           specialize (Hmem y).
           rewrite lookup_insert_ne in Hmem; try done.
           rewrite Hy in Hmem.
           rewrite lookup_insert_ne in Hmem; try done.
           by rewrite Hy0 in Hmem.
        ** destruct (i0 =? y) eqn:Heqi0.
        *** apply String.eqb_eq in Heqi0 ; subst.
            rewrite lookup_insert.
            specialize (Hmem y).
            rewrite lookup_insert_ne in Hmem => //.
            rewrite Hy in Hmem.
            rewrite lookup_insert in Hmem => //.
        *** apply String.eqb_neq in Heqi0 ; subst.
           rewrite lookup_insert_ne; first done.
           destruct (m0 !! y) eqn:Hy0; last done.
           (* Contradiction with Hmem *)
           specialize (Hmem y).
           rewrite lookup_insert_ne in Hmem; try done.
           rewrite Hy in Hmem.
           rewrite lookup_insert_ne in Hmem; try done.
           by rewrite Hy0 in Hmem.
Qed.

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


(*
(* executing implies executing with gammas *)
Lemma can_exec_with_gamma_typed Γ0 pc0 P0 S0 c0 m0 t0 c1 P1 S1 m1 t1 Γf :
  wf_memory m0 Γ0 ->
  typecheck Γ0 pc0 c0 Γf ->
  ( Some c0 , P0, S0, m0, t0 ) ---> (c1, P1, S1, m1, t1) ->
  exists j1 Γ1 pc1 ev,
    exec_with_gamma
      ( Some (jcommand_of_command c0) , P0, S0, m0, t0 ) Γ0 [pc0]
      ev
      ( j1, P1, S1, m1, t1 ) Γ1 pc1  /\ option_map command_of_jcommand j1 = c1 /\
      wf_memory m1 Γ1 /\
      match j1 with Some j1 => exists pcf, jtypecheck Γ1 pc1 j1 Γf pcf | None => True end.
Proof.
  intros Hwf Hc0 Hstep.

  generalize dependent c1; generalize dependent Γf.
  induction c0; intros;
    try by inversion Hstep; subst; repeat eexists; [econstructor | done | done | done].
  - inversion Hstep; subst.
    destruct (has_security_level _ _ _ _  H0 Hwf) as [l He].
    repeat eexists. econstructor => //. all: try done.
    intro x. destruct (s =? x) eqn:Hsx.
    + apply String.eqb_eq in Hsx as ->.
      rewrite lookup_insert. rewrite lookup_insert. done.
    + apply String.eqb_neq in Hsx.       
      rewrite lookup_insert_ne. done.
      specialize (Hwf x).
      destruct (m0 !! x) eqn:Hm0; rewrite Hm0 => //; rewrite lookup_insert_ne => //.
  - inversion Hc0; subst. inversion Hstep; subst.
    + eapply IHc0_1 in H0 as (j1 & Γ1 & pc1 & ev & Hexec & Ht & Hm & Hc1); last exact H3.
      destruct j1 => //. repeat eexists. econstructor => //=.
      inversion Ht. simpl. rewrite command_id. done. done. simpl. econstructor. done. econstructor. done. 
    + apply IHc0_1 in H0 as (j1 & Γ1 & pc1 & ev & Hexec & Ht).
      destruct j1 => //. repeat eexists. eapply GSeq2 => //.
      simpl. rewrite command_id. done. 
  - inversion Hstep; subst.
    destruct (has_security_level _ _ _ _ H0 Hwf) as [l He].
    eexists _,_,_,_. split. econstructor => //. done.
Qed.  *) 

(*
(* executing implies executing with gammas *)
Lemma can_exec_with_gamma_trans Γ0 pc0 P0 S0 c0 m0 t0 s1 :
  wf_memory m0 Γ0 ->
  ( c0 , P0, S0, m0, t0 ) --->* s1 ->
  exists Γ1 pc1,
    exec_with_gamma_trans
      ( c0 , P0, S0, m0, t0) Γ0 pc0
      s1 Γ1 pc1.
Proof.
  intros Hwf Hstep.
  induction Hstep.
  - eexists; eexists; econstructor.
  - destruct IHHstep as (Γ1 & pc1 & IH).
    (* destruct x,st. as (S & P & m & t). *)
    (* destruct x,st,p,p. *)
    (* eapply can_exec_with_gamma in Hwf. *)
    (* + admit. *)
    (* + admit. *)
Admitted. *)



 (* Lemma bridge_adequacy : *)
 (*   forall n c pc Γ Γf m S P t cf Sf Pf mf tf, *)
 (*     typecheck Γ pc c Γf -> *)
 (*     wf_memory m Γ -> *)
 (*     (Some c, S, P, m, t) --->[n] (cf, Sf, Pf, mf, tf) -> *)
 (*     exists j Γ' ls', bridges (Some (jcommand_of_command c), S, P, m, t) Γ [pc] *)
 (*               (j, Sf, Pf, mf, tf) Γ' ls' /\ option_map command_of_jcommand j = cf. *)
 (* Proof. *)
 (*   intro n. *)
 (*   induction n; *)
 (*     intros * Hc Hm Hred. *)
 (*   { inversion Hred; subst. repeat eexists. econstructor. econstructor.  *)
 (*     simpl. by rewrite command_id. } *)

 (*   inversion Hred; subst. *)
 (*   destruct y as [[[[c1 S1] P1] m1] t1]. *)
 (*   destruct c1; last first. *)
 (*   - inversion H1; subst; last by inversion H. *)
 (*     eapply can_exec_with_gamma in H0 as (j1 & Γ1 & pc1 & ev & Hredg & Hj); last done. *)
 (*     destruct j1 => //. *)
 (*     destruct ev. *)
 (*     + repeat eexists. econstructor 2. apply BridgePublic. exact Hredg. *)
 (*       econstructor. econstructor. done. *)
 (*     + repeat eexists. econstructor 2. econstructor. exact Hredg. *)
 (*       econstructor. econstructor. done. *)
 (*   - eapply IHn in H1. *)

   (* destruct ev. *)
   (* - repeat eexists. econstructor 2. apply BridgePublic. exact Hredg. *)
   (*   rewrite Hj. exact H1. lia. *)
   (* - destruct n. *)
   (*   + destruct j1. *)
   (*     * right. inversion H1; subst. *)
   (*       repeat eexists. econstructor. exact Hredg. econstructor. *)
   (*     * left. simpl in Hj; subst. inversion H1; subst. repeat eexists. *)
   (*       econstructor. exact Hredg. instantiate (1 := 0). done. lia. *)
   (*   + destruct c1; last first. *)
   (*     { inversion H1. inversion H0. } *)
   (*     destruct j1 => //. inversion Hj; subst.  *)
   (*     assert (-{ Γ1, fold_left join pc1 LPublic ⊢ (command_of_jcommand j) ~> Γf }-). *)
 (* Admitted. *)
 
 Lemma bridge_adequacy :
   forall n c pc Γ Γf m S P t cf Sf Pf mf tf,
     typecheck Γ pc c Γf ->
     wf_memory m Γ ->
     (Some c, S, P, m, t) --->[n] (cf, Sf, Pf, mf, tf) ->
     (exists j S' P' m' t' Γ' ls' ev k n',
       bridge (Some (jcommand_of_command c), S, P, m, t) Γ [] k ev (j, S', P', m', t') Γ' ls' /\
         (option_map command_of_jcommand j, S', P', m', t') --->[n'] (cf, Sf, Pf, mf, tf) /\
         k + n' + 1 = n) \/
       (exists j Γ' ls,
           incomplete_bridge (Some (jcommand_of_command c), S, P, m, t) Γ [] n
             ( j, Sf, Pf, mf, tf ) Γ' ls /\ option_map command_of_jcommand j = cf).
 (* Proof. *)
   (* intro n. *)
   (* induction n; *)
   (*   intros * Hc Hm Hred. *)
   (* { inversion Hred; subst. right. repeat eexists. econstructor. simpl. *)
   (*   by rewrite command_id. } *)

   (* inversion Hred; subst. *)
   (* destruct y as [[[[c1 S1] P1] m1] t1].  *)
   (* eapply can_exec_with_gamma in H0 as (j1 & Γ1 & pc1 & ev & Hredg & Hj); last done. *)
   (* destruct ev. *)
   (* - left. repeat eexists. apply BridgePublic. exact Hredg. *)
   (*   rewrite Hj. exact H1. lia. *)
   (* - destruct n. *)
   (*   + destruct j1. *)
   (*     * right. inversion H1; subst. *)
   (*       repeat eexists. econstructor. exact Hredg. econstructor. *)
   (*     * left. simpl in Hj; subst. inversion H1; subst. repeat eexists. *)
   (*       econstructor. exact Hredg. instantiate (1 := 0). done. lia. *)
   (*   + destruct c1; last first. *)
   (*     { inversion H1. inversion H0. } *)
   (*     destruct j1 => //. inversion Hj; subst.  *)
   (*     assert (-{ Γ1, fold_left join pc1 LPublic ⊢ (command_of_jcommand j) ~> Γf }-). *)
   (*     admit.  *)
   (*     eapply IHn in H1 as *)
   (*         [ (j1 & S' & P' & m' & t' & Γ' & ls' & ev & k & n' & Hbr & Hfollow) | *)
   (*           (j1 & Γ' & ls & Hbr & Hj') ] => //. *)
   (*     * left. repeat eexists. eapply BridgeMulti. *)
   (*       exact Hredg. rewrite command_id in Hbr. exact Hbr.  *)


 Admitted.

 (* Lemma bridge_noninterference : *)
 (*   forall Γ m1 m2 c Γf ev1 ev2 n1 n2 c1 S1 S1' P P1 m1' t1 t1' c2 S2 S2' P2 m2' t2 t2' Γ1' Γ2', *)
 (*     agree_on_public Γ m1 m2 -> *)
 (*     (⟦ t1 ⟧p = ⟦ t2 ⟧p) ->  *)
 (*     typecheck Γ LPublic c Γf -> *)
 (*     bridge (Some c, S1, P, m1, t1) Γ [] n1 ev1 (c1, S1', P1, m1', t1') Γ1' [] -> *)
 (*     bridge (Some c, S2, P, m2, t2) Γ [] n2 ev2 (c2, S2', P2, m2', t2') Γ2' [] -> *)
 (*     c1 = c2 /\ *)
 (*       P1 = P2 /\ *)
 (*       Γ1' = Γ2' /\ *)
 (*       agree_on_public Γ1' m1' m2' /\ *)
 (*       ev1 = ev2 /\ *)
 (*       ⟦ t1' ⟧p = ⟦ t2' ⟧p *)
 (* . *)
 (* Proof. *)
 (* Admitted. *)

 (* Lemma bridge_preservation : *)
 (*   forall Γ c Γf m S P t k ev c' S' P' m' t' Γ', *)
 (*     typecheck Γ LPublic c Γf -> *)
 (*     wf_memory m Γ -> *)
 (*     bridge (Some c, S, P, m, t) Γ [] k ev (c', S', P', m', t') Γ' [] -> *)
 (*     wf_memory m' Γ' /\ match c' with None => True | Some c' => typecheck Γ' LPublic c' Γf end. *)
 (* Proof. *)
 (* Admitted. *)




 Lemma typecheck_is_sound :
   forall c S1 S2 P m1 m2 t1 t2 c1 c2 S1' S2' P1 P2 m1' m2' t1' t2' Γ Γf,
     typecheck Γ LPublic c Γf ->
     agree_on_public Γ m1 m2 ->
     wf_memory m1 Γ ->
     wf_memory m2 Γ ->
     (⟦ t1 ⟧p = ⟦ t2 ⟧p) ->
     (Some c, S1, P, m1, t1) --->* (c1, S1', P1, m1', t1') ->
     (Some c, S2, P, m2, t2) --->* (c2, S2', P2, m2', t2') ->
     length (⟦ t1' ⟧p) = length (⟦ t2' ⟧p) ->
     ⟦ t1' ⟧p = ⟦ t2' ⟧p.
 Proof.
   intros c S1 S2 P m1 m2 t1 t2 c1 c2 S1f S2f P1f P2f m1f m2f t1f t2f Γ Γf
     Hc Hm Hm1 Hm2 Ht Hred1 Hred2 Hlen.
   assert (Hred1' := Hred1).
    apply rtc_bsteps in Hred1 as [n1 Hred1].
    generalize dependent c; generalize dependent S1; generalize dependent S2;
    generalize dependent P; generalize dependent m1; generalize dependent m2;
    generalize dependent t1; generalize dependent t2; generalize dependent Γ.
    induction n1; intros.
    { inversion Hred1; subst. apply trace_grows in Hred2 as [? ->].
      rewrite project_app. rewrite project_app Ht in Hlen. rewrite app_length in Hlen.
      destruct (⟦ x ⟧p) => //. simpl in Hlen. lia. }
    apply bsteps_nsteps in Hred1 as (n & Hn & Hred1).
    eapply bridge_adequacy in Hred1; try exact Htype ; try done.
    destruct Hred1 as
       [ (c1' & S1' & P1' & m1' & t1' & Γ1' & ev1' & k1 & n1' & Hbr1 & Hred1 & Hn1) |
         <- ].
    2:{ apply trace_grows in Hred2 as [x ->]. rewrite project_app.
        rewrite project_app in Hlen.  rewrite app_length Ht in Hlen.
        destruct (⟦ x ⟧p) => //. simpl in Hlen. lia. } 
    apply rtc_nsteps in Hred2 as [n2 Hred2].
    eapply bridge_adequacy in Hred2; try exact Htype ; try done.    
     destruct Hred2 as
       [ (c2' & S2' & P2' & m2' & t2' & Γ2' & ev2' & k2 & n2' & Hbr2 & Hred2 & Hn2) |
         <- ].
     2:{ apply trace_grows in Hred1' as [x ->]. rewrite project_app.
         rewrite project_app Ht app_length in Hlen.
         destruct (⟦ x ⟧p) => //. simpl in Hlen; lia. }
     assert (Hbr2' := Hbr2).
     eapply bridge_noninterference in Hbr2 as (Hc12 & HP & HΓ & Hm' & Hev & Ht');
       try exact Hbr1; try done.
     subst.
     eapply bridge_preservation in Hbr1 as [Hm12 Hc2']; try done.
     eapply bridge_preservation in Hbr2' as [Hm12' Hc2'']; try done.
     destruct c2'; last first.
     { inversion Hred1; last by inversion H.
       subst.
       inversion Hred2; last by inversion H.
       subst.
       done. }
     eapply IHn1; last first. 
     eapply rtc_nsteps. eexists; exact Hred1.
     eapply rtc_nsteps. eexists; exact Hred2.
     eapply bsteps_nsteps; eexists; split; last exact Hred1.
     lia.
     all: try done.
Qed.
    

 
 Lemma typecheck_PINI :
   forall c Γ, typecheck ∅ LPublic c Γ -> PINI c.
 Proof.
   intros c Γ Htype.
   unfold PINI.
   intros P ev1 d t1 (Si1 & S1 & P1 & c1 & m1 & Hred1 & Ht1) S0.
   split.
   - intro Hk.
     apply PKnow.
     inversion Hk; subst.
     destruct H as (S2 & P2 & c2 & m2 & t2 & H).
     exists S2, P2, c2, m2, t2, ev1.
     exact H.
   - intro Hpk.
     apply Know.
     inversion Hpk; subst.
     destruct H as (S2 & P2 & c2 & m2 & t2 & ev2 & Hred2 & Ht2).
     replace ev1 with ev2.
     { exists S2, P2, c2, m2, t2. by split. }
     eapply typecheck_is_sound; last first.
     exact Hred1. exact Hred2. exact Ht1. exact Ht2. 2: exact Htype. done.
 Qed. 

     
    
       
     
     
     
     
     


(* executing implies executing with gammas *)
Lemma can_exec_with_gamma Γ0 pc0 P0 S0 c0 m0 t0 s1 :
  wf_memory m0 Γ0 ->
  ( c0 , P0, S0, m0, t0 ) ---> s1 ->
  exists Γ1 pc1,
    exec_with_gamma
      ( c0 , P0, S0, m0, t0 ) Γ0 pc0
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
  wf_memory m0 Γ0 ->
  ( c0 , P0, S0, m0, t0 ) --->* s1 ->
  exists Γ1 pc1,
    exec_with_gamma_trans
      ( c0 , P0, S0, m0, t0) Γ0 pc0
      s1 Γ1 pc1.
Proof.
  intros Hwf Hstep.
  induction Hstep.
  - eexists; eexists; econstructor.
  - destruct IHHstep as (Γ1 & pc1 & IH).
    (* destruct x,st. as (S & P & m & t). *)
    (* destruct x,st,p,p. *)
    (* eapply can_exec_with_gamma in Hwf. *)
    (* + admit. *)
    (* + admit. *)
Admitted.

Lemma type_preservation :
  forall c Γ pc Γf Γ' P S m t P' S' c' m' t' pc',
  -{ Γ, pc ⊢ c ~> Γf }- ->
  exec_with_gamma
    ( Some c , S, P, m, t )  Γ pc
    ( c' , S', P', m', t' )  Γ' pc' ->
  match c' with
  | Some c' => -{ Γ', pc' ⊢ c' ~> Γf }-
  | None => Γ' = Γf
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
Lemma separate_last_event S0 P0 c0 m0 t0 Γ0 pc0 S1 P1 c1 m1 a t1 Γ1 pc1 :
  exec_with_gamma_trans
    ( Some c0 , S0, P0, m0, t0) Γ0 pc0
    ( c1 , S1, P1, m1, a::t1) Γ1 pc1 ->
  exists S2 P2 c2 m2 Γ2 pc2 S3 P3 c3 m3 Γ3 pc3,
    exec_with_gamma_trans
    ( Some c0 , S0, P0, m0, t0) Γ0 pc0
    ( Some c2 , S2, P2, m2, t1) Γ2 pc2
    /\ exec_with_gamma
        ( Some c2 , S2, P2, m2, t1) Γ2 pc2
        ( c3 , S3, P3, m3, a::t1) Γ3 pc3
    /\ exec_with_gamma_trans
        ( c3 , S3, P3, m3, a::t1 ) Γ3 pc3
        ( c1 , S1, P1, m1, a::t1 ) Γ1 pc1.
Proof.
Admitted.

(* Same as the previous lemma, but with public events only *)
Lemma separate_last_public_event S0 P0 c0 m0 t0 Γ0 pc0 S1 P1 c1 m1 t1 a d Γ1 pc1:
  exec_with_gamma_trans
    ( Some c0 , S0, P0, m0, t0 ) Γ0 pc0
    ( c1 , S1, P1, m1, t1 ) Γ1 pc1 ->
  ⟦ t1 ⟧p = a :: d ->
  exists S2 P2 c2 m2 t2 Γ2 pc2 S3 P3 c3 m3 Γ3 pc3,
    exec_with_gamma_trans
    ( Some c0 , S0, P0, m0, t0 ) Γ0 pc0
    ( Some c2 , S2, P2, m2, t2 ) Γ2 pc2
    /\ ⟦ t2 ⟧p = d
    /\ exec_with_gamma
        ( Some c2 , S2, P2, m2, t2 ) Γ2 pc2
        ( c3 , S3, P3, m3, a::t2 ) Γ3 pc3
    /\ exec_with_gamma_trans
        ( c3 , S3, P3, m3, a::t2 ) Γ3 pc3
        ( c1 , S1, P1, m1, t1 ) Γ1 pc1.
Proof.
Admitted.

(* One can add a public event to both sides of a public projection *)
Lemma public_projection_cons t a d t' d':
  ⟦ t ⟧p = a :: d ->
  ⟦ t' ⟧p = d' ->
  ⟦ a :: t' ⟧p  = a :: d'.
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
Lemma exec_both_some S1 P1 c m1 t1 Γ1 pc1 S1' P1' c1' m1' t1' Γ1' pc1'
  S2 P2 m2 t2 Γ2 pc2 S2' P2' c2' m2' t2' Γ2' pc2':
  exec_with_gamma
    ( Some c , S1, P1, m1, t1 ) Γ1 pc1
    ( c1' , S1', P1', m1', t1' ) Γ1' pc1' ->

  exec_with_gamma
    ( Some c , S2, P2, m2, t2 ) Γ2 pc2
    ( c2' , S2', P2', m2', t2' ) Γ2' pc2' ->

  match c1', c2' with
  | Some _, Some _ | None, None => True
  | _,_ => False end.

Proof.
  intros Hex1 Hex2.
  inversion Hex1; subst;
    inversion Hex2; subst => //.
Qed.

Lemma set_var_agree Γ (m1 m2 : memory) x v l :
  agree_on_public Γ m1 m2 ->
  agree_on_public (<[ x := l ]> Γ)
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
  forall c Γ pc Γ' t1 t2 d a1 a2 S1 P m1 S1' P1' c1' m1' Γ1 pc1
    S2 m2 S2' P2' c2' m2' Γ2 pc2,
  -{ Γ , pc ⊢ c ~> Γ' }- ->
  ⟦ t1 ⟧p = d ->
  ⟦ t2 ⟧p = d ->
  ⟦ (a1 :: t1) ⟧p = a1 :: d ->
  ⟦ (a2 :: t2) ⟧p = a2 :: d ->
  agree_on_public Γ m1 m2 ->
  exec_with_gamma
    ( Some c , S1, P, m1, t1 ) Γ pc
    ( c1' , S1', P1', m1', a1 :: t1 ) Γ1 pc1 ->
  exec_with_gamma
    ( Some c , S2, P, m2, t2 ) Γ pc
    ( c2' , S2', P2', m2', a2:: t2 ) Γ2 pc2 ->
  Γ1 = Γ2
  /\ pc1 = pc2
  /\ P1' = P2'
  /\ c1' = c2'
  /\ agree_on_public Γ1 m1' m2'
  /\ a1 = a2.
Proof.
  induction c;
    intros gamma pc gamma' t1 t2 d a1 a2 S1 P m1 S1' P1' c1' m1' gamma1 pc1 S2 m2
    S2' P2' c2' m2' gamma2 pc2 Ht Ht1 Ht2 Ha1 Ha2 Hmem Hex1 Hex2;
    try by inversion Hex1; subst; exfalso; apply (list_is_finite a1 t1).
  - inversion Hex1; subst.
    + inversion Hex2; subst.
      * inversion Ht.
        assert (public_projection t1 = public_projection t1) as Htriv => //.
        subst.
        edestruct (IHc1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                     H3 Htriv Ht2 Ha1 Ha2 Hmem H14 H15)
          as (-> & -> & -> & ? & ? & ->).
        inversion H; subst. by repeat split.
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
  forall d1 a1 a2 d2 c Γ Sinit1 P S1 P1 c1 m1 t1 Γ1 pc1 S1' P1' c1' m1' Γ1' pc1'
    Sinit2 S2 P2 c2 m2 t2 Γ2 pc2 S2' P2' c2' m2' Γ2' pc2',

    length d1 = length d2 ->
    -{ ∅ , LPublic ⊢ c ~> Γ }- ->

    exec_with_gamma_trans
      ( Some c , Sinit1, P, minit, [] ) ∅ LPublic
      ( Some c1 , S1, P1, m1, t1 ) Γ1 pc1 ->
    ⟦ t1 ⟧p = d1 ->
    exec_with_gamma
      ( Some c1 , S1, P1, m1, t1 ) Γ1 pc1
      ( c1' , S1', P1', m1', a1 :: t1 ) Γ1' pc1' ->
    ⟦ a1 :: t1 ⟧p = a1 :: d1 ->

    exec_with_gamma_trans
      ( Some c , Sinit2, P, minit, [] ) ∅ LPublic
      ( Some c2 , S2, P2, m2, t2 ) Γ2 pc2 ->
    ⟦ t2 ⟧p = d2 ->
    exec_with_gamma
      ( Some c2 , S2, P2, m2, t2 ) Γ2 pc2
      ( c2' , S2', P2', m2', a2 :: t2 ) Γ2' pc2' ->
    ⟦ a2 :: t2 ⟧p = a2 :: d2 ->

    Γ1 = Γ2
    /\ pc1 = pc2
    /\ P1 = P2
    /\ c1 = c2
    /\ agree_on_public Γ1 m1 m2
    /\ a1 = a2
    /\ d1 = d2.
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
  forall c Γ, typecheck ∅ LPublic c Γ -> PINI c.
Proof.
  intros c gamma Ht.
  unfold PINI.
  intros P a d t Had.
  split.
  (* Case K(P,c, a::d, S) -> PK(P,c,d,S) *)
  (* This direction is trivial *)
  { intro Hk.
    apply PKnow. inversion Hk; subst.
    destruct H as (S' & P' & c' & m' & t' & H).
    exists S', P', c', m', t', a.
    exact H. }
  (* Case PK(P,c,d,S) -> K(P,c, a::d, S) *)
  intro Hpk.
  apply Know.
  inversion Hpk; subst.
  destruct H as (S' & P' & c' & m' & t' & a0 & Hexec & Hp0).
  destruct Had as (S0 & S1 & P1 & c1 & m1 & Hexec0 & Hp).
  replace a with a0. exists S', P',c', m', t'. split => //.
  apply (can_exec_with_gamma_trans ∅ LPublic) in Hexec0 as (gamma1 & pc1 & Hexec0);
    last done.
  destruct (separate_last_public_event _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hexec0 Hp)
    as (S1m & P1m & c1m & m1m & t1m & gamma1m & pc1m &
          S1p & P1p & c1p & m1p & gamma1p & pc1p & Hex1m & Ht1m & Hex1c & Hex1p).
  apply (can_exec_with_gamma_trans ∅ LPublic) in Hexec as (gamma2 & pc2 & Hexec);
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
