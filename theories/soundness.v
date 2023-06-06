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
  bridges
  properties
  map_simpl.

(** Adequacy of the (full)-bridge relation *)

Lemma bridge_adequacy :
  forall n c pc Γ Γf m S P t cf Sf Pf mf tf,
  typecheck Γ pc c Γf ->
  wf_memory m Γ ->
  (Some c, S, P, m, t) --->[n] (cf, Sf, Pf, mf, tf) ->
  exists j Γ' ls' evs, bridge (Some (jcommand_of_command c), S, P, m, t) Γ [pc] evs
                    (j, Sf, Pf, mf, tf) Γ' ls' /\ option_map command_of_jcommand j = cf /\
                    trace_of_public_trace evs = (⟦ tf ⟧p).
Proof.
Admitted.

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

(** Agreements theorems *)

(* TODO explain the lemma *)
Lemma exec_agree j S1 P m1 t1 Γ1 pc ev j1 S1f P1f m1f t1f Γf1 pc1 S2 m2 t2 Γ2 ev' j2 S2f P2f m2f t2f Γf2 pc2:
  agree_on_public Γ1 m1 m2 ->
  (⟦ t1 ⟧p) = (⟦ t2 ⟧p) ->
  context_agree Γ1 Γ2 ->
  exec_with_gamma (Some j , S1 , P , m1 , t1) Γ1 pc
    (Some ev)
    (j1, S1f, P1f, m1f, t1f ) Γf1 pc1 ->
  exec_with_gamma (Some j, S2, P, m2, t2 ) Γ2 pc
    (Some ev')
    (j2, S2f, P2f, m2f, t2f ) Γf2 pc2 ->
  ev = ev' /\ j1 = j2 /\ P1f = P2f /\ context_agree Γf1 Γf2 /\ pc1 = pc2 /\ agree_on_public Γf1 m1f m2f /\ (⟦ t1f ⟧p) = (⟦ t2f ⟧p).
Proof.
  intros Hm Ht HΓ Hex1 Hex2.
  generalize dependent j1; generalize dependent j2; generalize dependent pc2;
    generalize dependent pc1.
  induction j; intros; inversion Hex1; inversion Hex2; subst.
  - eapply expr_type_agree in H36; last exact H16. 2: done. subst. destruct l0 => //.
    + eapply eval_expr_public in H35; try exact H15. 2: done. 2: done.
      subst. rewrite - H38 in H18. inversion H18; subst.
      repeat split => //. by apply context_agree_update. by apply agree_update.
    + destruct (Γ1 !! s) => //. destruct (Γ2 !! s) => //. destruct c, c0 => //.
      rewrite - H18 in H38. inversion H38; subst.
      repeat split => //. rewrite fold_secret. by apply context_agree_update.
      rewrite fold_secret. by apply agree_update_secret2.
  - eapply IHj1 in H15. 2:exact H32.
    destruct H15 as (-> & Hc & -> & HΓf & -> & Hmf & Htf).
    inversion Hc; subst. repeat split => //.
  - eapply IHj1 in H15. 2:exact H32.
    destruct H15 as (_ & ? & _) => //.
  - eapply IHj1 in H15. 2: exact H32.
    destruct H15 as (_ & ? & _) => //.
  - eapply IHj1 in H15. 2: exact H32.
    destruct H15 as (-> & _ & -> & HΓf & -> & Hmf & Htf).
    repeat split => //.
  - inversion H20; subst. repeat split => //.
    by apply context_agree_update. by apply agree_update.
    simpl. by rewrite Ht.
  - destruct (Γ2 !! s) => //.
  - destruct (Γ1 !! s) => //.
  - destruct (Γ1 !! s) => //. destruct (Γ2 !! s) => //. destruct c,c0 => //.
    rewrite - H34 in H16; inversion H16; subst.
    repeat split => //. by apply context_agree_update. by apply agree_update_secret2.
  - destruct c => //. 
    eapply eval_expr_public in H35; try exact H16; try done.
    subst. rewrite - H18 in H38. inversion H38; subst. repeat split => //.
    simpl. by rewrite Ht.
    destruct l => //. rewrite fold_secret in H17. done.
  - eapply IHj in H14. 2:exact H30.
    destruct H14 as (-> & Hj & -> & HΓf & -> & Hmf & Htf).
    inversion Hj; subst. repeat split => //.
  - eapply IHj in H14. 2: exact H30.
    destruct H14 as (_ & ? & _) => //.
  - eapply IHj in H14. 2: exact H30.
    destruct H14 as (_ & ? & _) => //.
  - eapply IHj in H14. 2: exact H30.
    destruct H14 as (-> & _ & -> & HΓf & Hpc & Hmf & Htf).
    inversion Hpc; subst.
    repeat split => //.
Qed.

(* TODO explain the lemma *)
Lemma exec_disagree j S1 P m1 t1 Γ1 pc ev j1 S1f P1f m1f t1f Γf1 pc1 S2 m2 t2 Γ2 j2 S2f P2f m2f t2f Γf2 pc2:
  agree_on_public Γ1 m1 m2 ->
  (⟦ t1 ⟧p) = (⟦ t2 ⟧p) ->
  context_agree Γ1 Γ2 ->
  exec_with_gamma (Some j , S1 , P , m1 , t1) Γ1 pc
    (Some ev)
    (j1, S1f, P1f, m1f, t1f ) Γf1 pc1 ->
  exec_with_gamma (Some j, S2, P, m2, t2 ) Γ2 pc
    None
    (j2, S2f, P2f, m2f, t2f ) Γf2 pc2 ->
  False.
Proof.
  intros Hm Ht HΓ Hex1 Hex2.
  generalize dependent j1; generalize dependent j2; generalize dependent pc2;
    generalize dependent pc1.
  induction j; intros; inversion Hex1; inversion Hex2; subst.
  - eapply expr_type_agree in H36; last exact H16. 2: done. subst. destruct l0 => //.
    specialize (HΓ s). 
    destruct (Γ1 !! s) => //. destruct c => //.
    destruct (Γ2 !! s) => //. destruct c => //.
  - eapply IHj1 in H15. 2:exact H32. done.
  - eapply IHj1 in H15. 2:exact H32. done.
  - eapply IHj1 in H15. 2: exact H32. done.
  - eapply IHj1 in H15. 2: exact H32. done.
  - done.
  - specialize (HΓ s). destruct (Γ1 !! s) => //. destruct c => //.
    destruct (Γ2 !! s) => //. destruct c => //.
  - destruct c => //.
  - eapply IHj in H14. 2:exact H30. done.
  - eapply IHj in H14. 2: exact H30. done.
  - eapply IHj in H14. 2: exact H30. done.
  - eapply IHj in H14. 2: exact H30. done.
Qed.

Lemma write_bridge_agree j S P m t Γ pc k evs j' S' P' m' t' Γ' pc':
  write_bridge (j, S, P, m, t) Γ pc k evs (j', S', P', m', t') Γ' pc' ->
  (⟦ t ⟧p) = (⟦ t' ⟧p).
Proof.
  intros Hbr.
  generalize dependent j; generalize dependent S; generalize dependent P;
    generalize dependent m; generalize dependent t; generalize dependent Γ;
    generalize dependent pc.
  induction k; intros; inversion Hbr; subst.
  - apply exec_with_gamma_no_event in H14 => //.
  - apply exec_with_gamma_no_event in H15 => //.
    apply IHk in H16 => //. by rewrite H15 H16.
Qed.


Lemma write_bridges_agree j S P m t Γ pc k evs j' S' P' m' t' Γ' pc':
  write_bridges (j, S, P, m, t) Γ pc k evs (j', S', P', m', t') Γ' pc' ->
  (⟦ t ⟧p) = (⟦ t' ⟧p).
Proof.
  intros Hbr.
  generalize dependent j; generalize dependent S; generalize dependent P;
    generalize dependent m; generalize dependent t; generalize dependent Γ;
    generalize dependent pc; generalize dependent evs.
  induction k; intros; inversion Hbr; subst.
  - done.
  - destruct jc' as [[[[??]?]?]?]. apply write_bridge_agree in H0 => //.
    apply IHk in H4 => //. by rewrite H0 H4.
Qed.


Lemma silent_bridge_agree j S P m t Γ pc k j' S' P' m' t' Γ' pc':
  silent_bridge (j, S, P, m, t) Γ pc k (j', S', P', m', t') Γ' pc' ->
  context_agree Γ Γ' /\
  P = P' /\ agree_on_public Γ' m m' /\ (⟦ t ⟧p = ⟦ t' ⟧p).
Proof.
  intros Hbr.
  destruct j; last first.
  { inversion Hbr; subst. repeat split. by apply reflexive_context_agree.
    by apply agree_refl. } 
  generalize dependent j; generalize dependent S; generalize dependent P;
       generalize dependent m; generalize dependent t; generalize dependent Γ;
       generalize dependent pc.
  induction k; intros; inversion Hbr; subst => //.
  { repeat split => //. by apply agree_refl. } 
  destruct c'; last first.
  { inversion H15; subst. apply exec_with_gamma_event_none in H14 => //. }
  eapply IHk in H15 as (HΓ & -> & Hm & H16).
  rewrite - H16.
  eapply exec_with_gamma_event_none in H14 as (HΓ' & -> & Hm' & Ht').
  repeat split => //. eapply transitive_context_agree => //. eapply transitive_agree_pub => //.
  by eapply agree_on_agree.
Qed.


(*
   Lemma silent_bridge_agree j S1 P m1 t1 Γ pc k S1f P1f m1f t1f Γ1 pc1 S2 m2 t2 k' S2f P2f m2f t2f Γ2 pc2:
     agree_on_public Γ m1 m2 ->
     (⟦ t1 ⟧p) = (⟦ t2 ⟧p) ->
     silent_bridge (Some j , S1 , P , m1 , t1) Γ pc
       k
       (None, S1f, P1f, m1f, t1f ) Γ1 pc1 ->
     silent_bridge (Some j, S2, P, m2, t2 ) Γ pc
       k'
       (None, S2f, P2f, m2f, t2f ) Γ2 pc2 ->
     k = k' /\ P1f = P2f /\ Γ1 = Γ2 /\ pc1 = pc2 /\ agree_on_public Γ1 m1f m2f /\ (⟦ t1f ⟧p) = (⟦ t2f ⟧p).
   Proof.
     intros Hm Ht Hbr1 Hbr2.
     induction k; intros; inversion Hbr1; inversion Hbr2; subst => //=.
 *)


(* TODO explain the lemma *)
Lemma basic_bridge_sequence j1 j2 S P m t Γ pc n ev j' S' P' m' t' Γ' pc':
  basic_bridge (Some (JSeq j1 j2), S, P, m, t) Γ pc n ev (j', S', P', m', t') Γ' pc' ->
  (exists k Sm Pm mm tm Γm pcm,
      k < Datatypes.S n
      /\ silent_bridge (Some j1, S, P, m, t) Γ pc
          k
          (None, Sm, Pm, mm, tm) Γm pcm
      /\ basic_bridge (Some j2, Sm, Pm, mm, tm) Γm pcm
          (n - k) ev
          (j', S', P', m', t') Γ' pc')
  \/
    (exists j1', basic_bridge (Some j1, S, P, m, t) Γ pc
              n ev
              (j1', S', P', m', t') Γ' pc'
            /\ j' = match j1' with Some j1' => Some (JSeq j1' j2) | None => Some j2 end).
Proof.
  intros Hbr.
  generalize dependent j1; generalize dependent S; generalize dependent P
  ; generalize dependent m; generalize dependent t; generalize dependent Γ
  ; generalize dependent pc.
  induction n; intros; inversion Hbr; subst.
  - inversion H14; subst; right; eexists; split; try by econstructor; try done.
  - inversion H15; subst.
    + apply IHn in H16 as [ (k & Sm & Pm & mm & tm & Γm & pcm & Hk & Hib & Hb)
                          | (j1' & Hb & Hj') ].
      * left. repeat eexists. instantiate (1 := Datatypes.S _).
        2:{ econstructor. 2: exact Hib. done. }
        lia. exact Hb.
      * right. eexists. split => //. econstructor. exact H17. exact Hb.
    + left. repeat eexists. instantiate (1 := Datatypes.S _).
      2:{ econstructor. done. econstructor. }
      lia. replace (Datatypes.S n - 1) with n; last lia. exact H16.
Qed.

 Lemma basic_bridge_agree: forall k j k' S1 P m1 t1 Γ1 pc ev j1 S1f P1f m1f t1f Γf1 pc1 S2 m2 t2 Γ2 ev' j2 S2f P2f m2f t2f Γf2 pc2,
     agree_on_public Γ1 m1 m2 ->
     (⟦ t1 ⟧p) = (⟦ t2 ⟧p) ->
     context_agree Γ1 Γ2 ->
     basic_bridge (Some j , S1 , P , m1 , t1) Γ1 pc
       k ev
       (j1, S1f, P1f, m1f, t1f ) Γf1 pc1 ->
     basic_bridge (Some j, S2, P, m2, t2 ) Γ2 pc
       k' ev'
       (j2, S2f, P2f, m2f, t2f ) Γf2 pc2 ->
     ev = ev' /\ j1 = j2 /\ P1f = P2f /\ context_agree Γf1 Γf2 /\ pc1 = pc2 /\ agree_on_public Γf1 m1f m2f /\ (⟦ t1f ⟧p) = (⟦ t2f ⟧p).
   Proof.
   Admitted.
   (* Proof attempt:
     (*     intros Hm Ht Hbr1 Hbr2. *)
     intros k.
     remember k as kind; rewrite Heqkind.
     assert (k <= kind) as Hk; first lia.
     clear Heqkind.
     generalize dependent k.
     (* generalize dependent j; generalize dependent S1; generalize dependent P;

       generalize dependent m1; generalize dependent t1; generalize dependent Γ;
       generalize dependent pc; generalize dependent S2; generalize dependent m2;
       generalize dependent t2; generalize dependent k. *)
     induction kind.
     - intros * Hk * Hm Ht HΓ Hbr1 Hbr2. destruct k; last lia.
       inversion Hbr1; inversion Hbr2; subst.
         eapply exec_agree in H31. 5: exact H14. all: try done.
         eapply exec_disagree in H31. 5: exact H14. all: try done.
     - (*generalize dependent S1; generalize dependent P; generalize dependent m1;
         generalize dependent t1; generalize dependent Γ; generalize dependent pc;
         generalize dependent S2; generalize dependent m2; generalize dependent t2;
           generalize dependent k. *)
       intros k Hkind j.
       generalize dependent k.
       induction j; intros * Hkind * Hm Ht HΓ Hbr1 Hbr2.
         + inversion Hbr1; subst; inversion H15.
         + inversion Hbr1; subst; inversion H15.
           subst. eapply (IHkind 0) => //. lia.
         + apply basic_bridge_sequence in Hbr1 as
             [ (k1 & Sm1 & Pm1 & mm1 & tm1 & Γm1 & pcm1 & Hk1 & Hib1 & Hb1)
             | (j1' & Hb1 & Hj'1) ];
             apply basic_bridge_sequence in Hbr2 as
               [ (k2 & Sm2 & Pm2 & mm2 & tm2 & Γm2 & pcm2 & Hk2 & Hib2 & Hb2)
               | (j2' & Hb2 & Hj'2) ].
           * apply silent_bridge_agree in Hib1 as (HΓ1 & -> & Hm1 & Ht1).
             apply silent_bridge_agree in Hib2 as (HΓ2 & -> & Hm2 & Ht2).
             eapply IHj2 in Hb1 as (-> & -> & -> & HΓf & -> & Hmf & Htf).
             
             6: exact Hb2.
             repeat split => //. lia. by rewrite - Ht1 Ht.
             admit.

         eapply IHk in H16. 4: exact H34.


       intros Hm Ht Hbr1 Hbr2.
     generalize dependent j; generalize dependent S1; generalize dependent P;
       generalize dependent m1; generalize dependent t1; generalize dependent Γ;
       generalize dependent pc; generalize dependent S2; generalize dependent m2;
       generalize dependent t2.
     induction k; intros ; inversion Hbr1; inversion Hbr2; subst.
     - eapply exec_agree in H31. 4: exact H14. 2: done. 2: done.
       destruct H31 as (-> & -> & -> & -> & -> & Hmf & Htf).
       repeat split => //.
     - eapply exec_disagree in H31. 4: exact H14. all:done.
     - eapply exec_disagree in H15. 4: exact H33. done. by apply agree_on_public_comm.
       done.
     - induction j; inversion H15; inversion H33; subst.
       + apply bridge_sequence in H16 as
             [ (k1 & Sm1 & Pm1 & mm1 & tm1 & Γm1 & pcm1 & Hk1 & Hib1 & Hb1)
             | (j1' & Hb1 & Hj'1) ];
         apply bridge_sequence in H34 as
             [ (k2 & Sm2 & Pm2 & mm2 & tm2 & Γm2 & pcm2 & Hk2 & Hib2 & Hb2)
             | (j2' & Hb2 & Hj'2) ].
         * eapply IHj1 .

         eapply IHk in H16. 4: exact H34.
     uasinasn
   Admitted.
 *)

(* TODO explain lemma *)
Lemma final_nw_bridges_agree j S1 P m1 t1 Γ1 pc k1 j1 S1f P1f m1f t1f Γf1 pc1 S2 m2 t2 k2 Γ2 j2 S2f P2f m2f t2f Γf2 pc2 Γf pcf evs1 evs2:
  jtypecheck Γ1 pc j Γf pcf ->
  wf_memory m1 Γ1 ->
  agree_on_public Γ1 m1 m2 ->
  (⟦ t1 ⟧p) = (⟦ t2 ⟧p) ->
  context_agree Γ1 Γ2 ->
  length (⟦ t1f ⟧p) = length (⟦ t2f ⟧p) ->
  final_nw_bridges (Some j, S1, P, m1, t1) Γ1 pc
    k1 evs1 (j1, S1f, P1f, m1f, t1f) Γf1 pc1 ->
  final_nw_bridges (Some j, S2, P, m2, t2) Γ2 pc
    k2 evs2 (j2, S2f, P2f, m2f, t2f) Γf2 pc2 ->
  k1 = k2 /\ j1 = j2 /\ P1f = P2f /\ context_agree Γf1 Γf2 /\ pc1 = pc2
  /\ agree_on_public Γf1 m1f m2f /\ evs1 = evs2.
Proof.
  intros Htype Hwf Hm Ht HΓ Hlen Hred1 Hred2.
  generalize dependent j; generalize dependent S1 ; generalize dependent m1;
    generalize dependent t1; generalize dependent evs1;
    generalize dependent S2; generalize dependent m2;
    generalize dependent t2; generalize dependent evs2;
    generalize dependent P; generalize dependent k2;
    generalize dependent Γ1; generalize dependent Γ2; generalize dependent pc.
  induction k1; intros; inversion Hred1; subst.
  - inversion Hred2; subst.
    + eapply basic_bridge_agree in H2.
      5: exact H0. 3: done. 2: done. 2: done.
      destruct H2 as (-> & -> & -> & HΓ' & -> & Hm' & Ht').
      repeat split => //. 
    + assert (H0' := H0).
      apply basic_bridge_grow_trace in H0.
      destruct jc' as [[[[??]?]?]?].
      assert (H1' := H1).
      apply basic_bridge_grow_trace in H1.
      apply final_nw_bridges_grow_trace in H2.
      rewrite - Hlen H1 H0 Ht in H2.
      eapply basic_bridge_agree in H1'.
      5: exact H0'. all: try done. 
      destruct H1' as (-> & _).
      destruct ev0 => //; simpl in H2; lia.
  - inversion Hred2; subst.
    + assert (H0' := H0). assert (H1' := H1).
      destruct jc' as [[[[??]?]?]?].
      apply basic_bridge_grow_trace in H0.
      apply final_nw_bridges_grow_trace in H4.
      apply basic_bridge_grow_trace in H1.
      rewrite Hlen H0 H1 Ht in H4.
      eapply basic_bridge_agree in H1'.
      5: exact H0'. all: try done.
      destruct H1' as (-> & _).
      destruct ev0 => //; simpl in H4; lia.
    + destruct jc'0 as [[[[ j0 S0 ] P0 ] m0 ] t0].
      destruct jc' as [[[[ j' S' ] P' ] m' ] t'].
      eapply basic_bridge_agree in H.
      5: exact H0. all: try done.
      destruct H as (-> & -> & -> & HΓ' & -> & Hm' & Ht').
      destruct j0.
      2:{ apply final_nw_bridges_none in H4 => //. }
      eapply IHk1 in H4.
      7: exact H1.
      destruct H4 as (-> & -> & -> & HΓf & -> & Hmf & ->).
      repeat split => //.
      all: try done.
      eapply preservation_basic_bridge in H0 as [??] => //.
      eapply preservation_basic_bridge in H0 as [??] => //.
Qed.


(* TODO explain lemmas and the different steps *)
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
  apply rtc_nsteps in Hred1 as [n1 Hred1].
  eapply bridge_adequacy in Hred1 as (j1 & Γf1 & pcf1 & k1 & Hred1 & Hj1 & Hk1) => //.
  apply rtc_nsteps in Hred2 as [n2 Hred2].
  eapply bridge_adequacy in Hred2 as (j2 & Γf2 & pcf2 & k2 & Hred2 & Hj2 & Hk2) => //.
  inversion Hred2; subst.
  - inversion Hred1; subst.
    + destruct jc1 as [[[[??]?]?]?].
      destruct jc2 as [[[[??]?]?]?].
      destruct jc3 as [[[[??]?]?]?].
      destruct jc4 as [[[[??]?]?]?].
      eapply final_nw_bridges_agree in H.
      8: exact H2.
      do 6 destruct H as [_ H]. rewrite H in Hk1. rewrite Hk1 in Hk2. done.
      eapply jtype_adequacy. done. done. done. done. done. done.
      apply silent_bridge_agree in H4 as (_ & _ & _ & Htf1).
      apply silent_bridge_agree in H1 as (_ & _ & _ & Htf2).
      apply write_bridges_agree in H3 as Ht3.
      apply write_bridges_agree in H0 as Ht4.
      by rewrite Ht3 Ht4 Htf1 Htf2.
    + destruct jc3 as [[[[??]?]?]?].
      apply write_bridges_agree in H2 as Ht1.
      apply silent_bridge_agree in H3 as (_ & _ & _ & Ht2).
      rewrite - Ht2 - Ht1 Ht in Hlen.
      destruct jc1 as [[[[??]?]?]?].
      apply final_nw_bridges_grow_trace in H.
      destruct jc2 as [[[[??]?]?]?].
      apply write_bridges_agree in H0 as Ht3.
      apply silent_bridge_agree in H1 as (_ & _ & _ & Ht4).
      rewrite Ht3 Ht4 in H. lia.
  - destruct jc1 as [[[[??]?]?]?].
    apply write_bridges_agree in H as Ht1.
    apply silent_bridge_agree in H0 as (_ & _ & _ & Ht2).
    inversion Hred1; subst.
    + rewrite - Ht2 - Ht1 - Ht in Hlen.
      destruct jc1 as [[[[??]?]?]?].
      apply final_nw_bridges_grow_trace in H0.
      destruct jc2 as [[[[??]?]?]?].
      apply write_bridges_agree in H1 as Ht3.
      apply silent_bridge_agree in H2 as (_ & _ & _ & Ht4).
      rewrite Ht3 Ht4 in H0. lia.
    + destruct jc1 as [[[[??]?]?]?].
      apply write_bridges_agree in H0 as Ht3.
      apply silent_bridge_agree in H1 as (_ & _ & _ & Ht4).
      rewrite - Ht2 - Ht1 - Ht4 - Ht3 => //.
Qed.

(** Main theorem -- Soundness of the type system *)
Theorem typecheck_PINI :
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
    erewrite typecheck_is_sound in Ht2; last first.
    2: exact Hred1. 2: exact Hred2. 6: exact Htype.
    rewrite Ht1 Ht2 => //. done. done. done. done.
    rewrite Ht1 in Ht2. by inversion Ht2.
Qed.

