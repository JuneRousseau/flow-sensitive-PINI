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


 Lemma trace_grows :
   forall c S P m t c' S' P' m' t',
     (c, S, P, m, t) --->* (c', S', P', m', t') ->
     exists nw, t' = app nw t.
 Proof.
 Admitted.

 Lemma project_app :
   forall t1 t2,
     ⟦ (t1 ++ t2)%list ⟧p = ((⟦ t1 ⟧p) ++ (⟦ t2 ⟧p))%list.
 Proof.
 Admitted.


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
Lemma can_exec_with_gamma Γ0 (* pc0 *) P0 S0 c0 m0 t0 c1 P1 S1 m1 t1 :
  wf_memory m0 Γ0 ->
  ( c0 , P0, S0, m0, t0 ) ---> (c1, P1, S1, m1, t1) ->
  exists j1 Γ1 pc1 ev,
    exec_with_gamma
      ( option_map jcommand_of_command c0 , P0, S0, m0, t0 ) Γ0 []
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
      inversion Ht. done. 
    + apply IHc0_1 in H0 as (j1 & Γ1 & pc1 & ev & Hexec & Ht).
      destruct j1 => //. repeat eexists. eapply GSeq2 => //.
      simpl. rewrite command_id. done. 
  - inversion Hstep; subst.
    destruct (has_security_level _ _ _ _ H0 Hwf) as [l He].
    eexists _,_,_,_. split. econstructor => //. done.
Qed. 

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

 
 Lemma bridge_adequacy :
   forall n c pc Γ Γf m S P t cf Sf Pf mf tf,
     typecheck Γ pc c Γf ->
     wf_memory m Γ ->
     (Some c, S, P, m, t) --->[n] (cf, Sf, Pf, mf, tf) ->
     (exists j S' P' m' t' Γ' ls' ev k n',
       bridge (Some (jcommand_of_command c), S, P, m, t) Γ [] k ev (j, S', P', m', t') Γ' ls' /\
         (option_map command_of_jcommand j, S', P', m', t') --->[n'] (cf, Sf, Pf, mf, tf) /\
         k + n' + 1 = n) \/ t = tf.
 Proof.
   intro n.
   induction n;
   intros * Hc Hm Hred.
   { inversion Hred; subst. by right. }

   inversion Hred; subst.
   destruct y as [[[[c1 S1] P1] m1] t1]. 
   eapply can_exec_with_gamma in H0 as (j1 & Γ1 & pc1 & ev & Hredg & Hj); last done.
   destruct ev.
   - left. repeat eexists. apply BridgePublic. exact Hredg.
     rewrite Hj. exact H1. lia.
   - destruct n.
     + admit.
     + destruct c1; last first.
       { inversion H1. inversion H0. }
       eapply IHn in H1. 
   
 Admitted.

 Lemma bridge_noninterference :
   forall Γ m1 m2 c Γf ev1 ev2 n1 n2 c1 S1 S1' P P1 m1' t1 t1' c2 S2 S2' P2 m2' t2 t2' Γ1' Γ2',
     agree_on_public Γ m1 m2 ->
     (⟦ t1 ⟧p = ⟦ t2 ⟧p) -> 
     typecheck Γ LPublic c Γf ->
     bridge (Some c, S1, P, m1, t1) Γ [] n1 ev1 (c1, S1', P1, m1', t1') Γ1' [] ->
     bridge (Some c, S2, P, m2, t2) Γ [] n2 ev2 (c2, S2', P2, m2', t2') Γ2' [] ->
     c1 = c2 /\
       P1 = P2 /\
       Γ1' = Γ2' /\
       agree_on_public Γ1' m1' m2' /\
       ev1 = ev2 /\
       ⟦ t1' ⟧p = ⟦ t2' ⟧p
 .
 Proof.
 Admitted.

 Lemma bridge_preservation :
   forall Γ c Γf m S P t k ev c' S' P' m' t' Γ',
     typecheck Γ LPublic c Γf ->
     wf_memory m Γ ->
     bridge (Some c, S, P, m, t) Γ [] k ev (c', S', P', m', t') Γ' [] ->
     wf_memory m' Γ' /\ match c' with None => True | Some c' => typecheck Γ' LPublic c' Γf end.
 Proof.
 Admitted.




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
    generalize dependent c. generalize dependent S1. generalize dependent S2.
    generalize dependent P. generalize dependent m1. generalize dependent m2.
    generalize dependent t1. generalize dependent t2. generalize dependent Γ.
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
