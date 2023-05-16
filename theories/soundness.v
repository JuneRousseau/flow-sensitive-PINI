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
