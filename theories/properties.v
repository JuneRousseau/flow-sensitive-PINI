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


(** Usefull definitions *)
(* Two memories have the same values for the public variables *)
Definition agree_on_public (Γ : context) (m1 m2 : memory) : Prop :=
  forall x,
    match Γ !! x with
    | Some LPublic => m1 !! x = m2 !! x
    | _ => True
    end
.

(* 
(* Two memories have the same values for the public variables *)
Definition agree_on_public (Γ : context) (m1 m2 : memory) : Prop :=
  forall x,
    match m1 !! x, m2 !! x, Γ !! x with
    | Some v1, Some v2, Some LPublic => v1 = v2
    (* NOTE Should we capture this ? If we don't, we don't have refl anymore *)
    | None, None, Some LPublic => True
    | _, _, Some LSecret => True
    | None, None, None => True
    | _, _, _ => False
    end
. *)

Lemma agree_refl Γ m : agree_on_public Γ m m.
Proof. intros x. 
       destruct (Γ !! x) eqn:HΓ => //;
       destruct c => //.
Qed.

(* Lemma agree_refl Γ m : wf_memory m Γ -> agree_on_public Γ m m.
Proof. intros H x. specialize (H x).
       destruct (m !! x) eqn:Hm, (Γ !! x) eqn:HΓ => //;
       destruct c => //.
Qed . *)

Lemma agree_on_public_comm Γ m1 m2 :
  agree_on_public Γ m1 m2 ->
  agree_on_public Γ m2 m1.
Proof.
  intros H x. specialize (H x). destruct (Γ !! x) => //.
  destruct c => //.
Qed.

#[export] Instance transitive_agree_pub { Γ : context } : Transitive (agree_on_public Γ).
Proof.
  intros m1 m2 m3 H1 H2 x.
  specialize (H1 x). specialize (H2 x).
  destruct (Γ !! x) => //;
  destruct c => //. by rewrite H1 H2.
Defined.

Lemma agree_update Γ m1 m2 s vg v:
  agree_on_public Γ m1 m2 ->
  agree_on_public (<[ s := vg ]> Γ) (<[ s := v ]> m1) (<[ s := v ]> m2).
Proof.
  intros H x. specialize (H x).
  destruct (x =? s) eqn:Hx.
  - apply String.eqb_eq in Hx as ->.
    repeat rewrite lookup_insert. by destruct vg.
  - apply String.eqb_neq in Hx.
    repeat rewrite lookup_insert_ne => //.
Qed.

Lemma agree_update_secret Γ m s v :
  Γ !! s = Some LSecret ->
(*   wf_memory m Γ -> *) 
  agree_on_public Γ m (<[ s := v ]> m).
Proof.
  intros H (* Hm *) x. (* specialize (Hm x). *)
  destruct (x =? s) eqn:Hx.
  - apply String.eqb_eq in Hx as ->.
    repeat rewrite lookup_insert. rewrite H. done. (* destruct (m !! s) => //. *)
  - apply String.eqb_neq in Hx.
    repeat rewrite lookup_insert_ne => //.
(*     destruct (m !! x) eqn:Hmx; rewrite Hmx; *)
    destruct (Γ !! x) => //; destruct c => //; destruct (Γ !! x) => //.
Qed.

Lemma agree_update_secret2 Γ m1 m2 s v1 v2 :
  agree_on_public Γ m1 m2 ->
  agree_on_public (<[ s := LSecret ]> Γ) (<[ s := v1 ]> m1) (<[ s := v2 ]> m2).
Proof.
  intros Hm x. specialize (Hm x).
  destruct (x =? s) eqn:Hx.
  - apply String.eqb_eq in Hx as ->.
    repeat rewrite lookup_insert. done. 
  - apply String.eqb_neq in Hx.
    repeat rewrite lookup_insert_ne => //.
Qed.

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
    specialize (Hagree s). rewrite H0 H1 H3 in Hagree. by inversion Hagree. 
  - inversion Hv1; subst. inversion Hv2; subst.
    inversion Ht; subst. destruct ℓ1 => //. destruct ℓ2 => //.
    rewrite (IHe1 v1 v0 H2 Hagree H4 H6).
    rewrite (IHe2 _ _ H9 Hagree H5 H7). done.
 Qed.

(* TODO what is context agree *)

Definition context_agree (Γ1 Γ2: context) : Prop :=
  forall x,
    match Γ1 !! x, Γ2 !! x with
    | Some LPublic, y | y, Some LPublic => y = Some LPublic
    | _, _ => True
    end.

#[export] Instance reflexive_context_agree : Reflexive context_agree.
Proof. intro Γ; intro x. destruct (Γ !! x) => //. destruct c => //. Defined.

#[export] Instance transitive_context_agree : Transitive context_agree.
Proof.
  intros Γ1 Γ2 Γ3 H1 H2 x.
  specialize (H1 x). specialize (H2 x).
  destruct (Γ1 !! x), (Γ2 !! x), (Γ3 !! x) => //.
  destruct c, c0, c1 => //. all: destruct c, c0 => //.
Defined.

Lemma context_agree_sym Γ1 Γ2 : context_agree Γ1 Γ2 -> context_agree Γ2 Γ1.
Proof.
  intros H x. specialize (H x). destruct (Γ1 !! x), (Γ2 !! x) => //.
  destruct c0, c => //.
Qed.

Lemma context_agree_update Γ1 Γ2 s v :
  context_agree Γ1 Γ2 ->
  context_agree (<[ s := v ]> Γ1) (<[ s := v ]> Γ2).
Proof.
  intros HΓ x. specialize (HΓ x).
  destruct (x =? s) eqn:Hx.
  - apply String.eqb_eq in Hx as ->.
    repeat rewrite lookup_insert.
    destruct v => //.
  - apply String.eqb_neq in Hx.
    repeat rewrite lookup_insert_ne => //.
Qed. 

Lemma context_agree_add_secret Γ s :
  Γ !! s = None ->
  context_agree Γ (<[ s := LSecret ]> Γ).
Proof.
  intros Hs x. destruct (x =? s) eqn:Hx.
  - apply String.eqb_eq in Hx as ->.
    repeat rewrite lookup_insert.
    by rewrite Hs.
  - apply String.eqb_neq in Hx.
    repeat rewrite lookup_insert_ne => //.
    destruct (Γ !! x) eqn:Hgx => //.
    + destruct c => //. by rewrite Hgx.
    + by rewrite Hgx.
Qed. 


Lemma agree_on_agree Γ Γ' m m' :
  agree_on_public Γ m m' ->
  context_agree Γ Γ' ->
  agree_on_public Γ' m m'.
Proof.
  intros Hm HΓ x.
  specialize (Hm x). specialize (HΓ x).
  destruct (Γ !! x) eqn:Hgx, (Γ' !! x) eqn:Hgx' => //.
  all: try by destruct c, c0.
  all: try by destruct c.
Qed.

(** Properties *)
Lemma expr_type_agree Γ1 Γ2 e l1 l2:
  context_agree Γ1 Γ2 ->
  {{ Γ1 ⊢ e : l1 }} -> {{ Γ2 ⊢ e : l2 }} -> l1 = l2.
Proof.
  intros HΓ He1 He2.
  generalize dependent l1. generalize dependent l2.
  induction e; intros; inversion He1; inversion He2; subst => //.
  - specialize (HΓ s). destruct (Γ1 !! s) => //. destruct c => //.
    + rewrite HΓ in H5. rewrite H1 in H5. by inversion H5.
    + destruct (Γ2 !! s) => //. destruct c => //. rewrite H1 in H5; by inversion H5.
  - rewrite (IHe1 ℓ0 H11 ℓ1 H4).
    rewrite (IHe2 ℓ3 H12 ℓ2 H5). done.
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
  - destruct (x =? y) eqn:Heq.
    + apply String.eqb_eq in Heq ; subst.
      by repeat (rewrite lookup_insert).
    + apply String.eqb_neq in Heq ; subst.
      rewrite lookup_insert_ne => //.
      rewrite lookup_insert_ne => //.
      rewrite lookup_empty.
      by destruct (<[i:=x0]> m !! y).
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
        *** by destruct (<[i0:=x1]> m0 !! y).
        (*     (* rewrite Hy in Hmem. *) *)
        (*     (* rewrite lookup_insert in Hmem => //. *) *)
        (* *** apply String.eqb_neq in Heqi0 ; subst. *)
        (*    rewrite lookup_insert_ne; first done. *)
        (*    destruct (m0 !! y) eqn:Hy0; last done. *)
        (*    (* Contradiction with Hmem *) *)
        (*    specialize (Hmem y). *)
        (*    rewrite lookup_insert_ne in Hmem; try done. *)
        (*    rewrite Hy in Hmem. *)
        (*    rewrite lookup_insert_ne in Hmem; try done. *)
        (*    by rewrite Hy0 in Hmem. *)
Qed.

(* For this lemma to be true, we must update the definition of wf_memory *)
Lemma wf_update_secret Γ m s :
  wf_memory m Γ ->
  wf_memory m (<[ s := LSecret ]> Γ).
Proof.
  intros H x. specialize (H x).
  destruct (x =? s) eqn:Hx.
  - apply String.eqb_eq in Hx as ->.
    repeat rewrite lookup_insert. destruct (m !! s) => //.
  - apply String.eqb_neq in Hx.
    destruct (m !! x) eqn:Hmx ; rewrite lookup_insert_ne => //.
Qed.


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
