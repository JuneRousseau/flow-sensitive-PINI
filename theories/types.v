Require Import String.
Require Import ssreflect.
From Coq Require Import
  Lists.List
  Streams.
From stdpp Require Import gmap.
From fspini Require Import lang.
Open Scope string_scope.


Inductive confidentiality :=
| LPublic
| LSecret.

Definition join l1 l2 :=
  match l1, l2 with
  | LPublic, LPublic => LPublic
  | _, _ => LSecret
  end.

(* Allow to use the notation "l1 '⊔' l2" *)
#[export] Instance join_confidentiality : Join confidentiality.
Proof. exact join. Defined.

Lemma join_public l : join l LPublic = l.
Proof. destruct l => //=. Qed.

Lemma join_secret l : join l LSecret = LSecret.
Proof. destruct l => //. Qed.

Lemma fold_secret l : fold_left join l LSecret = LSecret.
Proof. induction l => //. Qed.

Lemma fold_start pc l : (fold_left join pc LPublic) ⊔ l = fold_left join pc l.
Proof.
  induction pc => //=. by destruct l. destruct a => //.
  rewrite IHpc join_public => //. destruct l => //=.
  destruct (fold_left join pc LSecret) => //. rewrite fold_secret => //.
Qed.

Lemma join_comm (l1 l2: confidentiality) : l1 ⊔ l2 = l2 ⊔ l1.
Proof. destruct l1, l2 => //. Qed.

Lemma fold_join pc l : fold_left join (l :: pc) LPublic = fold_left join pc LPublic ⊔ l.
Proof. rewrite fold_start. simpl. by destruct l. Qed.

Definition flows l1 l2 :=
  match l1, l2 with
  | LSecret, LPublic => False
  | _, _ => True
  end.

(* Allow to use the notation "l1 '⊑' l2" *)
#[export] Instance sqsubseteq_confidentiality : SqSubsetEq confidentiality.
Proof. exact flows. Defined.

#[export] Instance reflexive_flows : Reflexive flows.
Proof. intro. destruct x => //. Defined.

#[export] Instance transitive_flows : Transitive flows.
Proof. intros x y z. destruct x, y,z => //. Defined.

(* typing environment *)
Definition context := gmap var confidentiality.
Definition empty_context : context := gmap_empty.

(* We say that a memory m is well-formed w.r.t a context Γ
   if all the variables defined in m are also defined in Γ *)
Definition wf_memory (m : memory) (Γ : context) : Prop :=
  forall x, match m !! x, Γ !! x with
       | Some _, Some _
       | None, None
       | None, Some _ => True
       | _, _ => False
       end.

(* Joining two contexts, to be used after an If-statement *)
Definition join_context (gamma1 gamma2 : context) : context :=
  merge
    (fun opt1 opt2 =>
       match opt1, opt2 with
       | Some l1, Some l2 => Some (l1 ⊔ l2)
       | None, _ => opt2
       | _, None => opt1
       end
    )
    gamma1 gamma2.
Notation "g1 '⊔g' g2" := (join_context g1 g2) (at level 40).

Definition flows_context (gamma1 gamma2 : context) : Prop :=
  forall x, match gamma1 !! x, gamma2 !! x with
       | Some l1, Some l2 => flows l1 l2
       | None, None => True
       | _,_ => False end.
Notation "g1 '⊑g' g2" := (flows_context g1 g2) (at level 40).

#[export] Instance reflexive_flows_context : Reflexive flows_context.
Proof. intros Γ x. destruct (Γ !! x) => //. Defined.

#[export] Instance transitive_flows_context : Transitive flows_context.
Proof. intros Γ1 Γ2 Γ3 H12 H23 x.
       specialize (H12 x); specialize (H23 x).
       destruct (Γ1 !! x), (Γ2 !! x), (Γ3 !! x) => //.
       by transitivity c0.
Defined.

Lemma join_context_self (Γ : context) : Γ = Γ ⊔g Γ.
Proof.
  unfold join_context.
  rewrite merge_idemp ; [| done].
  intros i.
  destruct (Γ !! i) eqn:Heq.
  rewrite Heq. destruct c => //.
  by rewrite Heq.
Qed.

Lemma join_context_some_flows:
  ∀ (Γ Γ' : context) (x : var) l,
  Γ !! x = Some l →
  exists l', l ⊑ l' /\ (Γ ⊔g Γ') !! x = Some l'.
Proof.
  intros  Γ Γ' x ℓ HΓ.
  destruct (Γ' !! x) eqn:HΓ'.
  destruct ℓ,c.
  all:
    try (exists LSecret; split => //; by rewrite lookup_merge; rewrite HΓ HΓ'; cbn).
  + exists LPublic; split => //.
    by rewrite lookup_merge; rewrite HΓ HΓ'; cbn.
  + exists ℓ; split => //.
    by rewrite lookup_merge; rewrite HΓ HΓ'; cbn.
Qed.

Lemma join_empty_r Γ : (Γ ⊔g ∅) = Γ.
Proof.
  induction Γ using map_ind.
  - by apply merge_empty.
  - unfold join_context.
    erewrite <- insert_merge_l; cbn.
    + rewrite (_: (merge
       (λ opt1 opt2 : option confidentiality,
          match opt1 with
          | Some l1 => match opt2 with
                       | Some l2 => Some (l1 ⊔ l2)
                       | None => opt1
                       end
          | None => opt2
          end) m ∅) =  m ⊔g ∅) ; first by (unfold join_context).
    by rewrite IHΓ.
    + by rewrite lookup_empty.
Qed.

Lemma flows_context_join Γ Γ' : Γ ⊑g (Γ ⊔g Γ').
Proof.
  intros x.
  destruct (Γ !! x) eqn:Hx => //;
  destruct ((Γ ⊔g Γ') !! x) eqn:Hx' => //.
  destruct c, c0 => //.
  - eapply join_context_some_flows in Hx.
    destruct Hx as [l' [Hl' HΓ]].
    erewrite Hx' in HΓ. injection HΓ ; intros ; subst ; auto.

  - eapply join_context_some_flows in Hx.
    destruct Hx as [l' [Hl' HΓ]].
    erewrite Hx' in HΓ. discriminate.

  - induction Γ' using map_ind.
    + by rewrite join_empty_r Hx in Hx'.
    + apply IHΓ'.
      unfold join_context in Hx'.
Admitted.

(* Lemma flows_context_refl Γ : Γ ⊑g Γ. *)
(* Proof. intros x. destruct (Γ !! x) => //. destruct c => //. Qed. *)

Lemma join_context_comm Γ1 Γ2 : Γ1 ⊔g Γ2 = Γ2 ⊔g Γ1.
Proof.
  unfold join_context.
  rewrite merge_comm; try done.
  intros.
  destruct (Γ1 !! i) eqn:H1 => // ; rewrite H1;
  destruct (Γ2 !! i) eqn:H2 => // ; rewrite H2; try done.
  f_equal.
  apply join_comm.
Qed.

Reserved Notation "'{{' Γ '⊢' e ':' ℓ '}}'" (at level 10, Γ at level 50, e at level 99).
Inductive typecheck_expr : context -> expr -> confidentiality -> Prop :=
| TLit : forall Γ n, {{ Γ ⊢ (ELit n) : LPublic }}
| TVar : forall ℓ Γ x,
     Γ !! x = Some ℓ -> {{ Γ ⊢ (EVar x) : ℓ }}
| TOp : forall ℓ1 ℓ2 Γ e1 op e2,
    {{ Γ ⊢ e1 : ℓ1 }} ->
    {{ Γ ⊢ e2 : ℓ2 }} ->
    {{ Γ ⊢ (EOp e1 op e2) : (ℓ1 ⊔ ℓ2) }}
where "{{ Γ '⊢' e ':' ℓ }}" := (typecheck_expr Γ e ℓ)
.

Definition confidentiality_of_channel (ch : channel) : confidentiality :=
  match ch with
  | Secret => LSecret
  | Public => LPublic
  end.

Reserved Notation "-{ Γ ',' pc '⊢' e '~>' Γ2 }-"
  (at level 10, Γ at level 55, Γ2 at level 50, pc at level 35, e at level 99).
Inductive typecheck : context -> confidentiality -> command -> context -> Prop :=
| TSkip : forall Γ pc Γf,
    flows_context Γ Γf ->
  -{ Γ, pc ⊢ CSkip ~> Γf }-

| TAssign : forall le Γ pc x e Γ',
  {{ Γ ⊢ e : le }} ->
  flows_context (<[ x := (le ⊔ pc) ]> Γ) Γ' ->
  -{ Γ, pc ⊢ (CAssign x e) ~> Γ' }-

| TSeq : forall (Γ1 Γ2 Γ3 : context) pc c1 c2,
    -{ Γ1, pc ⊢ c1 ~> Γ2 }- ->
(*    flows_context Γ2 Γ2' -> *)
  -{ Γ2, pc ⊢ c2 ~> Γ3 }- ->
  -{ Γ1, pc ⊢ (CSeq c1 c2) ~> Γ3 }-

| TIf : forall l Γ Γ1 Γ2 pc e c1 c2,
  {{ Γ ⊢ e : l }} ->
  -{ Γ, pc ⊔ l ⊢ c1 ~> Γ1 }- ->
  -{ Γ, pc ⊔ l ⊢ c2 ~> Γ2 }- ->
  -{ Γ, pc ⊢ (CIfThenElse e c1 c2) ~> (Γ1 ⊔g Γ2) }-

(* | TWhile : forall l Γ pc e c Γ', *)
(*     flows_context Γ Γ' -> *)
(*     {{ Γ' ⊢ e : l }} -> *)
(*     -{ Γ', pc ⊔ l ⊢ c ~> Γ' }- -> *)
(*     -{ Γ, pc ⊢ (CWhile e c) ~> Γ' }- *)

    (*
(* Does not change the environment *)
| TWhile1 : forall l Γ pc e c,
  {{ Γ ⊢ e : l }} ->
  -{ Γ, pc ⊔ l ⊢ c ~> Γ }- ->
  -{ Γ, pc ⊢ (CWhile e c) ~> Γ }-

(* Does change the environment *)
| TWhile2 : forall l Γ pc e c Γ' Γ'',
  {{ Γ ⊢ e : l }} ->
  -{ Γ, pc ⊔ l ⊢ c ~> Γ'' }- ->
  -{ Γ'', pc ⊢ (CWhile e c) ~> Γ' }- ->
  -{ Γ, pc ⊢ (CWhile e c) ~> Γ' }-
*)


| TInput : forall Γ pc x ch Γ',
  (pc ⊑ confidentiality_of_channel ch) ->
  flows_context ( <[ x := ((confidentiality_of_channel ch) ⊔ pc) ]> Γ) Γ' ->
  -{ Γ, pc ⊢ (CInput ch x) ~> Γ' }-

| TOutput : forall le Γ pc e ch Γ',
  {{ Γ ⊢ e : le }} ->
  ((pc ⊔ le) ⊑ confidentiality_of_channel ch) ->
  flows_context Γ Γ' ->
  -{ Γ, pc ⊢ (COutput ch e) ~> Γ' }-
where "-{ Γ ',' pc '⊢' e '~>' Γ2 }-" := (typecheck Γ pc e Γ2)
.


(** Properties *)
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

