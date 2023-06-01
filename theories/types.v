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

(* We say that a memory is well-formed w.r.t a context if all they define the
   same variables *)
(* TODO actually, we can just require dom(m) ⊆ dom(m) *)
Definition wf_memory (m : memory) (Γ : context) : Prop :=
  forall x, match m !! x, Γ !! x with
       | Some _, Some _
       | None, None => True
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

Lemma flows_context_join Γ Γ' : Γ ⊑g (Γ ⊔g Γ').
Proof.
  intros x.
  destruct (Γ !! x) eqn:Hx => //;
  destruct ((Γ ⊔g Γ') !! x) eqn:Hx' => //.
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
