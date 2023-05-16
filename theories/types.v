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

Definition flows l1 l2 :=
  match l1, l2 with
  | LSecret, LPublic => False
  | _, _ => True
  end.

(* Allow to use the notation "l1 '⊑' l2" *)
#[export] Instance sqsubseteq_confidentiality : SqSubsetEq confidentiality.
Proof. exact flows. Defined.


(* typing environment *)
Definition context := gmap var confidentiality.
Definition empty_content : context := gmap_empty.

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
  gmap_merge _ _ _
    (fun opt1 opt2 =>
       match opt1, opt2 with
       | Some l1, Some l2 => Some (l1 ⊔ l2)
       | None, _ => opt2
       | _, None => opt1
       end
    )
    gamma1 gamma2.
Notation "g1 '⊔g' g2" := (join_context g1 g2) (at level 40).

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
| TSkip : forall Γ pc,
  -{ Γ, pc ⊢ CSkip ~> Γ }-

| TAssign : forall le Γ pc x e Γ',
  {{ Γ ⊢ e : le }} ->
  Γ' = <[ x := (le ⊔ pc) ]> Γ ->
  -{ Γ, pc ⊢ (CAssign x e) ~> Γ' }-

| TSeq : forall (Γ1 Γ2 Γ3 : context) pc c1 c2,
  -{ Γ1, pc ⊢ c1 ~> Γ2 }- ->
  -{ Γ2, pc ⊢ c2 ~> Γ3 }- ->
  -{ Γ1, pc ⊢ (CSeq c1 c2) ~> Γ3 }-

| TIf : forall l Γ Γ1 Γ2 pc e c1 c2,
  {{ Γ ⊢ e : l }} ->
  -{ Γ, pc ⊔ l ⊢ c1 ~> Γ1 }- ->
  -{ Γ, pc ⊔ l ⊢ c2 ~> Γ2 }- ->
  -{ Γ, pc ⊢ (CIfThenElse e c1 c2) ~> (Γ1 ⊔g Γ2) }-

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

| TInput : forall Γ pc x ch Γ',
  (pc ⊑ confidentiality_of_channel ch) ->
  Γ' = <[ x := ((confidentiality_of_channel ch) ⊔ pc) ]> Γ ->
  -{ Γ, pc ⊢ (CInput ch x) ~> Γ' }-

| TOutput : forall le Γ pc e ch,
  {{ Γ ⊢ e : le }} ->
  ((pc ⊔ le) ⊑ confidentiality_of_channel ch) ->
  -{ Γ, pc ⊢ (COutput ch e) ~> Γ }-
where "-{ Γ ',' pc '⊢' e '~>' Γ2 }-" := (typecheck Γ pc e Γ2)
.
