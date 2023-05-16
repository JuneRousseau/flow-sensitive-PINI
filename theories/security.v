Require Import String.
Require Import ssreflect.
From Coq Require Import
  Lists.List
  Streams.
From stdpp Require Import gmap.
From fspini Require Import lang.

Fixpoint public_projection (t: trace) : trace :=
  match t with
  | [] => []
  | (EvInput Public v) :: q => (EvInput Public v :: public_projection q)
  | (EvOutput Public v) :: q => (EvOutput Public v :: public_projection q)
  | _ :: q => (public_projection q)
  end.

Notation "'⟦' t '⟧p'" := (public_projection t) (at level 90).

(* knowledge P c d S means that S is in the Set K(P,c,d) *)
Inductive knowledge: (Stream value) -> command -> trace -> (Stream value) -> Prop :=
| Know : forall P c d S,
    (exists S' P' c' m' t',
        ( Some c, S, P, minit, nil) --->* (c' , S', P', m', t')
        /\ ⟦ t' ⟧p  = d)
    -> knowledge P c d S
.

Definition PSNI c :=
  forall P a d t,
    (exists S S' P' c' m',
        ( Some c, S, P, minit, []) --->* ( c', S', P', m', t )
        /\ ⟦ t ⟧p = a :: d) ->
    (* Set equality is described with an iff *)
    (forall S, knowledge P c (a :: d) S <-> knowledge P c d S).

(* progress_knowledge P c d S means that S is in the Set K->(P,c,d) *)
Inductive progress_knowledge: (Stream value) -> command -> trace -> (Stream value) -> Prop :=
| PKnow : forall P c d S,
    (exists S' P' c' m' t' a,
        ( Some c, S, P, minit, [] ) --->* ( c', S', P', m', t')
        /\ ⟦ t' ⟧p = a :: d) ->
    progress_knowledge P c d S
.

Definition PINI c :=
  forall P a d t,
    (exists S S' P' c' m',
        ( Some c, S, P, minit, []) --->* (c', S', P', m', t)
        /\ ⟦ t ⟧p = (a :: d) ) ->
    (* Set equality is described with an iff *)
    (forall S, knowledge P c (a :: d) S <-> progress_knowledge P c d S).
