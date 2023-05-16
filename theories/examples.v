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

(** Examples *)
Definition example_typecheck example := exists gamma, -{ ∅ , LPublic ⊢ example ~> gamma}-.
(* /* Program 1 -- should be well-typed as it satisfies PINI (and PSNI) */ *)
Definition example1 :=
 (INPUT "x" @Secret) ;;;
   ("x" ::= 0) ;;;
   (OUTPUT "x" @Public).

Lemma example1_typecheck : example_typecheck example1.
Proof.
  eexists.
  repeat econstructor.
Qed.

(* /* Program 2 -- must be ill-typed as it violates PINI */ *)
Definition example2 :=
  (INPUT "x" @Secret) ;;; (OUTPUT "x" @Public).
Lemma example2_not_typecheck : not (example_typecheck example2).
Proof.
  intro.
  inversion H.
  inversion H0; subst; simpl in *.
  inversion H5; subst; simpl in *.
  inversion H7; subst; simpl in *.
  inversion H8; subst; simpl in *.
  inversion H3; subst; simpl in *.
  assumption.
Qed.

(* /* Program 3 -- must be ill-typed because of the implicit flow */ *)
Definition example3 :=
  INPUT "x" @Secret ;;;
  "y" ::= 0 ;;;
  IFB "x" THEN "y" ::= 1 ELSE SKIP FI ;;;
  OUTPUT "y" @Public.

Lemma example3_not_typecheck : not (example_typecheck example3).
Proof.
  intro.
  inversion H;subst; simpl in *.
  inversion H0;subst; simpl in *.
  inversion H5;subst; simpl in *. clear H5 H6.
  inversion H7;subst; simpl in *. clear H7.
  inversion H5;subst; clear H5; simpl in *.
  inversion H6;subst; clear H6; simpl in *.
  inversion H8;subst; clear H8; simpl in *.
  inversion H5;subst; clear H5; simpl in *.
  inversion H8;subst; simpl in *.
  cbn in H3; inversion H3.
  rewrite ( _ : ( <["y":=LPublic]> (<["x":=LSecret]> ∅) !! "x" = Some LSecret ))
  in H2; [(by clear H3; simpl_map)| subst ; clear H3].
  cbn in *.
  (* inversion H4;subst; clear H4. *)
  (* cbn in H3; inversion H3 ; subst ; clear H3. *)
  inversion H11;subst; clear H11.
  inversion H10;subst; clear H10.
  inversion H7;subst; clear H7.
  cbn in *.
  inversion H6;subst.
  cbn in H3; inversion H3 ; subst ; clear H3.
  inversion H5;subst; cbn in *.
  assumption.
Qed.

(* /* Program 4 -- should be well-typed as it satisfies PINI (and PSNI) */ *)
Definition example4 :=
  INPUT "x" @Secret ;;;
  IFB "x" THEN "y" ::= 1 ELSE SKIP FI ;;;
  OUTPUT "y" @Secret ;;;
  "y" ::= 0 ;;;
  OUTPUT "y" @Public.
Lemma example4_typecheck : example_typecheck example4.
Proof.
  repeat econstructor.
Qed.

(* /* Program 5 -- should be well-typed as it satisfies PINI */ *)
Definition example5 :=
  INPUT "x" @Secret ;;;
  ( WHILE "x"
      DO
      "x" ::= (EOp "x" Sub 1);;;
      INPUT "y" @Secret
      END
  ) ;;;
  OUTPUT 0 @Public.

Lemma example5_typecheck : example_typecheck example5.
Proof.
  econstructor.
  econstructor.
  econstructor;eauto.
  econstructor; eauto.
  eapply TWhile2.
  all : (repeat econstructor).
  cbn.
  by repeat (symmetry; map_simpl).
Qed.

(* /* Program 6 -- must be ill-typed as it violates PINI */ *)
(* input(secret, x) *)
(* while x do *)
(* x = x - 1 *)
(* input(secret, y) *)
(* output(public, x) *)
Definition example6 :=
    INPUT "x" @Secret ;;;
    ( WHILE "x"
        DO
        "x" ::= (EOp "x" Sub 1);;;
        INPUT "y" @Secret
        END
    ) ;;;
    OUTPUT "x" @Public.
Lemma example6_typecheck : not (example_typecheck example6).
Proof.
  intro.
  inversion H;subst.
  inversion H0;subst; clear H0.
  inversion H5;subst; cbn in H4; clear H5 H4; cbn in *.
  inversion H7;subst; clear H7.
  inversion H6;subst; clear H6.

  inversion H4;subst; clear H4.
  - inversion H9;subst; clear H9.
    inversion H4;subst; clear H4.
    inversion H7;subst; clear H7.
    inversion H10;subst; clear H10.
    inversion H5;subst; clear H5.
    inversion H6;subst; clear H6 ; cbn in H4.
    cbn in H2; inversion H2; subst.
    cbn in H3; inversion H3; subst.
    inversion H11;subst; clear H11.
    cbn in *.
    by cbn in H8.
  - admit.
Admitted.

(* /* Program 7 -- must be well-typed  */ *)
Definition example7 :=
  INPUT "x" @Secret ;;;
  INPUT "x" @Public ;;;
  OUTPUT "x" @Public
  .
Lemma example7_typecheck : example_typecheck example7.
Proof.
  repeat econstructor.
Qed.


(* /* Program 8 -- must be ill-typed  */ *)
Definition example8 :=
  INPUT "x" @Public ;;;
  ( WHILE "x"
      DO
      OUTPUT "x" @Public;;;
      INPUT "x" @Secret
      END
  ).
Lemma example8_typecheck : not (example_typecheck example8).
Proof.
Admitted.
