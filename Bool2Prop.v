Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

(** We present two ways to deal with boolean expression and proposition. *)

(** The first approach is straight-forward. Just [destruct (_ ? _); b2p]
    whenever you see comparision. *)

Ltac b2p0 :=
  match goal with
  | [ H : (_ ?= _) = Eq |- _] => apply Nat.compare_eq_iff in H; subst
  | [ H : (_ ?= _) = Lt |- _] => apply Nat.compare_lt_iff in H
  | [ H : (_ ?= _) = Gt |- _] => apply Nat.compare_gt_iff in H
  | [ H : (_ =? _) = true |- _] => apply beq_nat_true in H; subst
  | [ H : (_ =? _) = false |- _] => apply beq_nat_false in H
  | [ H : (_ <? _) = true |- _] => apply Nat.ltb_lt in H
  | [ H : (_ <? _) = false |- _] => apply Nat.ltb_ge in H
  | [ H : (_ <=? _) = true |- _] => apply leb_complete in H
  | [ H : (_ <=? _) = false |- _] => apply leb_complete_conv in H
  end.

Ltac b2p := repeat b2p0.

(** The second approach is inspired from "Verified functional algorithms"
    written by Andrew Appel. Here we use the idea of reflection to convert
    boolean expression to proposition. *)

Lemma beq_reflect :
  forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y; apply iff_reflect; symmetry.
  apply beq_nat_true_iff.
Qed.

Lemma blt_reflect :
  forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y; apply iff_reflect; symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma ble_reflect :
  forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y; apply iff_reflect; symmetry.
  apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H] ]
    ].

Ltac cdestruct X :=
  match X with
  | (?x ?= ?y) => let H := fresh "H" in
      destruct X eqn:H;
      [ apply Nat.compare_eq_iff in H; subst | apply Nat.compare_lt_iff in H
        | apply Nat.compare_gt_iff in H ]
  | _ => fail
  end.
