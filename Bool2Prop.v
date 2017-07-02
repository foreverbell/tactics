Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

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