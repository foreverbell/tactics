Require Import Bool Arith.

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.

Ltac bsimpl :=
  repeat
    match goal with
    | [ H : (_ ?= _) = Eq |- _] => rewrite Nat.compare_eq_iff in H; subst
    | [ H : (_ ?= _) = Lt |- _] => rewrite Nat.compare_lt_iff in H
    | [ H : (_ ?= _) = Gt |- _] => rewrite Nat.compare_gt_iff in H
    | [ H : (_ =? _) = true |- _] => rewrite beq_nat_true in H; subst
    | [ H : (_ =? _) = false |- _] => rewrite beq_nat_false in H
    | [ H : (_ <? _) = true |- _] => rewrite Nat.ltb_lt in H
    | [ H : (_ <? _) = false |- _] => rewrite Nat.ltb_ge in H
    | [ H : (_ <=? _) = true |- _] => rewrite leb_complete in H
    | [ H : (_ <=? _) = false |- _] => rewrite leb_complete_conv in H
    end.

Ltac bdestruct X :=
  let H := fresh "H" in
    match X with
    | (?x =? ?y) =>
        destruct X eqn:H;
        [ apply beq_nat_true in H; subst |
          apply beq_nat_false in H ]
    | (?x <? ?y) =>
        destruct X eqn:H;
        [ apply Nat.ltb_lt in H; subst |
          apply Nat.ltb_ge in H ]
    | (?x <=? ?y) =>
        destruct X eqn:H;
        [ apply leb_complete in H; subst |
          apply leb_complete_conv in H ]
    | (?x ?= ?y) =>
        destruct X eqn:H;
        [ apply Nat.compare_eq_iff in H; subst |
          apply Nat.compare_lt_iff in H |
          apply Nat.compare_gt_iff in H ]
    end.