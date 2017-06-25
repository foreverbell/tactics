Require Import Arith Omega.
Import PeanoNat.Nat.

(** Modulo induction principle. *)
(** Taken from https://github.com/tchajed/100game/blob/master/coq/solution.v. *)
Theorem mod_principle k (Hneq0: k <> 0) :
  forall (P: nat -> Prop)
    (Hsmall: forall n, n < k -> P n)
    (Hind: forall p, (forall n, n < k -> P (k * p + n)) ->
                (forall n, n < k -> P (k * S p + n))),
    (forall n, P n).
Proof.
  intros.
  pose proof (div_mod n k ltac:(auto)).
  remember (n / k) as p. remember (n mod k) as r.
  rewrite H.
  pose proof (mod_upper_bound n k ltac:(assumption)).
  rewrite <- Heqr in H0.
  clear n H Heqp Heqr.
  generalize dependent r.
  induction p.
  - rewrite mul_0_r. auto.
  - apply Hind. apply IHp.
Qed.

(** Second induction principle. *)
Lemma snd_principle' :
  forall (P: nat -> Prop),
    (forall n, (forall k, k < n -> P k) -> P n) ->
    (forall n, P n /\ (forall k, k < n -> P k)).
Proof.
  intros.
  induction n.
  - split.
    + pose proof (H 0) as H0.
      apply H0. intros. omega.
    + intros. omega.
  - destruct IHn as [IHn1 IHn2].
    split;
      try apply H; intros;
      apply lt_n_Sm_le in H0;
      apply le_lt_or_eq in H0;
      destruct H0; subst; auto.
Qed.

Theorem snd_principle :
  forall (P: nat -> Prop),
    (forall n, (forall k, k < n -> P k) -> P n) ->
    (forall n, P n).
Proof.
  intros.
  pose proof (snd_principle' P H).
  specialize (H0 n).
  tauto.
Qed.

(** Example usage:
  * induction n using (mod_principle 11 ltac:(omega)).
  * induction n using snd_principle. *)
