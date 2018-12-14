Require Import Omega.

Module numbers.
Axiom p_or_np: forall P:Prop, P \/ ~P.

Theorem impl_to_or: forall (P Q : Prop),
(~P -> Q) -> P \/ Q.
Proof.
    intros. unfold not in H. destruct (p_or_np P).
    - left. apply H0.
    - apply H in H0. right. apply H0.
Qed. 

Inductive divisor : nat -> nat -> Prop :=
    | div_a_0 : forall a:nat, divisor a 0
    | div_a_b : forall (a b : nat), divisor a b -> divisor a (a + b).

Notation "a | b" := (divisor a b)
(at level 60).

(* Notation "( a | b c )" := (a | b /\ a | c)
(at level 40, right associativity). *)

Theorem divisor_smaller: forall (a b : nat),
    b<>0 -> a | b -> a <= b.
Proof.
    intros. inversion H0.
    - unfold not in H. subst. contradiction.
    - omega.
Qed.

Theorem exists_codivisor: forall (a b : nat),
    a | b <-> (exists d : nat, b = d * a).
Proof.
    split; intros.
    - induction H.
        + exists 0. omega.
        + destruct IHdivisor. exists (1 + x). rewrite H0. simpl. reflexivity.
    - destruct H.
        + generalize dependent a. generalize dependent b. induction x.
            * intros. simpl in H. rewrite H. apply div_a_0.
            * intros. simpl in H. rewrite H. apply div_a_b. apply IHx. reflexivity.
Qed.

Theorem div_ab_c: forall (a b c d : nat),
(a + b = c) -> d | a -> d | b -> d | c.
Proof.
    intros. rewrite exists_codivisor. rewrite exists_codivisor in H0. rewrite exists_codivisor in H1.
    destruct H0. destruct H1. exists (x + x0). rewrite <- H. rewrite H0. rewrite H1. symmetry. apply mult_plus_distr_r.
Qed.

Theorem div_abc: forall (a b c d : nat),
(a = b + c) -> d | a -> d | b -> d | c.
Proof.
    intros. rewrite exists_codivisor. rewrite exists_codivisor in H0. rewrite exists_codivisor in H1.
    destruct H0. destruct H1. exists (x - x0). rewrite mult_minus_distr_r. rewrite <- H0. rewrite <- H1.
    omega.
Qed. 

Inductive prime (p : nat) : Prop :=
    prim : 1 < p -> (forall d : nat, 1 < d -> d < p -> ~ d | p) -> prime p.

Example prime3: prime 3.
Proof.
    apply prim.
    - omega.
    - unfold not. intros. induction d.
        + omega.
        + inversion H.
            * inversion H1. subst. assert (b = 1).
                -- omega.
                -- subst. inversion H5.
            * omega.
Qed. 

End numbers.