Require Import a10.
Require Import List Arith Bool.
Require String.
Import ListNotations.

Module CheckAuthor.
Import String.
Import Author.
Definition check_author : string := author.
Definition check_netid : string := netid.
Definition check_hours_worked : nat := hours_worked.
Definition check_collaborators : string := collaborators.
End CheckAuthor.

Module CheckSimpleQueue.
Import SimpleQueue.
Definition check_queue : Type -> Type := queue.
Definition check_empty : forall A : Type, queue A := @empty.
Definition check_is_empty : forall A : Type, queue A -> bool := @is_empty.
Definition check_front : forall A : Type, queue A -> option A := @front.
Definition check_enq : forall A : Type, A -> queue A -> queue A := @enq.
Definition check_deq : forall A : Type, queue A -> queue A := @deq.
Definition check_eqn1 : forall (A : Type), is_empty (@empty A) = true := eqn1.
Definition check_eqn2 : forall (A : Type) (x : A) (q : queue A), is_empty (enq x q) = false := eqn2.
Definition check_eqn3 : forall (A : Type), front (@empty A) = None := eqn3.
Definition check_eqn4 : forall (A : Type) (x : A) (q : queue A), is_empty q = true -> front (enq x q) = Some x := eqn4.
Definition check_eqn5 : forall (A : Type) (x : A) (q : queue A), is_empty q = false -> front (enq x q) = front q := eqn5.
Definition check_eqn6 : forall (A : Type), deq (@empty A) = @empty A := eqn6.
Definition check_eqn7 : forall (A : Type) (x : A) (q : queue A), is_empty q = true -> deq (enq x q) = empty := eqn7.
Definition check_eqn8 : forall (A : Type) (x : A) (q : queue A), is_empty q = false -> deq (enq x q) = enq x (deq q) := eqn8.
End CheckSimpleQueue.

Module CheckTwoListQueue.
Import TwoListQueue.
Definition check_queue : Type -> Type := queue.
Definition check_rep_ok : forall A : Type, queue A -> Prop := @rep_ok.
Definition check_empty : forall A : Type, queue A := @empty.
Definition check_is_empty : forall A : Type, queue A -> bool := @is_empty.
Definition check_front : forall A : Type, queue A -> option A := @front.
Definition check_enq : forall A : Type, A -> queue A -> queue A := @enq.
Definition check_deq : forall A : Type, queue A -> queue A := @deq.
Definition check_test_two_lists : enq 1 (enq 0 empty) = ([0], [1]) := test_two_lists.
Definition check_eqn1 : forall (A : Type), is_empty (@empty A) = true := eqn1.
Definition check_eqn2 : forall (A : Type) (x : A) (q : queue A), rep_ok q -> is_empty (enq x q) = false := eqn2.
Definition check_eqn3 : forall (A : Type), front (@empty A) = None := eqn3.
Definition check_eqn4 : forall (A : Type) (x : A) (q : queue A), rep_ok q -> is_empty q = true -> front (enq x q) = Some x := eqn4.
Definition check_eqn5 : forall (A : Type) (x : A) (q : queue A), rep_ok q -> is_empty q = false -> front (enq x q) = front q := eqn5.
Definition check_eqn6 : forall (A : Type), deq (@empty A) = @empty A := eqn6.
Definition check_eqn7 : forall (A : Type) (x : A) (q : queue A), rep_ok q -> is_empty q = true -> deq (enq x q) = empty := eqn7.
Module CheckCounterEx.
Import CounterEx.
Definition check_x : nat := x.
Definition check_q : list nat * list nat := q.
Definition check_counter1 : rep_ok q := counter1.
Definition check_counter2 : is_empty q = false := counter2.
Definition check_counter3 : deq (enq x q) <> enq x (deq q) := counter3.
End CheckCounterEx.
Definition check_equiv : forall (A:Type), queue A -> queue A -> Prop := @equiv.
Definition check_eqn8_equiv : forall (A : Type) (x : A) (q : queue A), rep_ok q -> is_empty q = false -> equiv (deq (enq x q)) (enq x (deq q)) := eqn8_equiv.
Definition check_rep_ok_empty : forall (A : Type), rep_ok (@empty A) := rep_ok_empty.
Definition check_rep_ok_enq : forall (A : Type) (q : queue A), rep_ok q -> forall (x : A), rep_ok (enq x q) := rep_ok_enq.
Definition check_rep_ok_deq: forall (A : Type) (q : queue A), rep_ok q -> rep_ok (deq q) := rep_ok_deq.
End CheckTwoListQueue.

Module CheckLogic.
Import Logic.
Definition check_logic1 : forall P Q R S T: Prop, ((P /\ Q) /\ R) -> (S /\ T) -> (Q /\ S) := logic1.
Definition check_logic2 : forall P Q R S : Prop, (P -> Q) -> (R -> S) -> (P \/ R) -> (Q \/ S) := logic2.
Definition check_logic3 : forall P Q : Prop, (P -> Q) -> (((P /\ Q) -> P) /\ (P -> (P /\ Q))) := logic3.
Definition check_logic4 : forall P Q : Prop, (P -> Q) -> (~~P -> ~~Q) := logic4.
End CheckLogic.

Module CheckInduction.
Import Induction.
Definition check_sumsq_to : nat -> nat := sumsq_to.
Definition check_sumsq : forall n, 6 * sumsq_to n = n * (n+1) * (2*n+1) := sumsq.
Definition check_app_assoc : forall (A : Type) (lst1 lst2 lst3 : tsil A), app lst1 (app lst2 lst3) = app (app lst1 lst2) lst3 := app_assoc.
Definition check_app_length : forall (A : Type) (lst1 lst2 : tsil A), length (app lst1 lst2) = length lst1 + length lst2 := app_length.
End CheckInduction.
