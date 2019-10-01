(** * A10 *)

(* Do not modify these imports. *)
Require Import List Arith Bool.
Require String.
Import ListNotations.

Module Author.
Open Scope string_scope.
Definition author := "Andrew Wang".
Definition netid := "ayw24".
Definition hours_worked := 0.
Definition collaborators := "Jack Ding". 
(* The latter should be the names of other students with whom
     you discussed ideas on this assignment, following the collaboration
     policy stated in the handout. *)
End Author.

(********************************************************************

               AAA                 1111111        000000000     
              A:::A               1::::::1      00:::::::::00   
             A:::::A             1:::::::1    00:::::::::::::00 
            A:::::::A            111:::::1   0:::::::000:::::::0
           A:::::::::A              1::::1   0::::::0   0::::::0
          A:::::A:::::A             1::::1   0:::::0     0:::::0
         A:::::A A:::::A            1::::1   0:::::0     0:::::0
        A:::::A   A:::::A           1::::l   0:::::0 000 0:::::0
       A:::::A     A:::::A          1::::l   0:::::0 000 0:::::0
      A:::::AAAAAAAAA:::::A         1::::l   0:::::0     0:::::0
     A:::::::::::::::::::::A        1::::l   0:::::0     0:::::0
    A:::::AAAAAAAAAAAAA:::::A       1::::l   0::::::0   0::::::0
   A:::::A             A:::::A   111::::::1110:::::::000:::::::0
  A:::::A               A:::::A  1::::::::::1 00:::::::::::::00 
 A:::::A                 A:::::A 1::::::::::1   00:::::::::00   
AAAAAAA                   AAAAAAA111111111111     000000000       

*********************************************************************)

(**

Here is an OCaml interface for queues:
<<
(* ['a t] is a queue containing values of type ['a]. *)
type 'a t

(* [empty] is the empty queue *)
val empty : 'a t

(* [is_empty q] is whether [q] is empty *)
val is_empty : 'a t -> bool

(* [front q] is [Some x], where [x] the front element of [q],
 * or [None] if [q] is empty. *)
val front : 'a t -> 'a option

(* [enq x q] is the queue that is the same as [q], but with [x] 
 * enqueued (i.e., inserted) at the end. *)
val enq : 'a -> 'a t -> 'a t

(* [deq x q] is the queue that is the same as [q], but with its
 * front element dequeued (i.e., removed).  If [q] is empty, 
 * [deq q] is also empty. *)  
val deq : 'a t -> 'a t
>>

Note that the specification for [deq] differs from what we have given
before:  the [deq] of an empty list is the empty list; there are no
options or exceptions involved.

Here is an equational specification for that interface:
<<
(1) is_empty empty      = true
(2) is_empty (enq _ _ ) = false
(3) front empty         = None
(4) front (enq x q)     = Some x         if is_empty q = true
(5) front (enq _ q)     = front q        if is_empty q = false
(6) deq empty           = empty
(7) deq (enq _ q)       = empty          if is_empty q = true
(8) deq (enq x q)       = enq x (deq q)  if is_empty q = false
>>

Your task in the next two parts of this file is to implement the Coq equivalent
of that interface and prove that your implementation satisfies the equational
specification.  Actually, you will do this twice, with two different
representation types:

- _simple queues_, which represent a queue as a singly-linked list
  and have worst-case linear time performance.

- _two-list queues_, which represent a queue with two singly-linked
  lists, and have amortized constant time performance.

You will find both of those implementations in section 5.9 of the textbook.

*)

(********************************************************************)
(** ** Part 1: Simple Queues *)
(********************************************************************)

Module SimpleQueue.

(** Your first task is to implement and verify simple queues.
    To get you started, we provide the following definitions for
    the representation type of a simple queue, and for the empty 
    simple queue. *)

(** [queue A] is the type that represents a queue as a 
    singly-linked list.  The list [[x1; x2; ...; xn]] represents
    the queue with [x1] at its front, then [x2], ..., and finally
    [xn] at its end.  The list [[]] represents the empty queue. *)
Definition queue (A : Type) := list A.

Definition empty {A : Type} : queue A := [].

(** 
*** Implementation of simple queues.
Define [is_empty], [front], [enq], and [deq]. We have provided some starter code
below that type checks, but it defines those operations in trivial and incorrect
ways. _Hint:_ this isn't meant to be tricky; you just need to translate the code
you would naturally write in OCaml into Coq syntax. 
*)

Definition is_empty {A : Type} (q : queue A) : bool :=
  match q with
  | nil => true
  | cons _ _ => false
  end.

Definition front {A : Type} (q : queue A) : option A :=
  match q with
  | nil => None 
  | x :: _ => Some x
  end.  

Fixpoint enq {A : Type} (x : A) (q : queue A) : queue A := 
  match q with
  | nil => x::q
  | cons h t => h::enq x t
  end.

Definition deq {A : Type} (q : queue A) : queue A :=
  match q with 
  | nil => nil
  | cons h t => t
  end.

(** 
*** Verification of simple queues.
Prove that the equations in the queue specification hold. We have written
them for you, below, but instead of a proof we have written [Admitted].  That
tells Coq to accept the theorem as true (hence it will compile) even though
there is no proof.  You need to replace [Admitted] with [Proof. ...  Qed.]
_Hint:_ the only tactics you need are [intros], [trivial], [discriminate],
and [destruct].  You might also find [simpl] to be useful in making a goal
easier to read.  If [simpl] won't simplify a computation involving a queue, 
instead try [destruct] on that queue.  Always pay attention to the hypotheses 
to see whether one might be false, in which case you should concentrate on it 
rather than the goal.
*)

Theorem eqn1 : forall (A : Type), 
  is_empty (@empty A) = true.
Proof.
  trivial.
Qed.

Theorem eqn2 : forall (A : Type) (x : A) (q : queue A),
  is_empty (enq x q) = false.
Proof.
  intros A x q.
  destruct q.
    all: trivial.
Qed.

Theorem eqn3 : forall (A : Type),
  front (@empty A) = None.
Proof.
  trivial. 
Qed.

Theorem eqn4 : forall (A : Type) (x : A) (q : queue A),
  is_empty q = true -> front (enq x q) = Some x.
Proof.
  intros A x q empty_is_true.
  destruct q.
    trivial. 
    discriminate.
Qed. 
  
Theorem eqn5 : forall (A : Type) (x : A) (q : queue A),
  is_empty q = false -> front (enq x q) = front q.
Proof.
  intros A x q empty_is_false.
  destruct q.
    discriminate.
    trivial.
Qed. 

Theorem eqn6 : forall (A : Type),
  deq (@empty A) = (@empty A).
Proof.
  trivial.
Qed.

Theorem eqn7 : forall (A : Type) (x : A) (q : queue A),
  is_empty q = true -> deq (enq x q) = empty.
Proof.
  intros A x q empty_is_true.
  destruct q.
    simpl. trivial. 
    simpl. discriminate.
Qed.

Theorem eqn8 : forall (A : Type) (x : A) (q : queue A),
  is_empty q = false -> deq (enq x q) = enq x (deq q).
Proof.
  intros A x q empty_is_false.
  destruct q.
    simpl. discriminate.
    simpl. trivial.
Qed.

End SimpleQueue.





(********************************************************************)
(** ** Part 2: Two-list Queues *)
(********************************************************************)

Module TwoListQueue.

(** Your second task is to implement and verify two-list queues.
    To get you started, we provide the following definitions for
    the representation type of a two-list queue, and for the empty 
    two-list queue. *)

(** [queue A] is the type that represents a queue as a pair of two
    singly-linked lists.  The pair [(f,b)] represents the same
    queue as does the simple queue [f ++ rev b].  The list [f] is
    the front of the queue, and the list [b] is the back of the
    queue stored in reversed order.

    _Representation invariant:_  if [f] is [nil] then [b] is [nil].

    The syntax [% type] in this definition tells Coq to treat the
    [*] symbol as the pair constructor rather than multiplication. 
    You shouldn't need to use that syntax anywhere in your solution. *)
Definition queue (A : Type) := (list A * list A) % type.

(** [rep_ok q] holds iff [q] satisfies its RI as stated above *)
Definition rep_ok {A : Type} (q : queue A) : Prop :=
  match q with
  | (f,b) => f = [] -> b = []
  end.

Definition empty {A : Type} : queue A := ([],[]).

(** 
*** Implementation of two-list queues.
Define [is_empty], [front], [enq], and [deq]. We have provided some starter code
below that type checks, but it defines those operations in trivial and incorrect
ways. You must use the efficient implementation described in the textbook.
You may not store the entire queue in the first component of the
pair and use the inefficient implementation on that component. 
_Hint:_ this isn't meant to be tricky; you just need to translate the code
you would naturally write in OCaml into Coq syntax.  You will need to define
one new function as part of that.
*)

Definition is_empty {A : Type} (q : queue A) : bool := 
  match q with
  | (nil, _) => true
  | _ => false
  end.

Definition front {A : Type} (q : queue A) : option A :=
  match q with 
  | (nil, _) => None
  | (cons x _, _) => Some x
  end.

Definition norm {A : Type} (q: queue A) : queue A :=
  match q with
  | (nil, b) => (rev b, nil)
  | q => q
  end.

Definition enq {A : Type} (x : A) (q : queue A) : queue A := 
  match q with 
  | (nil, _) => norm (nil, x::[])
  | (f, t) => norm (f, x::t)
  end.

Definition deq {A : Type} (q : queue A) : queue A :=
  match q with
  | (nil, _) => (nil, [])
  | (cons h t, b) => norm (t, b)
  end.

(** This "unit test" checks to make sure your implementation correctly
    uses both the front and back list on a simple example.  You should
    be able to prove it just by changing [Admitted.] to [trivial. Qed.]  
    If not, you probably have coded up the [enq] function or a helper 
    incorrectly.  In that case, fix it before moving on to the theorems 
    below. *)
Example test_two_lists : enq 1 (enq 0 empty) = ([0], [1]).
Proof. trivial. Qed.  

(** 
*** Verification of two-list queues.
Next you need to prove that the equations in the queue specification hold.
The statements of those equations below now include as a precondition
that the RI holds of any input queues.
_Hint:_ in addition to the tactics you used for simple queues, you will
also find [apply...in], [rewrite], and [assumption] to be helpful.
We suggest factoring out helper lemmas whenever you discover that
a hypothesis is difficult to work with in its current form. 
*)

Theorem eqn1 : forall (A : Type), 
  is_empty (@empty A) = true.
Proof.
  trivial.
Qed. 

Theorem eqn2 : forall (A : Type) (x : A) (q : queue A),
  rep_ok q -> is_empty (enq x q) = false.
Proof. 
  intros A x q evRep.
  destruct q as [front back].
  destruct front.
    trivial.
    destruct back. 
      all: trivial.
Qed.

Theorem eqn3 : forall (A : Type),
  front (@empty A) = None.
Proof.
  trivial.
Qed.

Theorem eqn4 : forall (A : Type) (x : A) (q : queue A),
  rep_ok q -> is_empty q = true -> front (enq x q) = Some x.
Proof.
  intros A x q evRep empty_eq_true.
  destruct q as [f b].
    destruct f.
    trivial.
    discriminate.
Qed.

Theorem eqn5 : forall (A : Type) (x : A) (q : queue A),
  rep_ok q -> is_empty q = false -> front (enq x q) = front q.
Proof.
  intros A x q evRep empty_eq_true.
  destruct q as [f b].
    simpl.
    destruct f.
      discriminate.
      trivial.
Qed.

Theorem eqn6 : forall (A : Type),
  deq (@empty A) = @empty A.
Proof.
  trivial.
Qed. 

Theorem eqn7_helper : forall (A : Type) (x : A) (q: queue A),
rep_ok q -> is_empty q = true -> q = ([], []).
Proof.
  intros.
  destruct q as [f back].
    simpl.
    destruct f.
    simpl.
      rewrite H.
      trivial.
      trivial.
      discriminate.
Qed.

(** Look into how to break this one up *)
Theorem eqn7 : forall (A : Type) (x : A) (q : queue A),
  rep_ok q -> is_empty q = true -> deq (enq x q) = empty.
Proof.
  intros A x q evRep empty_eq_true.
  destruct q as [f b].
    destruct f.
      destruct b.
        simpl.
        trivial.
        trivial.
        discriminate.
Qed.

(**
It turns out that two-list queues actually do not satisfy [eqn8]! To show that,
find a counterexample:  values for [x] and [q] that cause [eqn8] to be invalid.
Plug in your values for [x] and [q] below, then prove the three theorems
[counter1], [counter2], and [counter3].  _Hint_: if you choose your values well,
the proofs should be short and easy, requiring only [discriminate] or [trivial].
*)

Module CounterEx.

Definition x : nat := 0.  
(* change [0] to a value of your choice *)
Definition q : (list nat * list nat) := ([x], [x]). 
(* change [empty] to a value of your choice *)

Theorem counter1 : rep_ok q.
Proof.
  discriminate.
Qed.

Theorem counter2 : is_empty q = false.
Proof. 
  trivial.
Qed.

Theorem counter3 : deq (enq x q) <> enq x (deq q).
Proof.
  discriminate.
Qed.


End CounterEx.

(**
Two-list queues do satisfy a relaxed version of [eqn8], though,
where instead of requiring [deq (enq x q)] and [enq x (deq q)]
to be _equal_, we only require them to be _equivalent_ after being
converted to simple queues.  The following definition implements
that idea of equivalence:
*)

Definition equiv {A:Type} (q1 q2 : queue A) : Prop :=
  match (q1, q2) with
  | ((f1,b1),(f2,b2)) => f1 ++ rev b1 = f2 ++ rev b2
  end.

(** 
Now prove that the following relaxed form of [eqn8] holds.  _Hint:_
this is probably the hardest proof in the assignment.  Don't hesitate
to manage the complexity of the proof by stating and proving helper lemmas.
We found uses for some additional tactics in this proof:
[contradiction], [destruct (e)], and [unfold].  We also found
a theorem involving [++] from the [List] library to be helpful.
*)

(* Lemma eqn8_equiv' : forall (A : Type) (x : A) (q : queue A),
rep_ok q -> is_empty q = false -> (deq (enq x q)) *)


Lemma front_no_back : forall (A : Type) (x : A) (f : list A),
  f <> [] -> equiv (deq (enq x (f, []))) (enq x (deq (f, []))).
Proof.
  intros A x f f_not_empty.
  destruct f.
    contradiction.
    simpl.
    destruct f.
      simpl.
      unfold equiv. trivial. simpl.
      unfold equiv. simpl. trivial.
Qed.

Lemma elt_cons_front : forall (A : Type) (x : A) (f b: list A),
  f <> [] -> is_empty (f, b) = false.
Proof.
  intros.
  destruct f.
  contradiction.
  trivial.
Qed.

Lemma enq_nonempty : forall (A : Type) (x : A) (f b : list A),
  rep_ok (f,b) -> is_empty (f,b) = false -> enq x (f,b) = (f, x::b).
Proof.
  intros A x f b rep_ok is_not_empty.
  destruct f.
    destruct b.
    discriminate.
    simpl.
      discriminate.
      simpl.
      trivial.
Qed.

Lemma deq_nonempty : forall (A : Type) (x : A) (f b : list A),
  rep_ok (f,b) -> is_empty (f,b) = false -> deq (x::f,b) = (f, b).
Proof.
  intros.
  destruct f. 
    discriminate.
    trivial.
Qed.

Lemma one_front_back : forall (A : Type) (x a a0 : A) (b : list A),
  deq (enq x ([a], a0 :: b)) = (rev (x :: a0 :: b), []).
Proof.
  trivial.
Qed.

Lemma some_deq : forall (A : Type) (x a a0 : A) (b : list A), 
  deq ([a], a0 :: b) = (rev (a0 :: b), []).
Proof.
  trivial.
Qed.

Theorem eqn8_equiv : forall (A : Type) (x : A) (q : queue A),
  rep_ok q -> is_empty q = false -> 
  equiv (deq (enq x q)) (enq x (deq q)).
Proof.
  intros A x q rep_good is_not_empty.
  destruct q as [front back].
    destruct front.
      destruct back.
        discriminate. discriminate.
        destruct back.
          destruct front0.
            unfold equiv.
            simpl. trivial.
            unfold equiv.
            simpl. trivial.
            destruct front0.
              rewrite one_front_back.
              rewrite some_deq.
              unfold equiv.
              simpl.
              destruct (rev back).
                simpl. trivial.
                simpl.
                rewrite app_nil_r.
                trivial.
                assumption.
                simpl.
                unfold equiv.
                trivial.
Qed.

(**
Finally, verify that [empty] satisfies the RI, and that [enq] and [deq] both
preserve the RI.
*)

Theorem rep_ok_empty : forall (A : Type), 
  rep_ok (@empty A).
Proof. 
  intros A.
  intros evRep.
  trivial.
Qed.

Theorem rep_ok_enq : forall (A : Type) (q : queue A), 
  rep_ok q -> forall (x : A), rep_ok (enq x q).
Proof.
  intros A q rep_good.
  intros x.
  destruct q as [front back].
    destruct front.
    all: discriminate.
Qed.

Theorem rep_ok_deq: forall (A : Type) (q : queue A),
  rep_ok q -> rep_ok (deq q).
Proof.
  intros.
  destruct q.
    destruct l.
      simpl. trivial. 
      destruct l.
        trivial.
        simpl.
        destruct (rev l0).
        trivial.
        discriminate.
        discriminate.
  Qed.

End TwoListQueue.

(********************************************************************)
(** ** Part 3: Logic, and Programs as Proofs *)
(********************************************************************)

Module Logic.

(** 
Change each of the following conjectures into a definition.  Your
definition should provide a Coq program that is the proof of the 
conjecture.  For example, given
<<
Conjecture logic0 : forall P : Prop, 
  P -> P.
>>
You would transform it into
<<
Definition logic0 : forall P : Prop, 
  P -> P
:=
  fun (P : Prop) (p : P) => p.
>>
Please note that if you use tactics to find the programs 
you will negatively impact your ability to solve similar problems
on the final exam.
*)

Definition logic1 : forall P Q R S T: Prop,
  ((P /\ Q) /\ R) -> (S /\ T) -> (Q /\ S) 
:= fun (P Q R S T: Prop) (pq_and_r: ((P /\ Q) /\ R)) (s_and_t: (S /\ T)) =>
  match (pq_and_r, s_and_t) with
  | (conj (conj p q) r, conj s t) => conj q s 
  end. 

Definition logic2 : forall P Q R S : Prop,
  (P -> Q) -> (R -> S) -> (P \/ R) -> (Q \/ S)
:= fun (P Q R S: Prop) (p_imp_q: P -> Q) (r_imp_s: R -> S) (p_or_r: P \/ R) =>
  match p_or_r with
  | or_introl p => or_introl (p_imp_q p)
  | or_intror r => or_intror (r_imp_s r)
  end.

Definition logic3 : forall P Q : Prop,
  (P -> Q) -> (((P /\ Q) -> P) /\ (P -> (P /\ Q)))
:= fun (P Q: Prop) (p_imp_q: P -> Q) => 
  conj (fun (p_and_q: P /\ Q) =>  (match p_and_q with 
                                    | conj p q => p
                                  end ))
       (fun (p: P) => conj p (p_imp_q p)).

Definition logic4 : forall P Q : Prop,
  (P -> Q) -> (~~P -> ~~Q)
:= fun (P Q : Prop) (p_imp_q: P -> Q) 
      (double_neg_p: (P -> False) -> False) (neg_q: Q -> False) => 
    double_neg_p (fun (p: P) => neg_q (p_imp_q p)).
  
End Logic.

(********************************************************************)
(** ** Part 4: Induction *)
(********************************************************************)

Module Induction.

(** For the proofs in this part of the assignment, in addition
    to the tactics already used, we found these to be useful:
    [induction] and [ring]. *)

(**
Here is an OCaml function:
<<
let rec sumsq_to n = 
  if n = 0 then 0
  else n*n + sumsq_to (n-1)
>>

Prove that
<<
  sumsq_to n  =  n * (n+1) * (2*n + 1) / 6
>>
by completing the following code.
*)

(** [sumsq_to n] is [0*0 + 1*1 + ... + n*n]. *)
Fixpoint sumsq_to (n:nat) : nat :=
  match n with 
  | 0 => n
  | S k => n * n + (sumsq_to k)
  end.

Lemma sumsq_helper : forall n : nat, 
  6 * sumsq_to (S n) = 6 * (S n) * (S n) + 6 * sumsq_to n.
Proof.
  intros n. simpl. ring.
Qed.

Theorem sumsq : forall n,
  6 * sumsq_to n = n * (n+1) * (2*n+1).
Proof.
  intros n. 
  induction n as [ | k IH].
    - trivial.
    - rewrite -> sumsq_helper.
      rewrite -> IH.
      ring.
Qed.

(**
Here is a "backwards" definition of lists, which is why we spell
all the names backwards.  Unlike OCaml lists, in which as you
pattern match you encounter the first element of the list,
then the second, etc., with these lists, you encounter
the last element of the list, then the next-to-last, etc.
You may not change this definition.
*)

Inductive tsil (A : Type) : Type := 
  | lin : tsil A
  | snoc : tsil A -> A -> tsil A.

(** Don't worry about understanding these commands.  For those who
    are curious:  they make it possible to omit the [A] argument 
    when writing constructors.  E.g., to write [lin] instead
    of [lin A]. *)
Arguments lin {A}.
Arguments snoc {A} xs x.

(**
For example, the list whose first element is [1], second is [2],
and third is [3] would be written
<<
snoc (snoc (snoc lin 1) 2) 3.
>>
*)

(** [length lst] is the number of elements in [lst]. 
    You may not change this definition. *)
Fixpoint length {A : Type} (lst : tsil A) : nat :=
  match lst with
  | lin => 0
  | snoc xs _ => 1 + length xs
  end.

(** [app lst1 lst2] contains all the elements of [lst1]
    followed by all the elements of [lst2].  "app" is
    short for "append". You may not change this definition. *)
Fixpoint app {A : Type} (lst1 lst2: tsil A) : tsil A :=
  match lst2 with
  | lin => lst1
  | snoc xs x => snoc (app lst1 xs) x
  end.

(** Prove the next two theorems.  You will need to use induction.
    Think carefully about which list to induct on, based on how
    [tsil] is defined. *)

Theorem app_assoc : forall (A : Type) (lst1 lst2 lst3 : tsil A),
  app lst1 (app lst2 lst3) = app (app lst1 lst2) lst3.
Proof.
  intros A lst1 lst2 lst3.
  induction lst3 as [ | h IH t].
    - simpl. trivial.
    - simpl. rewrite <- IH. trivial.
Qed.

Theorem app_length : forall (A : Type) (lst1 lst2 : tsil A),
  length (app lst1 lst2) = length lst1 + length lst2.
Proof.
  intros A lst1 lst2.
  induction lst2 as [ | h IH t].
    - simpl. trivial.
    - simpl. rewrite -> IH. trivial.
Qed.

End Induction.

(********************************************************************)
(** THE END *)
(********************************************************************)