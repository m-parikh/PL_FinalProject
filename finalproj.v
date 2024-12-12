From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Strings.String.
Open Scope string_scope.
From Coq Require Import List.
Import ListNotations.
Require Import BinInt.
From Coq Require Import ZArith.Int.
(* Import Z_as_Int.
Delimit Scope Int_scope with I. *)
From Coq Require Import Recdef.
From Coq Require Import Program.
From Coq Require Import Lia.
From Coq Require Import Classes.RelationClasses.
(* Require Import Ascii. *)

Delimit Scope string_scope with string.
Local Open Scope string_scope.
Reserved Notation "x ++ y" (right associativity, at level 60).

 
Inductive term : Type :=
| empty
| l (l1 : string)
| nl (n: string) (l1 : string).

Inductive clause : Type :=
| ce 
| co (n1 : term) (c : clause).

Check co (l "a") (co (nl "~" "b") ce).

Inductive formula: Type :=
| fe
| fa (c : clause) (f : formula).

Definition eql (l1 l2: term) : bool :=
match l1, l2 with
| l l1', nl n' l2' => false
| nl n' l1', l l2' => false
| l l1', l l2' => eqb l1' l2'
| nl n1' l1', nl n2' l2' => eqb (n1'++l1') (n2'++l2')
| empty, empty => true
| _, _ => false
end.
  Infix "=?" := eql.

Fixpoint eqc (c1 c2: clause) : Prop :=
match c1, c2 with
| ce, ce => True
| co n1 c1', co n2 c2' => if n1 =? n2 then 
                                 eqc c1' c2' else False
| _, _ => False
end.

Fixpoint check_unsat (f: formula) : Prop :=
  match f with
    | fe => True
    | fa c1 f => match c1 with
                 | ce => False
                 | _ => check_unsat f
               end
  end.

Example unsatAST1:
check_unsat (fa (ce) (fa (co ( l ("a") ) ce) fe)) = False.
Proof.
simpl. reflexivity.
Qed.

Example satAST1:
check_unsat (fa (co ( nl "~" "b" ) ce) fe) = True.
Proof.
simpl. reflexivity.
Qed.

Fixpoint neg_clause (c: clause) : bool := 
match c with
| ce => false
| co n1 n2 => match n1 with 
                  | nl n l1 => true
                  | _ => neg_clause n2
                     end
end.

Fixpoint check_allneg (f : formula) : bool :=
  match f with
    | fe => true (* gone through all  *)
    | fa c1 f1 => match c1 with 
                | ce => false (* unsat *)
                | _ => if neg_clause c1 then check_allneg f1 else false
               end
  end.

(* is literal in the clause *)
Fixpoint literal_clause (a: term) (c: clause) : bool := 
match c with
| ce => false
| co n1 c1 => if n1 =? a then true else literal_clause a c1
end.

Fixpoint remove_clauses_literal (a: term) (f: formula) (returnthis: formula)
: formula :=
match f with 
| fe => returnthis
| fa c1 f1 => if literal_clause a c1 then remove_clauses_literal a f1 returnthis
                                  (* remove clause from formula *)
                                else remove_clauses_literal a f1 (fa c1 returnthis)
                                   (* add clause *)
end.

Fixpoint In (c: clause) (f: formula) : Prop :=
match f with 
| fe => False
| fa c1 f1 => eqc c1 c \/ In c f1
end.


(* Fixpoint eqf (f1 f2: formula) : bool :=
match f1, f2 with
| fe, fe => true
| fa c1 f1', fa c2 f2' => if eqc c1 c2 = True then 
                                 eqf f1' f2' else false
| _, _ => false
end. *)


Theorem clause_with_literal_not_in_f: forall (c: clause) (a: term) (f: formula),
(In c (remove_clauses_literal a f fe)) -> literal_clause a c = false.
Proof.
Admitted.

Notation "[ ]" := ce.


Example testremoveLiteral1: 
remove_clauses_literal (l ("c")) (
fa (co ( nl "~" "b" ) [ ]) 
(fa (co ( l ("c") ) [ ])
fe )
) (fe) = 
fa (co (nl "~" "b") [ ]) fe.
Proof.
simpl. reflexivity.
Qed.


Definition neg_eq (l1 l2: term) : bool :=
match l1, l2 with
| l l1', nl n' l2' => if eqb l1' l2' then true else false
| nl n' l1', l l2' => if eqb l1' l2' then true else false
| _,_ => false
end.

Fixpoint find_negation_literal (a: term) (c: clause) (returnthis: clause): clause := 
match c with
| ce => returnthis
| co l1 c2 => if neg_eq l1 a then 
              find_negation_literal a c2 returnthis
             else find_negation_literal a c2 (co l1 returnthis)
end.

Example testunsat: 
check_unsat (
fa (co ( nl "~" "b" ) [ ]) 
(fa [ ]
fe )
) = False.
Proof.
simpl. reflexivity.
Qed.

Example testremoveNegLiteralge1: 
find_negation_literal (l ("c")) (co ( nl "~" "b" ) (co ( nl "~" "c" ) ce)) (ce) = 
(co ( nl "~" "b" ) ce).
Proof.
simpl. reflexivity.
Qed.

Fixpoint exists_negation (a: term) (c: clause) : bool := 
match c with
| ce => false
| co l1 c2 => if neg_eq l1 a then true else exists_negation a c2
end.

(* if there is a literal then remove it from the other clauses *)
Fixpoint remove_neg_literal (a: term) (f: formula) (returnthis: formula)
: formula :=
match f with 
| fe => returnthis
| fa c f1 => if exists_negation a c 
then remove_neg_literal a f1 (fa (find_negation_literal a c ce) returnthis)
                                else remove_neg_literal a f1 (fa c returnthis)
end.

Example testremoveNegLiteral: 
remove_neg_literal (l ("c")) 
(fa (co ( nl "~" "c" ) [ ] ) fe)
 fe = 
fa [] fe
.
Proof.
simpl. reflexivity.
Qed.

Example check_unsat_again:
check_unsat (fa [] fe) = False.
Proof.
simpl. reflexivity.
Qed.


(* Fixpoint propagate (f: formula) (literal : term) (returnthis: formula)
: formula :=
match f with 
| fe => returnthis
| fa c1 f1 => match c1 with
           | ce => returnthis
           | co n1 c2 => if n1 =? literal then 
(remove_neg_literal literal (find_clauses_literal literal f fe) fe)
                                     else propagate f1 literal returnthis
          end
end.

Example test_propagate:
propagate 
(
fa (co ( l "b" ) ce) 
(fa (co ( nl "~" "b" ) (co (l "a") (co (nl "~" "d") ce)))
(fa (co ( l "a" ) (co (l "b") (co (nl "~" "f") ce))) fe)
)
) (l "b") fe
= 
fa (co (nl "~" "d") (co (l "a") [])) fe.
Proof.
simpl.  reflexivity.
Qed. *)

Fixpoint length (f: formula) : nat :=
match f with
| fe => 0
| fa c1 f1 => 1 + length f1
end.

Definition list_ind2_principle:= forall (P : formula -> Prop),
      P fe ->
      (forall (a: clause), P (fa a fe)) ->
      forall f : formula, P f.

Theorem remove_literal_smaller: 
forall (a: term) (f: formula) (c: clause),
length f > 0 /\ In c f /\ literal_clause a c = true ->
length (remove_clauses_literal a f fe) < length f.
Proof.
induction f.
- intros. easy.
- intros. inversion H.
simpl. 
induction ((if literal_clause a c
   then remove_clauses_literal a f fe
   else remove_clauses_literal a f (fa c fe))). auto.
   simpl. admit.
Admitted.


Theorem zero_le: forall (n : nat) ,
0 < S n.
Proof.
intros. auto. 
induction n. auto. rewrite IHn. auto. 
Qed.

Theorem one_le: forall (n : nat) ,
1 < S (S (S n)).
Proof.
intros. auto.
induction n.
- auto.
- rewrite IHn. auto.
Qed.


Theorem smaller: forall (a: term) (f: formula) (c : clause),
length f > 0 /\ In c f /\ literal_clause a c = true ->
length (remove_clauses_literal a (remove_neg_literal a f fe) fe) < length f.
Proof.
intros. auto.
simpl.
destruct remove_neg_literal.
- auto. simpl. apply H.
- induction remove_clauses_literal.
 + apply H.
 + simpl. induction f. simpl. easy. auto. intuition. simpl.
admit.
Admitted.

(* Function first_attempt_eval (f: formula) (literals : clause)
{measure length f}: formula :=
match f with
| fe => (fa literals f)
| fa c1 f1 => if check_allneg f then (fa literals f) else
            match c1 with 
            | ce => (fa ce fe)
            | co n1 ce => match n1 with
                          | l l1 => first_attempt_eval (propagate f n1 fe) literals
                          | _ => first_attempt_eval f1 literals
                          end
            | _ => first_attempt_eval f1 literals
            end
end.
Proof. 
intros. symmetry in teq. rewrite teq. 
destruct propagate.   
simpl. symmetry in teq. rewrite teq. simpl. apply zero_le.
simpl.

intros. simpl. auto.
intros. simpl. auto.
Admitted. *)

Fixpoint return_neg_eq (c: clause) : term :=
match c with
  | ce => empty
  | co l1 c1 => match l1 with
                | nl n l2 => l1
                | _ => return_neg_eq c1
                end
end.

Fixpoint sat_asgn (f: formula) (returnthis: clause) : clause :=
match f with 
| fe => returnthis
| fa c f1 => (sat_asgn f1 (co (return_neg_eq c) returnthis))
end.

Function attempt_eval (f: formula) (literals : formula)
{measure length f}:
formula :=
match f with
| fe => (fa (sat_asgn f ce) literals)
| fa c1 f1 => if check_allneg f then (fa (sat_asgn f ce) literals) else
            match c1 with 
            | ce => fe
            | co n1 ce => match n1 with
                          | l l1 => 
attempt_eval (remove_clauses_literal n1 (remove_neg_literal n1 f fe) fe) literals
                          | _ => attempt_eval f1 literals
                          end
            | _ => attempt_eval f1 literals
            end
end.
Proof.
intros. simpl. auto.
intros. 
apply smaller with c. split. 
- simpl. apply zero_le.
- split.
  + admit.
  + simpl. auto. admit.
- simpl. auto.
- simpl. auto.
Admitted.
