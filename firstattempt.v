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
Import Z_as_Int.
Delimit Scope Int_scope with I.
From Coq Require Import Recdef.

Module HornClause.
Open Scope Int_scope.

(* Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..). *)

(* if [] in [horn_clause list] then unsat *)
Fixpoint check_unsat (l:list (list Z)) : Prop :=
  match l with
    | [] => True
    | x::xs => match x with
                 | [] => False
                 | _ => check_unsat xs
               end
  end.

(* positive literal is zero 
all others are negative *)

Example testunsat: 
check_unsat [[(-1)%Z;(-2)%Z];[]] = False.
Proof.
reflexivity.
Qed.

Example testsat: 
check_unsat [[(-1)%Z;(-2)%Z;(3)%Z];[(1)%Z]] = True.
Proof.
reflexivity.
Qed.

Example testsatempty: 
check_unsat [] = True.
Proof.
reflexivity.
Qed.

Example testsatone: 
check_unsat [[(0)%Z]] = True.
Proof.
reflexivity.
Qed.

Example testsat2: 
check_unsat [[(-1)%Z;(-2)%Z;(3)%Z;(-4)%Z];[(-1)%Z;(-2)%Z;(3)%Z]] = True.
Proof.
reflexivity.
Qed.

Example testunsat2: 
check_unsat [[];[(-1)%Z;(-2)%Z;(3)%Z]] = False.
Proof.
reflexivity.
Qed.

Notation "x > y" := (i2z x > i2z y)%Z : Int_scope.


  Infix "=?" := eqb.
  Infix "<?" := ltb.
  Infix "<=?" := leb. 
 
Fixpoint find_neg (l: list Z) : bool := 
match l with
| [] => false
| x::xs => if (0)%Z<?x then find_neg xs else true
(* match x with 
            | x > 0 => find_neg xs
            | _ => true
            end *)
end.

Fixpoint check_allneg (l:list (list Z)) : bool :=
  match l with
    | [] => true (* gone through all  *)
    | x::xs => match x with 
                | [] => false
                | y::ys => if find_neg x then check_allneg xs else false
               end
  end.

Example testallneg: 
check_allneg [[(-1)%Z;(-2)%Z; (1)%Z ];[(-4)%Z; (-5)%Z]] = true.
Proof.
reflexivity.
Qed.

Example testnotsat: 
check_allneg [[(-1)%Z; (1)%Z];[(1)%Z]] = false.
Proof.
reflexivity.
Qed.

Example testallneg2: 
check_allneg [[(-1)%Z];[(-2)%Z];[(-3)%Z];[(-4)%Z]] = true.
Proof.
reflexivity.
Qed.

Example testallneg3: 
check_allneg [[(1)%Z];[(-1)%Z];[(-2)%Z];[(-3)%Z]] = false.
Proof.
reflexivity.
Qed.

Fixpoint find_literal (a: Z) (l: list Z) : bool := 
match l with
| [] => false
| x::xs => if x =? a then true else find_literal a xs
(* match x with 
            | x > 0 => find_neg xs
            | _ => true
            end *)
end.

(* if there is a literal then remove it from the other clauses *)
Fixpoint find_clauses_literal (a: Z) (l:list (list Z)) (returnthis: list (list Z))
: list (list Z) :=
match l with 
| [] => returnthis
| x::xs => if find_literal a x then find_clauses_literal a xs returnthis
                                else find_clauses_literal a xs (cons x returnthis)
end.

Example testfindLiteral: 
find_literal (1)%Z [(1)%Z] = 
true. 
Proof.
reflexivity.
Qed.

Example printthis:
(if (find_literal (1)%Z [(-2)%Z]) then [] else (cons [(-2)%Z] [])) = [[(-2)%Z]].
Proof.
reflexivity.
Qed.

Example sanity:
(cons [(-1)%Z] [[(-2)%Z]]) = [[(-1)%Z]; [(-2)%Z]].
Proof.
simpl.
reflexivity.
Qed.


Example testnoLiteral: 
find_clauses_literal (1)%Z [[(-1)%Z];[(-2)%Z;(-3)%Z]] [] = 
[[(-2)%Z;(-3)%Z]; [(-1)%Z]]. 
Proof.
simpl.
reflexivity.
Qed.

Example testremoveLiteral: 
find_clauses_literal (1)%Z [[(1)%Z]] [] = 
[]. 
Proof.
simpl.
reflexivity.
Qed.

Example testremoveLiteralge1: 
find_clauses_literal (1)%Z [[(1)%Z]; [(-1)%Z; (-2)%Z; (1)%Z]] [] = 
[]. 
Proof.
simpl.
reflexivity.
Qed.


Lemma testremoveLiteralge2: 
find_clauses_literal (1)%Z [[(-1)%Z]; [(-1)%Z; (-2)%Z; (1)%Z]] [] = 
[[(-1)%Z]]. 
Proof.
simpl.
reflexivity.
Qed.

Definition opp := Z.opp.
Notation "- x" := (opp x) : Int_scope.

Fixpoint find_negation_literal (a: Z) (l: list Z) (returnclause: list Z): list Z := 
match l with
| [] => returnclause
| x::xs => if x =? - a then 
              find_negation_literal a xs returnclause
             else find_negation_literal a xs (cons x returnclause)
end.

Example testfindNegLiteral: 
find_negation_literal (1)%Z [(-1)%Z] []= 
[]. 
Proof.
simpl.
reflexivity.
Qed.

Example testnofindNegLiteral: 
find_negation_literal (1)%Z [(1)%Z] [] = 
[(1)%Z]. 
Proof.
simpl.
reflexivity.
Qed.

Example testfindNegLiterallength: 
find_negation_literal (1)%Z [(-2)%Z; (-3)%Z; (-1)%Z] [] = 
[(-3)%Z; (-2)%Z]. 
Proof.
simpl.
reflexivity.
Qed.

Fixpoint exists_negation (a: Z) (l: list Z) : bool := 
match l with
| [] => false
| x::xs => if x =? - a then true else exists_negation a xs
end.

(* if there is a literal then remove it from the other clauses *)
Fixpoint remove_neg_literal (a: Z) (l:list (list Z)) (returnthis: list (list Z))
: list (list Z) :=
match l with 
| [] => returnthis
| x::xs => if exists_negation a x 
then remove_neg_literal a xs (cons (find_negation_literal a x []) returnthis)
                                else remove_neg_literal a xs (cons x returnthis)
end.

Example test_remove_negations: 
remove_neg_literal (1)%Z [
[(-4)%Z]
] [] = 
[
[(-4)%Z]
]. 
Proof.
simpl.
reflexivity.
Qed.

Fixpoint propogate (l : list (list Z)) (literal : Z) (returnthis: list (list Z))
: list (list Z) :=
match l with 
| [] => returnthis
| x::xs => match x with
           | [] => returnthis
           | y::ys => if y =? literal then (remove_neg_literal literal (find_clauses_literal literal l []) [])
                                     else propogate xs literal returnthis
          end
end.

Example test_propogate:
propogate 
[
[(1)%Z; (-2)%Z; (-3)%Z];
[(1)%Z];
[(-1)%Z; (-4)%Z; (5)%Z];
[(-1)%Z]
] (1)%Z [] = 
[
[(5)%Z; (-4)%Z];
[]
].
Proof.
intros. simpl.
reflexivity.
Qed.

Theorem lessthan0: forall n,
0 < S (S n).
Proof.
intros. auto. induction n.
apply lt_0_2.
rewrite IHn. auto.
Qed.

Function first_attempt_eval (l : list (list Z)) (literals : list Z)
{measure length l}: list (list Z) :=
match l with
| [] => (cons literals l)
| x::xs => if check_allneg l then (cons literals l) else
            match x with 
            | [] => []
            | [y] => first_attempt_eval (propogate l y []) (cons y literals)
            | _ => first_attempt_eval xs literals
            end
end.
Proof.
intros. auto. symmetry in teq. rewrite teq.
destruct propogate. simpl. auto. symmetry in teq. rewrite teq. auto.
simpl. destruct Datatypes.length. auto. auto. apply lessthan0.
simpl. subst. simpl. admit.
intros. auto.
Admitted.

