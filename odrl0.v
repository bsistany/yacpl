Module ODRL.


Require Import Arith.
Require Import Omega.
Require Import Coq.Logic.Decidable.

Set Implicit Arguments.

(* Open Scope string_scope. *)



Section nonemptylist.

Variable X : Set.

Inductive nonemptylist : Set :=
  | Single : X -> nonemptylist
  | NewList : X -> nonemptylist -> nonemptylist.


Fixpoint app_nonempty (l1 l2 : nonemptylist) : nonemptylist :=
  match l1 with
  | Single s  => NewList s l2
  | NewList s rest => NewList s (app_nonempty rest l2)
  end.

Fixpoint length_nonempty (l1 : nonemptylist) : nat :=
  match l1 with
  | Single s  => 1
  | NewList s rest => 1 + (length_nonempty rest)
  end.

Definition hd (l:nonemptylist) : X :=
  match l with
  | Single s => s
  | NewList s rest => s
  end.


Fixpoint In (a:X) (l:nonemptylist) : Prop :=
    match l with
      | Single s => s=a
      | NewList s rest => s = a \/ In a rest
    end.

Theorem in_dec :
(forall x y:X, {x = y} + {x <> y}) -> 
    forall (a:X) (l:nonemptylist), {In a l} + {~ In a l}.


Proof.
intros H; induction l as [| a0 l IHl].
apply H.
destruct (H a0 a); simpl; auto.
destruct IHl; simpl; auto.
right; unfold not; intros [Hc1| Hc2]; auto.
Defined.


End nonemptylist.


Notation "x , l" := (NewList x l) (at level 60, right associativity).
Notation "[ x ]" := (Single x).

Section Fold_Nonempty.
  Variables A B : Set.
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_nonempty (l:nonemptylist B) : A :=
    match l with
      | Single s => f s a0
      | NewList s rest => f s (fold_nonempty rest)
    end.

End Fold_Nonempty.

Section MyPair.
  Variable X : Set.
  Variable Y : Set.

  Record Twos : Set :=
  mkTwos
  {
    left    : X;
    right   : Y
  }.
End MyPair.


Section Process_Lists.

Variable X : Set.
Variable Y : Set.
Variable Z : Set.


Fixpoint process_two_lists (l1 : nonemptylist X) (l2 : nonemptylist Y) :  nonemptylist (Twos X Y) :=

let process_element_list := (fix process_element_list (e1 : X) (l2 : nonemptylist Y) :	nonemptylist (Twos X Y) :=
  match l2 with
    | Single s => Single (mkTwos e1 s)
    | NewList s rest => app_nonempty (Single (mkTwos e1 s)) (process_element_list e1 rest)
  end) in

  match l1 with
    | Single s => process_element_list s l2
    | NewList s rest => app_nonempty (process_element_list s l2) (process_two_lists rest l2)
  end.




End Process_Lists.

(*From Pierce: SF*)

Theorem pierce_eq_nat_dec : forall (n m : nat), {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].

    intros m.
    destruct m as [|m'].

      left. reflexivity.

      right. intros contra. inversion contra.

    intros m.
    destruct m as [|m'].

      right. intros contra. inversion contra.

      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined.



Definition subject := nat.
Definition NullSubject:subject := 100.
Definition Alice:subject := 101.
Definition Bob:subject := 102.
Definition Charlie:subject := 103.
Definition Bahman:subject := 104.


(* simplified *)
Definition prin := nonemptylist subject.

Definition act := nat.
Definition NullAct := 300.
Definition Play : act := 301.
Definition Print : act := 302.
Definition Display : act := 303.

Definition asset := nat.
Definition NullAsset := 900.
Definition FindingNemo : asset := 901.
Definition Alien : asset := 902.
Definition Beatles : asset := 903.
Definition LoveAndPeace : asset := 904.
Definition TheReport:asset := 905.
Definition ebook:asset := 906.

(* Definition money := string. *)

Definition policyId := nat.
Definition NullId:subject := 200.
Definition id1:policyId := 201.
Definition id2:policyId := 202.
Definition id3:policyId := 203.
Definition id4:policyId := 204.

Inductive constraint : Set :=
  | Principal : prin  -> constraint
  | Count : nat -> constraint
  | CountByPrin : prin -> nat -> constraint.

Inductive primPreRequisite : Set :=
  | TruePrq : primPreRequisite
  | Constraint : constraint -> primPreRequisite
  | NotCons : constraint -> primPreRequisite.
 
Inductive preRequisite : Set :=
  | PreRequisite : nonemptylist primPreRequisite -> preRequisite.

Definition makePreRequisite (prq:primPreRequisite) : preRequisite :=
 (PreRequisite (Single prq)).


(*
Inductive preRequisite : Set :=
  | TruePrq : preRequisite
  | Constraint : constraint -> preRequisite
  | NotCons : constraint -> preRequisite
  | AndPrqs : nonemptylist preRequisite -> preRequisite
  | OrPrqs : nonemptylist preRequisite -> preRequisite
  | XorPrqs : nonemptylist preRequisite -> preRequisite.
*)

(*** Changing the policy and policySets definintion: July 1st, 2015 ***)
Inductive primPolicy : Set :=
  | PrimitivePolicy : preRequisite -> policyId -> act -> primPolicy.

Inductive andPolicy : Set :=
  | AndPolicy : nonemptylist primPolicy -> andPolicy.

Inductive policy : Set :=
  | Policy : nonemptylist primPolicy -> policy.

Inductive primInclusivePolicySet : Set :=
  | PrimitiveInclusivePolicySet : preRequisite -> policy -> primInclusivePolicySet.

Inductive primExclusivePolicySet : Set :=
  | PrimitiveExclusivePolicySet : preRequisite -> policy  -> primExclusivePolicySet.

Inductive primPolicySet : Set :=
  | PIPS : primInclusivePolicySet -> primPolicySet
  | PEPS : primExclusivePolicySet -> primPolicySet.

Inductive andPolicySet : Set :=
  | AndPolicySet : nonemptylist primPolicySet -> andPolicySet.

Inductive policySet : Set :=
  | PPS : primPolicySet -> policySet.


Inductive agreement : Set :=
  | Agreement : prin -> asset -> policySet -> agreement.

Definition is_act_in_prim_policy (ac:act)(p:primPolicy) : Prop :=
  match p with 
    | PrimitivePolicy prq pid action => ac = action 
  end.


Fixpoint is_act_in_primPolicies (ac:act)(l:nonemptylist primPolicy){struct l}  : Prop :=
  
         match l with
           | Single pp => is_act_in_prim_policy ac pp
	   | NewList pp rest => (is_act_in_prim_policy ac pp) \/
                                (is_act_in_primPolicies ac rest)
         end.
  
Definition is_act_in_policy (ac:act)(p:policy): Prop :=

  match p with
   (* | PP pp => is_act_in_prim_policy ac pp  *)         
    | Policy ppolicies => is_act_in_primPolicies ac ppolicies
end.

Definition is_act_in_prim_policySet (ac:act)(pps:primPolicySet) : Prop :=
  match pps with 
    | PIPS pips => 
        match pips with | PrimitiveInclusivePolicySet _ pol => 
          is_act_in_policy ac pol
        end
    | PEPS peps => 
        match peps with | PrimitiveExclusivePolicySet _ pol => 
          is_act_in_policy ac pol
        end
  end.

Fixpoint is_act_in_primPolicySets (ac:act)(l:nonemptylist primPolicySet){struct l}  : Prop :=
  
  match l with
    | Single pps => is_act_in_prim_policySet ac pps
    | NewList pps rest => (is_act_in_prim_policySet ac pps) \/
                          (is_act_in_primPolicySets ac rest)
  end.
  
Definition is_act_in_policySet (ac:act)(ps:policySet): Prop :=

  match ps with
    | PPS pps => is_act_in_prim_policySet ac pps     
end.

Definition is_act_in_agreement (ac:act)(agr: agreement) : Prop :=
  match agr with
    | Agreement pr ass ps => is_act_in_policySet ac ps
  end.

Definition is_asset_in_agreement (a: asset)(agr: agreement) : Prop :=
  match agr with
    | Agreement pr ass ps => ass = a
  end.


(* Example 2.5 *)

Definition tenCount:preRequisite := (PreRequisite (Single (Constraint (Count 10)))).
Definition fiveCount:constraint := (Count 5).
Definition oneCount:constraint := (Count 1).

Definition prins2_5 := (NewList Alice (Single Bob)).




(*** 2.6 ***)
Definition prins2_6 := prins2_5.

Definition aliceCount10:preRequisite := 
 (PreRequisite (Single (Constraint (CountByPrin (Single Alice) 10)))).
Definition primPolicy2_6:policy := Policy (Single (PrimitivePolicy aliceCount10 id3 Play)).
Definition policySet2_6_modified:= 
  PPS (PEPS (PrimitiveExclusivePolicySet (makePreRequisite TruePrq) primPolicy2_6)).


(****** Environments ******)
Section Environment.


Inductive count_equality : Set :=
   | CountEquality : subject -> policyId -> nat -> count_equality.

Check count_equality.


Definition make_count_equality
  (s:subject)(id:policyId)(n:nat): count_equality :=
  CountEquality s id n.


Inductive environment : Set :=
  | SingleEnv : count_equality -> environment
  | ConsEnv :  count_equality ->  environment -> environment.


(** New getCount: simply return a number since for formal verification purposes
    it doesn't matter what that number is. The only thing that matters
    is whether the current count satisfies what the corresponding policy 
    specifies. Note that this also means we don't need to keep track of 
    environements if we assume that are always cosistent **)



(** Looks for count of a (subject, id) pair.
    Assumes e is consistent, so it returns the first count it sees for a (subject, id) pair.
	If a count for a (subject, id) pair is not found it returns 0. **)

Fixpoint getCount
  (e:environment)(s:subject)(id: policyId): nat :=

  match e with
  | SingleEnv f  =>
      match f with
	  | CountEquality s1 id1 n1 =>
	  if (beq_nat s s1)
	  then if (beq_nat id id1) then n1 else 0
	  else 0
      end
  | ConsEnv f rest =>
      match f with
	  | CountEquality s1 id1 n1 =>
	  if (beq_nat s s1)
	  then if (beq_nat id id1) then n1 else (getCount rest s id)
	  else (getCount rest s id)
      end
  end.




Definition f1:count_equality := make_count_equality Alice id2 6.
Definition f2:count_equality := make_count_equality Alice id2 7.


Definition inconsistent (f1 f2 : count_equality) : Prop :=
   match f1 with (CountEquality s1 id1 n1) =>
     match f2 with (CountEquality s2 id2 n2) =>
       s1 = s2 -> id1 = id2 -> n1 <> n2
     end
   end.

Check inconsistent.

Eval compute in (inconsistent f1 f2).


Eval compute in (6 <> 7).


Fixpoint formula_inconsistent_with_env (f: count_equality)
			  (e : environment) : Prop :=
  match e with
    | SingleEnv g =>  inconsistent f g
    | ConsEnv g rest => (inconsistent f g) \/ (formula_inconsistent_with_env f rest)
  end.



Inductive env_consistent : environment -> Prop :=
| consis_1 : forall f, env_consistent (SingleEnv f)
| consis_2 : forall f g, ~(inconsistent f g) -> env_consistent (ConsEnv f (SingleEnv g))
| consis_more : forall f e,
   env_consistent e -> ~(formula_inconsistent_with_env f e) -> env_consistent (ConsEnv f e).


(* test the first clause: single count formula should return a pair of null count formulas *)
Definition e1 : environment :=
  (SingleEnv (make_count_equality Alice id1 8)).

(* test the second clause: two count formulas should return a pair of the two count formulas *)
Definition e2 : environment := (ConsEnv f1 (SingleEnv f2)).

(* test the third case: three count formulas should return a list of 3 pairs of count formulas *)
Definition e3 : environment :=
  (ConsEnv (make_count_equality Alice id1 8)
     (ConsEnv (make_count_equality Bob id2 9) (SingleEnv (make_count_equality Charlie id3 10)))).

(* test the third case with 4 count formulas: should return a list of 6 pairs of count formulas *)
Definition e4 : environment :=
  (ConsEnv (make_count_equality Alice id1 8)
     (ConsEnv (make_count_equality Bob id2 9)
	(ConsEnv (make_count_equality Charlie id3 10)
	  (SingleEnv (make_count_equality Bahman id4 11))))).
(****************************************)
(****************************************)




Eval compute in (env_consistent e2).




End Environment.

Section Results.

Inductive answer : Set :=
  | Permitted : answer
  | Unregulated : answer
  | NotPermitted : answer.


Inductive result : Set :=
  | Result : answer -> subject -> act -> asset -> result.


Inductive queryResult: Prop :=
  | QueryResult : nonemptylist result -> queryResult.


Definition isResultInQueryResult (res:result)(results: nonemptylist result) : Prop :=
  In res results.

Definition permittedResult (s:subject)(ac:act)(ass:asset) : result :=
  (Result Permitted s ac ass).

Definition notPermittedResult (s:subject)(ac:act)(ass:asset) : result :=
  (Result NotPermitted s ac ass).

Definition unregulatedResult (s:subject)(ac:act)(ass:asset) : result :=
  (Result Unregulated s ac ass).

Definition isPermissionGranted (s:subject)(ac:act)(ass:asset)
   (results: nonemptylist result) : Prop :=
  (In (permittedResult s ac ass) results) /\
  ~(In (notPermittedResult s ac ass) results).

Definition isPermissionDenied (s:subject)(ac:act)(ass:asset)
   (results: nonemptylist result) : Prop :=
  ~(In (permittedResult s ac ass) results) /\
  (In (notPermittedResult s ac ass) results).

Definition isPermissionUnregulated (s:subject)(ac:act)(ass:asset)
  (results: nonemptylist result) : Prop :=
     (In (unregulatedResult s ac ass) results) /\
    ~(In (permittedResult s ac ass) results) /\
    ~(In (notPermittedResult s ac ass) results).

Definition makeResult
  (ans:answer)(s:subject)(ac:act)(ass:asset) : result := 
 (Result ans s ac ass).


Check permittedResult.

End Results.

(******* Semantics ********)

Section Sems.



Definition eq_type := nat -> nat -> Prop.

Check Twos.


Check prod.





(* is x in prin? *)
(** Definition prin := nonemptylist subject. **)
Fixpoint trans_prin
  (x:subject)(p: prin): Prop :=

  match p with
    | Single s => (x=s)
    | NewList s rest => ((x=s) \/ trans_prin x rest)
  end.


Fixpoint getId (p:policy) : nonemptylist policyId :=

 let getIds
    := (fix getIds (ppolicies: nonemptylist primPolicy) : nonemptylist policyId :=
	  match ppolicies with
	    | Single pp => 
                match pp with
                  | PrimitivePolicy prereq pid action => Single pid
                end
	    | NewList pp rest => 

               app_nonempty 
                (match pp with
                  | PrimitivePolicy prereq pid action => Single pid
                end)
                (getIds rest)

	  end) in
  match p with
    | Policy policies => getIds policies
end.


Fixpoint trans_count_aux (e:environment)(ids_and_subjects : nonemptylist (Twos policyId subject)) : nat :=
  match ids_and_subjects with
	| Single pair1 => getCount e (right pair1) (left pair1)
	| NewList pair1 rest_pairs =>
	    (getCount e (right pair1)(left pair1)) +
	    (trans_count_aux e rest_pairs)
  end.

Theorem getCountGtEqualZero:
  forall (e:environment)(s:subject)(id: policyId),
    (getCount e s id) >= 0.
Proof.
intros. destruct e. destruct c.
unfold getCount.
case_eq (beq_nat s s0).
intuition.
intuition.
destruct c.
unfold getCount.
case_eq (beq_nat s s0).
intuition.
intuition.
Qed.

Theorem trans_count_auxGtEqualZero:
  forall (e:environment)(ids_and_subjects : nonemptylist (Twos policyId subject)),
    (trans_count_aux e ids_and_subjects) >= 0.
Proof.
intros. destruct e. destruct c. unfold trans_count_aux. induction ids_and_subjects.
apply getCountGtEqualZero. intuition.
destruct c. unfold trans_count_aux. induction ids_and_subjects.
apply getCountGtEqualZero. intuition.
Qed.
Theorem trans_count_aux_dec: 
  forall (e:environment)(ids_and_subjects : nonemptylist (Twos policyId subject))(n:nat), 
    {trans_count_aux e ids_and_subjects < n} + 
 {~ (trans_count_aux e ids_and_subjects < n)}.
Proof.
intros.
case (lt_dec (trans_count_aux e ids_and_subjects) n).
intros H'. auto.
intros H'. auto.
Defined.

Fixpoint trans_count
  (e:environment)(n:nat)(IDs:nonemptylist policyId)
  (prin_u:prin) : Prop :=
  let ids_and_subjects := process_two_lists IDs prin_u in
  let running_total := trans_count_aux e ids_and_subjects in
  running_total < n.

Theorem trans_count_dec: 
  forall (e:environment)(n:nat)(IDs:nonemptylist policyId)(prin_u:prin), 
    {trans_count e n IDs prin_u} + {~ trans_count e n IDs prin_u}.
Proof.
intros.
destruct e. simpl.
apply trans_count_aux_dec. simpl.
apply trans_count_aux_dec.
Defined.

Definition trans_count_333 (n:nat) : nat -> Prop :=
  (fun running_total : nat => running_total < n).

Definition trans_count_444 (n:nat) : Prop :=
 forall (running_total:nat), running_total < n.

Definition trans_count_old2 (n:nat) : Prop :=
  let running_total := 4 in (** this is some nat for now. 
                                As far as proofs are concerned it 
                                doesn't matter how we obtain it so '4' will do
                             **)
  running_total < n.

Fixpoint trans_constraint
  (e:environment)(x:subject)(const:constraint)(IDs:nonemptylist policyId)
  (prin_u:prin){struct const} : Prop :=
(*************************************************)
(*************************************************)
  match const with
    | Principal prn => trans_prin x prn

    | Count n => trans_count e n IDs prin_u

    | CountByPrin prn n => trans_count e n IDs prn

  end.



Definition trans_notCons
  (e:environment)(x:subject)(const:constraint)(IDs:nonemptylist policyId)(prin_u:prin) : Prop :=
  ~ (trans_constraint e x const IDs prin_u).

Definition trans_primPreRequisite
  (e:environment)(x:subject)(prq:primPreRequisite)(IDs:nonemptylist policyId)
  (prin_u:prin) : Prop :=
   match prq with
    | TruePrq => True
    | Constraint const => trans_constraint e x const IDs prin_u
    | NotCons const => trans_notCons e x const IDs prin_u
   end.

Fixpoint trans_andPrqs
    (e:environment)(x:subject)
    (prqs:nonemptylist primPreRequisite)
    (IDs:nonemptylist policyId)(prin_u:prin) {struct prqs}: Prop :=
   
   match prqs with
     | Single prq => trans_primPreRequisite e x prq IDs prin_u 
     | NewList prq' rest_prqs => 
         (trans_primPreRequisite e x prq' IDs prin_u) /\
         (trans_andPrqs e x rest_prqs IDs prin_u)

   end.



Definition trans_preRequisite
  (e:environment)(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin) : Prop :=

  match prq with
    | PreRequisite prqs => trans_andPrqs e x prqs IDs prin_u
  end.

Definition process_single_pp_trans_policy_unregulated
   (pp: primPolicy)(x:subject)
   (a:asset)(action_from_query: act)  : nonemptylist result :=
  match pp with
    | PrimitivePolicy prq' policyId action =>
        (Single (makeResult Unregulated x action_from_query a))
  end.

Fixpoint trans_pp_list_trans_policy_unregulated
  (pp_list:nonemptylist primPolicy)(x:subject)
  (a:asset)(action_from_query: act){struct pp_list}:=
   match pp_list with
     | Single pp1 => process_single_pp_trans_policy_unregulated pp1 x a action_from_query
     | NewList pp pp_list' => app_nonempty
	 (process_single_pp_trans_policy_unregulated pp x a action_from_query) 
	 (trans_pp_list_trans_policy_unregulated pp_list' x a action_from_query)
   end.

Fixpoint trans_policy_unregulated
  (e:environment)(x:subject)(p:policy)(a:asset)
  (action_from_query: act){struct p} : nonemptylist result :=

  match p with
     | Policy pp_list => trans_pp_list_trans_policy_unregulated pp_list x a action_from_query
  end.

Definition process_single_pp_trans_policy_negative
   (pp: primPolicy)(x:subject)
   (a:asset)(action_from_query: act)  : nonemptylist result :=
  match pp with
    | PrimitivePolicy prq' policyId action =>
 
          if (pierce_eq_nat_dec action_from_query action)
          then
            (Single 
              (makeResult NotPermitted x action_from_query a))
          else
            (Single 
              (makeResult Unregulated x action_from_query a))

  end.

Fixpoint trans_pp_list_trans_policy_negative 
  (pp_list:nonemptylist primPolicy)(x:subject)
  (a:asset)(action_from_query: act){struct pp_list}:=
   match pp_list with
     | Single pp1 => process_single_pp_trans_policy_negative pp1 x a action_from_query
     | NewList pp pp_list' => app_nonempty
	 (process_single_pp_trans_policy_negative pp x a action_from_query) 
	 (trans_pp_list_trans_policy_negative pp_list' x a action_from_query)
   end.


Fixpoint trans_policy_negative
  (e:environment)(x:subject)(p:policy)(a:asset)
  (action_from_query: act){struct p} : nonemptylist result :=

  match p with
  
  | Policy pp_list => trans_pp_list_trans_policy_negative pp_list x a action_from_query
  end.


Fixpoint is_subject_in_prin (s:subject)(p:prin): Prop :=
  match p with
  | Single s'  => s=s'
  | NewList s' rest => s=s' \/ (is_subject_in_prin s rest)
  end.

Theorem subject_in_prin_dec :
    forall (a:subject) (l:prin), {is_subject_in_prin a l} + {~ is_subject_in_prin a l}.

Proof.
induction l as [| a0 l IHl].
apply pierce_eq_nat_dec.
destruct (pierce_eq_nat_dec a0 a); simpl; auto.
destruct IHl; simpl; auto.
right; unfold not; intros [Hc1| Hc2]; auto.
Defined.

Theorem trans_prin_dec :
   forall (x:subject)(p: prin),
     {trans_prin x p} + {~trans_prin x p}.

Proof.

apply subject_in_prin_dec.
Defined.

Theorem double_neg_constraint:
 forall (e:environment)(x:subject)
 (const:constraint)(IDs:nonemptylist policyId)(prin_u:prin),
  (trans_constraint e x const IDs prin_u) ->
   ~~(trans_constraint e x const IDs prin_u).
Proof.
intros e x const IDs prin_u.
intros H. unfold not. intros H'. apply H'. exact H. Qed.


Theorem trans_constraint_dec :
forall (e:environment)(x:subject)
(const:constraint)(IDs:nonemptylist policyId)(prin_u:prin),
     {trans_constraint e x const IDs prin_u} + 
     {~trans_constraint e x const IDs prin_u}.

Proof.
intros e x const IDs prin_u.

induction const. simpl.
apply trans_prin_dec.
simpl.
apply trans_count_dec.
simpl.
apply trans_count_dec.
Defined.




Theorem trans_negation_constraint_dec :
forall (e:environment)(x:subject)
(const:constraint)(IDs:nonemptylist policyId)(prin_u:prin),
     {~trans_constraint e x const IDs prin_u} + 
     {~~trans_constraint e x const IDs prin_u}.

Proof.
intros e x const IDs prin_u.
pose (j:= trans_constraint_dec e x const IDs prin_u). 
destruct j. apply double_neg_constraint in t. right. exact t. left. exact n. Defined.





Theorem trans_notCons_dec :
forall (e:environment)(x:subject)
(const:constraint)(IDs:nonemptylist policyId)(prin_u:prin),
   {trans_notCons e x const IDs prin_u} + 
   {~ trans_notCons e x const IDs prin_u}.
Proof.
intros e x const IDs prin_u. 
unfold trans_notCons. apply trans_negation_constraint_dec. Defined.

Theorem trans_primPreRequisite_dec :
  forall (e:environment)(x:subject)
    (prq:primPreRequisite)(IDs:nonemptylist policyId)(prin_u:prin),
       {trans_preRequisite e x (makePreRequisite prq) IDs prin_u} +
       {~ trans_preRequisite e x (makePreRequisite prq) IDs prin_u}.
Proof.
simpl.
destruct prq as [theTruePrq | theConst | theNotConst].  
simpl. auto.
simpl. apply trans_constraint_dec.
simpl. apply trans_notCons_dec.
Defined.

Check nonemptylist_ind.

Theorem trans_prq_list_idetity:
  forall (e:environment)(x:subject)(prq' : primPreRequisite)
    (rest_prqs : nonemptylist primPreRequisite)
    (IDs:nonemptylist policyId)(prin_u:prin),
 (trans_andPrqs e x (prq', rest_prqs) IDs prin_u) =
 ((trans_primPreRequisite e x prq' IDs prin_u) /\
  (trans_andPrqs e x rest_prqs IDs prin_u)).
Proof.
intros. simpl. auto. Defined.


Theorem trans_prq_restprq_implies_all:
  forall (e:environment)(x:subject)(prq' : primPreRequisite)
    (rest_prqs : nonemptylist primPreRequisite)
    (IDs:nonemptylist policyId)(prin_u:prin),

      ({trans_andPrqs e x rest_prqs IDs prin_u} +
      {~ trans_andPrqs e x rest_prqs IDs prin_u}) ->
 
   ({trans_andPrqs e x (prq', rest_prqs) IDs prin_u} +
   {~ trans_andPrqs e x (prq', rest_prqs) IDs prin_u}).
Proof. 
intros.
specialize trans_primPreRequisite_dec with e x prq' IDs prin_u.
intros. simpl in H0.
specialize trans_prq_list_idetity with e x prq' rest_prqs IDs prin_u.
intros.
rewrite -> H1.
tauto.
Defined.

Theorem trans_preRequisite_dec :
  forall (e:environment)(x:subject)
    (prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin),
       {trans_preRequisite e x prq IDs prin_u} +
       {~ trans_preRequisite e x prq IDs prin_u}.
Proof.

intros.
induction prq as [primPrqs].
induction primPrqs as [prq | prq' rest_prqs].
apply trans_primPreRequisite_dec.
simpl.
apply trans_prq_restprq_implies_all.
simpl in IHrest_prqs. assumption.
Defined. 

Theorem act_in_primPolicy_dec :
    forall (ac:act) (p:primPolicy), 
      {is_act_in_prim_policy ac p} + {~ is_act_in_prim_policy ac p}.

Proof.
intros ac p. destruct p. simpl. apply pierce_eq_nat_dec. Defined.

Theorem act_in_primPolicies_dec:
   forall (ac:act) (l:nonemptylist primPolicy), 
      {is_act_in_primPolicies ac l} + {~ is_act_in_primPolicies ac l}.

Proof.
induction l as [| a0 l IHl].

destruct x; apply pierce_eq_nat_dec.

destruct a0. destruct (pierce_eq_nat_dec a ac). simpl. auto.

destruct IHl. simpl. auto.

right. unfold not. intros [Hc1| Hc2]. auto. auto.
Defined.



Theorem act_in_policy_dec :
    forall (ac:act) (p:policy), 
      {is_act_in_policy ac p} + {~ is_act_in_policy ac p}.

Proof.
intros ac p. induction p.
apply act_in_primPolicies_dec.
Defined.

Theorem act_in_primPolicySet_dec :
    forall (ac:act) (pps:primPolicySet), 
      {is_act_in_prim_policySet ac pps} + {~ is_act_in_prim_policySet ac pps}.

Proof.
intros ac pps. destruct pps. 
 destruct p; apply act_in_policy_dec.
 destruct p; apply act_in_policy_dec. 
Defined.


Theorem act_in_primPolicySets_dec:
   forall (ac:act) (l:nonemptylist primPolicySet), 
      {is_act_in_primPolicySets ac l} + {~ is_act_in_primPolicySets ac l}.

Proof.
induction l as [| a0 l IHl].
apply act_in_primPolicySet_dec.
destruct (act_in_primPolicySet_dec ac a0); simpl; auto.
destruct IHl; simpl; auto.
right; unfold not; intros [Hc1| Hc2]; auto.
Defined.

Theorem act_in_policySet_dec :
    forall (ac:act) (p:policySet), 
      {is_act_in_policySet ac p} + {~ is_act_in_policySet ac p}.

Proof.
intros ac p. induction p.
apply act_in_primPolicySet_dec. 
Defined.

Theorem act_in_agreement_dec :
    forall (ac:act) (agr: agreement), 
      {is_act_in_agreement ac agr} + {~ is_act_in_agreement ac agr}.
Proof.
 intros ac agr. induction agr as [prn ass ps].
 simpl.
 apply act_in_policySet_dec. Defined.

Definition process_single_pp_trans_policy_positive 
   (pp: primPolicy)(e:environment)(x:subject)(prin_u:prin)
   (a:asset)(action_from_query: act)  : nonemptylist result :=
  match pp with
    | PrimitivePolicy prq' policyId action =>
        if (trans_preRequisite_dec e x prq' (Single policyId) prin_u)
        then (* prin /\ prq /\ prq' *)
          if (pierce_eq_nat_dec action_from_query action)
          then
            (Single 
              (makeResult Permitted x action_from_query a))
          else
            (Single 
              (makeResult Unregulated x action_from_query a))
        else (* prin /\ prq /\ ~prq' *)
          (Single 
              (makeResult Unregulated x action_from_query a))
  end.

Fixpoint trans_pp_list_trans_policy_positive 
  (pp_list:nonemptylist primPolicy)(e:environment)(x:subject)
  (prin_u:prin)(a:asset)(action_from_query: act){struct pp_list}:=
   match pp_list with
     | Single pp1 => process_single_pp_trans_policy_positive pp1 e x prin_u a action_from_query
     | NewList pp pp_list' => app_nonempty
	 (process_single_pp_trans_policy_positive pp e x prin_u a action_from_query) 
	 (trans_pp_list_trans_policy_positive pp_list' e x prin_u a action_from_query)
   end.

Definition trans_policy_positive
  (e:environment)(x:subject)(p:policy)(prin_u:prin)(a:asset)
  (action_from_query: act) : nonemptylist result :=
  match p with
    | Policy pp_list => trans_pp_list_trans_policy_positive pp_list e x prin_u a action_from_query
  end.


Definition trans_policy_PIPS
  (e:environment)(prq: preRequisite)(p:policy)(x:subject)
  (prin_u:prin)(a:asset)(action_from_query:act) : nonemptylist result :=
  
    if (trans_prin_dec x prin_u)
    then (* prin *)
      if (trans_preRequisite_dec e x prq (getId p) prin_u)
      then (* prin /\ prq *)
        (trans_policy_positive e x p prin_u a action_from_query)                           
      else (* prin /\ ~prq *)
        (trans_policy_unregulated e x p a action_from_query)
    else (* ~prin *)
      (trans_policy_unregulated e x p a action_from_query).

Definition trans_policy_PEPS
  (e:environment)(prq: preRequisite)(p:policy)(x:subject)
  (prin_u:prin)(a:asset)(action_from_query:act) : nonemptylist result :=
  
  if (trans_prin_dec x prin_u)
  then (* prin *)
    if (trans_preRequisite_dec e x prq (getId p) prin_u)
    then (* prin /\ prq *)
      (trans_policy_positive e x p prin_u a action_from_query)
    else (* prin /\ ~prq *)
      (trans_policy_unregulated e x p a action_from_query)
  else (* ~prin *)
    (trans_policy_negative e x p a action_from_query).





Fixpoint trans_ps
  (e:environment)(action_from_query:act)(subject_from_query:subject)(asset_from_query:asset)
  (ps:policySet)
  (prin_u:prin)(a:asset){struct ps} : nonemptylist result :=

let process_single_ps := (fix process_single_ps (pps: primPolicySet):=
  
  match pps with 
    | PIPS pips => 
        match pips with 
          | PrimitiveInclusivePolicySet prq p => 
            (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)                
        end
    | PEPS peps => 
        match peps with 
          | PrimitiveExclusivePolicySet prq p => 
            (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query)
        end  
   end) in


let trans_ps_list := 
  (fix trans_ps_list (ps_list:nonemptylist primPolicySet)(prin_u:prin)(a:asset){struct ps_list}:=
     match ps_list with
       | Single pps1 => process_single_ps pps1
       | NewList pps pps_list' => 
           app_nonempty (process_single_ps pps) (trans_ps_list pps_list' prin_u a)
     end) in

if (pierce_eq_nat_dec asset_from_query a)
then (* asset_from_query = a *)  
    match ps with
      | PPS pps => process_single_ps pps
    end
else (* asset_from_query <> a *)
       (Single 
          (makeResult 
             Unregulated subject_from_query action_from_query asset_from_query)).
    
  

Definition trans_agreement
   (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset) : nonemptylist result :=

   match ag with
   | Agreement prin_u a ps => 
       (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)
   end.
End Sems.





Definition get_Prin_From_Agreement(agr:agreement): prin :=
  match agr with
   | Agreement prin_u a ps => prin_u
   end.

Definition get_Asset_From_Agreement(agr:agreement): asset :=
  match agr with
   | Agreement prin_u a ps => a
   end.

Definition get_PS_From_Agreement(agr:agreement): policySet :=
  match agr with
   | Agreement prin_u a ps => ps
   end.



(** Example 2.1 **)

Definition ps_21_p1:primPolicy := 
  (PrimitivePolicy (makePreRequisite (Constraint (Count  5))) id1 Print).



Definition ps_21_p2prq1:primPreRequisite := 
  (Constraint (Principal (Single Alice))).
Definition ps_21_p2prq2:primPreRequisite := 
  (Constraint (Count 2)).
Definition ps_21_prq:preRequisite := 
  (PreRequisite (NewList ps_21_p2prq1 (Single ps_21_p2prq2))).

Definition ps_21_p2:primPolicy := 
  (PrimitivePolicy ps_21_prq id2 Print).

Definition ps_21_p:policy := 
  (Policy (NewList ps_21_p1 (Single ps_21_p2))).

Definition ps_21:primPolicySet :=
  PIPS (PrimitiveInclusivePolicySet
    (makePreRequisite TruePrq) ps_21_p).

Definition A21 := Agreement (NewList Alice (Single Bob)) TheReport (PPS ps_21).
		

Definition e_21_1 : environment :=
 (ConsEnv (make_count_equality Bob id1 0)
   (ConsEnv (make_count_equality Bob id2 0)
     (ConsEnv (make_count_equality Alice id1 0)
       (SingleEnv (make_count_equality Alice id2 0))))).

(* 

Eval compute in (trans_policy_PIPS e_21_1 TruePrq ps_21_p 
  Alice
 (NewList Alice (Single Bob)) TheReport Print).

 
Eval compute in (trans_ps e_21_1 Print Alice TheReport 
 (PPS ps_21) 
 (NewList Alice (Single Bob)) 
  TheReport).
*)
Eval compute in (trans_agreement e_21_1 A21 Print Alice TheReport).

Definition e_21_2 : environment :=
 (ConsEnv (make_count_equality Bob id1 0)
   (ConsEnv (make_count_equality Bob id2 0)
     (ConsEnv (make_count_equality Alice id1 10)
       (SingleEnv (make_count_equality Alice id2 10))))).


Eval compute in (trans_agreement e_21_2 A21 Print Alice TheReport).


(***** 3.1 *****)



(*** Canonical Agreement example ***)
Section A1.

Definition psA1:policySet :=
  PPS (PIPS (PrimitiveInclusivePolicySet
             (makePreRequisite TruePrq)
            (Policy (Single (PrimitivePolicy 
                      (makePreRequisite (Constraint (Count  5))) id1 Print))))).

Definition AgreeCan := Agreement (Single Alice) TheReport psA1.
Definition eA1 : environment :=
  (SingleEnv (make_count_equality Alice id1 2)).

Eval compute in (trans_agreement eA1 AgreeCan).

Theorem AnswersEqual: forall (ans1:answer)(ans2:answer)(s:subject)(ac:act)(ass:asset),
 (ans1=ans2) -> ((Result ans1 s ac ass) = (Result ans2 s ac ass)).
Proof.
intros. subst. reflexivity. Qed.

Theorem eq_add_S : forall(n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.




Theorem AnswersNotEqual: forall (ans1:answer)(ans2:answer)(s:subject)(ac:act)(ass:asset),
  (ans1<>ans2) -> ((Result ans1 s ac ass) <> (Result ans2 s ac ass)).
Proof.
intros. intuition. inversion H0. apply H in H2. contradiction. Qed.
(***** 'simpl' takes too long: temporarily comment out *****)
(**

Theorem SSS: 
  isPermissionGranted Alice Print TheReport (trans_agreement eA1 AgreeCan Print Alice TheReport).

Proof.

unfold trans_agreement.
unfold isPermissionGranted.
simpl.
split.



unfold trans_policy_PIPS.
destruct (trans_prin_dec Alice [Alice]).
destruct (trans_preRequisite_dec eA1 Alice (Constraint (Count 5)) [id1] [Alice]).
destruct (trans_preRequisite_dec eA1 Alice TruePrq
        (getId (Policy [PrimitivePolicy (Constraint (Count 5)) id1 Print]))
        [Alice]).
simpl.
destruct (trans_preRequisite_dec eA1 Alice (Constraint (Count 5)) [id1] [Alice]).
simpl.
unfold makeResult. unfold permittedResult. auto.
simpl in n. unfold trans_count in n. omega. 
simpl in n. intuition. 
simpl in n. unfold trans_count in n. omega.
simpl.
simpl in n.
assert (Alice=Alice). auto. contradiction.


unfold trans_policy_PIPS.
destruct (trans_prin_dec Alice [Alice]).
destruct (trans_preRequisite_dec eA1 Alice TruePrq
        (getId (Policy [PrimitivePolicy (Constraint (Count 5)) id1 Print]))
        [Alice]).
simpl.
destruct (trans_preRequisite_dec eA1 Alice (Constraint (Count 5)) [id1] [Alice]).
unfold makeResult. unfold notPermittedResult. simpl. 
apply AnswersNotEqual. intuition. inversion H.
simpl in n. unfold trans_count in n. omega. 
simpl in n. intuition. 
simpl.
simpl in n.
assert (Alice=Alice). auto. contradiction.

Qed.
**)

End A1.

Section Example4_3.

Definition ps_alice:policySet := 
  PPS (PIPS (PrimitiveInclusivePolicySet (makePreRequisite TruePrq) 
   (Policy (Single (PrimitivePolicy (makePreRequisite TruePrq) id1 Print))))).

Definition agr := Agreement (Single Alice) TheReport ps_alice.
Definition e_agr : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement e_agr agr).

Definition ps_bob:policySet := 
   PPS (PEPS (PrimitiveExclusivePolicySet (makePreRequisite TruePrq) 
   (Policy (Single (PrimitivePolicy (makePreRequisite TruePrq) id2 Print))))).
Definition agr' := Agreement (Single Bob) TheReport ps_bob.
Definition e_agr' : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement e_agr' agr').

End Example4_3.

Section A2.

(**  getCount Alice "id1" = 5,	and see if you can prove ~(Unregulated Alice ...). **)

(**  getCount Alice "id1" = 3,	and see if you can prove (Permitted Alice ...). **)

Definition eA2 : environment :=
  (SingleEnv (make_count_equality Alice id1 3)).

Definition psA2:policySet :=
  PPS (PIPS (PrimitiveInclusivePolicySet
             (makePreRequisite TruePrq)
            (Policy (Single (PrimitivePolicy 
              (makePreRequisite (Constraint (Count  5))) id1 Print))))).

Definition AgreeA2 := Agreement (Single Alice) TheReport psA2.

Eval compute in (trans_agreement eA2 AgreeA2 Bob Print TheReport).


(* Hypothesis AliceCount : getCount Alice "id1" = 5. *)
(*
Theorem SS1: 
isPermissionGranted Alice Print TheReport (trans_agreement eA2 AgreeA2 Print Alice TheReport).

Proof. 


unfold trans_agreement.
unfold isPermissionGranted.
split.


unfold permittedResult.
simpl.
unfold trans_policy_PIPS.
destruct (trans_prin_dec Alice [Alice]).
destruct (trans_preRequisite_dec eA2 Alice (Constraint (Count 5)) [id1] [Alice]).
destruct (trans_preRequisite_dec eA2 Alice TruePrq
        (getId (Policy [PrimitivePolicy (Constraint (Count 5)) id1 Print]))
        [Alice]).
simpl.
destruct (trans_preRequisite_dec eA2 Alice (Constraint (Count 5)) [id1] [Alice]).
simpl.
unfold makeResult. auto.
simpl in n. unfold trans_count in n. omega. 
simpl in n. intuition. 
simpl in n. unfold trans_count in n. omega.
simpl.
simpl in n.
assert (Alice=Alice). auto. contradiction.

unfold notPermittedResult.
simpl.
unfold trans_policy_PIPS.
destruct (trans_prin_dec Alice [Alice]).
destruct (trans_preRequisite_dec eA2 Alice TruePrq
        (getId (Policy [PrimitivePolicy (Constraint (Count 5)) id1 Print]))
        [Alice]).
simpl.
destruct (trans_preRequisite_dec eA2 Alice (Constraint (Count 5)) [id1] [Alice]).
unfold makeResult. simpl. 
apply AnswersNotEqual. intuition. inversion H.
simpl in n. unfold trans_count in n. omega. 
simpl in n. intuition. 
simpl.
simpl in n.
assert (Alice=Alice). auto. contradiction.
Qed.

*)

(* don't use the hypothesis. Add it directy to the Theorem statement *)

Theorem BobUnregulated: 
  (trans_prin Bob (get_Prin_From_Agreement AgreeA2)) -> 
     isPermissionUnregulated Bob Print TheReport (trans_agreement eA2 AgreeA2 Print Bob TheReport).

Proof.

unfold trans_agreement.
unfold isPermissionUnregulated.
split.


unfold unregulatedResult.
simpl.
unfold makeResult. auto.

split.

unfold trans_agreement.
unfold permittedResult.
simpl.
unfold makeResult.
apply AnswersNotEqual. intuition. inversion H0.

unfold trans_agreement.
unfold notPermittedResult.
simpl.
unfold makeResult.
apply AnswersNotEqual. intuition. inversion H0.
Qed.

End A2.



Section A3.

Definition eA3 : environment :=
  (ConsEnv (make_count_equality Alice id1 3)
     (ConsEnv (make_count_equality Alice id2 0)
	(ConsEnv (make_count_equality Bob id1 4)
	  (SingleEnv (make_count_equality Bob id2 0))))).
End A3.



Section A5.

Definition prin_bob := (Single Bob). 
Definition single_pol:policy := 
  Policy (Single (PrimitivePolicy (makePreRequisite TruePrq) id3 Print)).
Definition two_pols:policy := Policy 
  (NewList (PrimitivePolicy (makePreRequisite TruePrq) id1 Display)
     (Single (PrimitivePolicy (makePreRequisite TruePrq) id3 Print))).

Definition single_pol_set:policySet := 
  PPS (PEPS (PrimitiveExclusivePolicySet (makePreRequisite TruePrq) single_pol)).
Definition two_pol_set:policySet := 
  PPS (PEPS (PrimitiveExclusivePolicySet (makePreRequisite TruePrq) two_pols)).

Definition AgreeA5_single := Agreement prin_bob LoveAndPeace single_pol_set.
Definition AgreeA5_two := Agreement prin_bob LoveAndPeace two_pol_set.

Definition eA5 : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement eA5 AgreeA5_single).



Theorem T1_A5: 
forall x, (x<>Bob) ->
  isPermissionDenied x Print LoveAndPeace (trans_agreement eA5 AgreeA5_two Print x LoveAndPeace).


Proof. 
intros x H.

unfold trans_agreement.
unfold isPermissionDenied.
split.


unfold permittedResult.
simpl.
unfold trans_policy_PEPS.
destruct (trans_prin_dec x prin_bob).
destruct (trans_preRequisite_dec eA5 x (makePreRequisite TruePrq) 
           (getId two_pols) prin_bob).
simpl.
destruct (trans_preRequisite_dec eA5 x (makePreRequisite TruePrq) [id1] prin_bob).
destruct (trans_preRequisite_dec eA5 x (makePreRequisite TruePrq) [id3] prin_bob).
simpl.
unfold makeResult.
intuition.
simpl in n. intuition. 
simpl in n. intuition. 
simpl in n. intuition.
simpl.
unfold makeResult.
intuition. inversion H1. 
apply AnswersNotEqual in H1. auto. intuition. inversion H0.


unfold trans_agreement.
unfold notPermittedResult.
simpl.
unfold trans_policy_PEPS.
destruct (trans_prin_dec x prin_bob).
destruct (trans_preRequisite_dec eA5 x (makePreRequisite TruePrq) (getId two_pols) prin_bob).
simpl in t. contradiction.
simpl in n. intuition.
simpl. unfold makeResult.
right. auto. Qed.
Theorem T2_A5: isPermissionDenied Alice Print LoveAndPeace 
  (trans_agreement eA5 AgreeA5_two Print Alice LoveAndPeace).


Proof. 

apply T1_A5. 

intuition. inversion H. Qed.

End A5.



Section Query.

(* a query is a tuple: (agreements * subject * act * asset * environment)  *)

Inductive single_query : Set :=
   | SingletonQuery : agreement -> subject -> act -> asset -> environment -> single_query.


Inductive general_query : Set :=
   | GeneralQuery : nonemptylist agreement -> subject -> act -> asset -> environment -> general_query.


Definition make_general_query
  (agrs:nonemptylist agreement)(s:subject)(myact:act)(a:asset)(e:environment) : general_query :=
  GeneralQuery agrs s myact a e.

Definition make_single_query
  (agr: agreement)(s:subject)(myact:act)(a:asset)(e:environment) : single_query :=
  SingletonQuery agr s myact a e.

Definition general_q1: general_query := make_general_query (Single AgreeA5_single) Alice Display TheReport e1.
Definition single_q1: single_query := make_single_query AgreeA5_single Alice Display TheReport e1.
End Query.








(********* TODO *********)
Example test_inconsistent: (inconsistent f1 f2) = (6<>7).
(* Proof. unfold inconsistent. simpl. intuition. *) Admitted.



Section Sanity1.

Theorem f1_and_f2_are_inconsistent: inconsistent f1 f2.
Proof. unfold inconsistent. simpl. omega. Qed.

Theorem f1_and___env_of_f2_inconsistent: formula_inconsistent_with_env f1 (SingleEnv f2).
Proof. unfold formula_inconsistent_with_env. apply f1_and_f2_are_inconsistent. Qed.


Theorem two_inconsistent_formulas_imply_env_inconsistent:
  forall f g, inconsistent f g -> ~env_consistent (ConsEnv f (SingleEnv g)).
Proof. intros. unfold not. intros H'.
inversion H'. intuition. intuition. Qed.


Theorem e2_is_inconsistent: ~env_consistent e2.
Proof.

apply two_inconsistent_formulas_imply_env_inconsistent.
apply f1_and_f2_are_inconsistent. Qed.

Lemma NPeirce : forall (P : Prop), (P -> ~P) -> ~P.
auto.
Qed.

Theorem env_consistent_implies_two_consistent_formulas:
  forall (f g: count_equality),
    env_consistent (ConsEnv f (SingleEnv g))-> ~inconsistent f g.
Proof. intros. inversion H. exact H1. intuition. Qed.

Theorem two_consistent_formulas_imply_env_consistent:
  forall (f g: count_equality),
    ~inconsistent f g -> env_consistent (ConsEnv f (SingleEnv g)).
Proof. intros. apply consis_2. exact H. Qed.

SearchAbout count_equality.

Check count_equality_ind.

Theorem env_inconsistent_implies_two_inconsistent_formulas:
  forall (f g: count_equality),
    ~env_consistent (ConsEnv f (SingleEnv g))-> inconsistent f g.
(** using elim on an hypothesis of the shape ~ P,
    you say to Coq "I know that P holds, so using P -> False,
    I can derive a proof of False" which closes the goal by contradiction.
    That's why each time you elim a ~ P, Coq asks you to provide a proof of P.
**)
Proof.
induction f.
induction g.
unfold inconsistent.
intros.
subst.
generalize (dec_eq_nat n n0).
intro h; elim h.
intro; subst.
elim H.
apply consis_2.
unfold inconsistent.
intro.
assert (s0=s0); auto.
assert (p0=p0); auto.
specialize H0 with (1:=H1) (2:=H2).
elim H0; auto.
auto.
Qed.


Theorem theo1 : forall (s1 s2: subject),
		forall (id1 id2: policyId),
		forall (n1 n2: nat),

  (s1 = s2 /\ id1 = id2 /\ n1 <> n2) ->
  inconsistent (CountEquality s1 id1 n1) (CountEquality s2 id2 n2).

Proof. intros. unfold inconsistent. intros. intuition. Qed.

Fixpoint app_envs (e e' : environment) : environment :=
  match e with
  | SingleEnv f  => ConsEnv f e'
  | ConsEnv f rest_env => ConsEnv f (app_envs rest_env e')
  end.

Definition count_equality_equal (f1 f2:count_equality) : Prop :=
  match f1 with (CountEquality s1 id1 n1) =>
     match f2 with (CountEquality s2 id2 n2) =>
       s1 = s2 -> id1 = id2 -> n1 = n2
     end
   end.


Theorem count_equality_equal_refl: forall (a : count_equality), count_equality_equal a a.
Proof. intros. destruct a. simpl. intuition. Qed.



Fixpoint mem_countform_in_env (a:count_equality)(e : environment) : Prop :=
 match e with
  | SingleEnv f  => count_equality_equal f a
  | ConsEnv f rest_env => (count_equality_equal f a) \/
			  (mem_countform_in_env a rest_env)
  end.

SearchAbout env_consistent.


Theorem theo4_1: forall (c: count_equality), mem_countform_in_env c (SingleEnv c).
Proof. induction c. unfold mem_countform_in_env. apply count_equality_equal_refl. Qed.


Axiom e_is_consistent: forall (e:environment), env_consistent e.


Theorem PP1: forall (P Q:Prop), (P->True->True->Q) -> (P->Q).
Proof. intros. apply H. exact H0. auto. auto. Qed.


Theorem PP2: forall (P Q:Prop), (P->Q) -> (P->True->True->Q).
Proof. intros. apply H. exact H0. Qed.
(**
If p -> q, we know two things:
modus ponens says that if p is true, then q must be true.
Modus tollens (MT) says that if q is false, then p must be false.
**)

Theorem ModesT: forall (P Q: Prop), ~Q /\ (P -> Q) -> ~P.
Proof.
intro P.
intro Q.
intro HNQPQ.
destruct HNQPQ as [HNQ HPQ].
intro HP.
(**
The tactic generalize takes as input a term t (for instance,
a proof of some proposition) and then changes the conclusion
from G to T -> G,
where T is the type of t (for instance, the proposition proved by the proof t).

Here 'generalize (HPQ HP)' applies HPQ to HP resulting in Q. then generlize changes the
goal from False to Q -> False.
**)
generalize (HPQ HP).
intro HQ.
(* Notice that we have both Q and ~Q which is a contradiction *)
contradiction.
Qed.


Hypothesis Q: Charlie <> Alice.
Hypothesis T: Charlie <> Bob.

End Sanity1.







Definition get_Sq_Agreement(sq:single_query): agreement :=
  match sq with
    | SingletonQuery agr s myact a e => agr
  end.
Definition get_Sq_Subject(sq:single_query): subject :=
  match sq with
    | SingletonQuery agr s myact a e => s
  end.
Definition get_Sq_Action(sq:single_query): act :=
  match sq with
    | SingletonQuery agr s myact a e => myact
  end.
Definition get_Sq_Asset(sq:single_query): asset :=
  match sq with
    | SingletonQuery agr s myact a e => a
  end.
Definition get_Sq_Env(sq:single_query): environment :=
  match sq with
    | SingletonQuery agr s myact a e => e
  end.


Section ZZZ.

Lemma notTransImpliesUnregulated:
			       forall (s:subject) (p:prin)(t:Prop), not (trans_prin s p) ->
				~ (trans_prin s p /\ t).
Proof.
intros. unfold not. intros. destruct H0. contradiction. Qed.


Theorem queryWithNonReleveantAssetIsUnregulated:
  forall (sq:single_query),
     ((get_Sq_Asset sq) <> (get_Asset_From_Agreement (get_Sq_Agreement sq))) 
-> 
  forall (ac:act),
  isPermissionUnregulated (get_Sq_Subject sq) ac (get_Sq_Asset sq)
   (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ac (get_Sq_Subject sq) (get_Sq_Asset sq)).

Proof.
destruct sq as 
  [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.


intros H'.
unfold trans_agreement.
unfold isPermissionUnregulated.
intros ac.
split.


unfold unregulatedResult.

destruct ps as [prim_policySet]. simpl.

destruct (pierce_eq_nat_dec asset_from_query asset_from_agreement).
contradiction.

unfold makeResult. simpl. auto.

destruct ps as [prim_policySet]. simpl.
split.
destruct (pierce_eq_nat_dec asset_from_query asset_from_agreement).
contradiction.
unfold permittedResult.
simpl.
unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.


destruct (pierce_eq_nat_dec asset_from_query asset_from_agreement).
contradiction.

unfold notPermittedResult.
simpl.
unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.
Qed.







(*** July 1st, 2015: It should now be possible to proof the one below ****)


Section preRequisiteFromPS.

Definition get_preRequisite_From_primPolicy (p:primPolicy) : 
                  preRequisite :=
  match p with 
    | PrimitivePolicy prq pid action => prq
  end.

(*
Fixpoint get_preRequisite_From_primPolicies 
  (l:nonemptylist primPolicy){struct l}  : preRequisite :=
  
         match l with
           | Single pp => get_preRequisite_From_primPolicy pp
	   | NewList pp rest => 
               (app_nonempty
                         (Single (get_preRequisite_From_primPolicy pp)) 
                         (Single (get_preRequisite_From_primPolicies rest)))
         end.

Definition get_preRequisite_From_policy (p:policy): preRequisite :=

  match p with
    (*| PP pp => get_preRequisite_From_primPolicy pp *)           
    | Policy ppolicies => 
        get_preRequisite_From_primPolicies ppolicies
  end.
*)
Definition get_ID_From_policy (p:policy): nonemptylist policyId :=

let process_single_pp := 
  (fix process_single_pp (pp: primPolicy) : nonemptylist policyId :=
  match pp with
    | PrimitivePolicy prq' policyId action => Single policyId      
  end) in 
let trans_pp_list := 
  (fix trans_pp_list (pp_list:nonemptylist primPolicy){struct pp_list}:=
		  match pp_list with
		    | Single pp1 => process_single_pp pp1
		    | NewList pp pp_list' => app_nonempty
			(process_single_pp pp) 
			(trans_pp_list pp_list')
		  end) in

  match p with
  | Policy pp_list => trans_pp_list pp_list
  end.

Definition getActionFromPolicy (p: policy) : nonemptylist act :=

let process_single_pp := 
  (fix process_single_pp (pp: primPolicy) : nonemptylist act :=
  match pp with
    | PrimitivePolicy prq' policyId action => Single action        
  end) in 
let trans_pp_list := 
  (fix trans_pp_list (pp_list:nonemptylist primPolicy){struct pp_list}:=
		  match pp_list with
		    | Single pp1 => process_single_pp pp1
		    | NewList pp pp_list' => app_nonempty
			(process_single_pp pp) 
			(trans_pp_list pp_list')
		  end) in

  match p with
  | Policy pp_list => trans_pp_list pp_list
  end.

Eval compute in (getActionFromPolicy two_pols).
Eval compute in (get_ID_From_policy two_pols).

Definition get_preRequisite_From_primPolicySet (pps:primPolicySet) : 
                  preRequisite :=
  match pps with 
    | PIPS pips => 
        match pips with 
          | PrimitiveInclusivePolicySet prq pol => prq  
        end
    | PEPS peps => 
        match peps with 
          | PrimitiveExclusivePolicySet prq pol => prq
        end
  end.
(*
Fixpoint get_preRequisite_From_primPolicySets 
 (l:nonemptylist primPolicySet){struct l}  : preRequisite :=
  
  match l with
    | Single pps => get_preRequisite_From_primPolicySet pps
    | NewList pps rest => 
        AndPrqs (app_nonempty
                   (Single (get_preRequisite_From_primPolicySet pps))
                   (Single (get_preRequisite_From_primPolicySets rest)))
  end.
  
Definition get_preRequisite_From_policySet (ps:policySet): 
   preRequisite :=

  match ps with
    | PPS pps => get_preRequisite_From_primPolicySet pps 
  end.

Definition get_policy_preRequisite_From_primPolicySet (pps:primPolicySet) : 
                  preRequisite :=
  match pps with 
    | PIPS pips => 
        match pips with 
          | PrimitiveInclusivePolicySet _ pol =>
              get_preRequisite_From_policy pol
        end
    | PEPS peps => 
        match peps with 
          | PrimitiveExclusivePolicySet _ pol => 
              get_preRequisite_From_policy pol
        end
  end.


Definition get_policy_preRequisite_From_policySet (ps:policySet): 
   preRequisite :=

  match ps with
    | PPS pps => get_policy_preRequisite_From_primPolicySet pps 
  end.


Definition get_IDs_From_primPolicySet (pps:primPolicySet) : nonemptylist policyId :=
                
  match pps with 
    | PIPS pips => 
        match pips with | PrimitiveInclusivePolicySet _ pol => 
          getId pol
        end
    | PEPS peps => 
        match peps with | PrimitiveExclusivePolicySet _ pol => 
          getId pol
        end
  end.

Fixpoint get_IDs_From_primPolicySets 
 (l:nonemptylist primPolicySet){struct l}  : nonemptylist policyId :=
  
  match l with
    | Single pps => get_IDs_From_primPolicySet pps
    | NewList pps rest => app_nonempty 
                            (get_IDs_From_primPolicySet pps)
                            (get_IDs_From_primPolicySets rest)
  end.

Definition get_IDs_From_policySet (ps:policySet) : nonemptylist policyId :=
  match ps with
    | PPS pps => get_IDs_From_primPolicySet pps 
  end.
    
Definition get_policy_From_primPolicySet (pps:primPolicySet) : 
                  policy :=
  match pps with 
    | PIPS pips => 
        match pips with 
          | PrimitiveInclusivePolicySet _ pol => pol
        end
    | PEPS peps => 
        match peps with 
          | PrimitiveExclusivePolicySet _ pol => pol
        end
  end.


Definition get_policy_From_policySet (ps:policySet): policy :=

  match ps with
    | PPS pps => get_policy_From_primPolicySet pps 
  end.
*)
End preRequisiteFromPS.


(****
If [P n] is some proposition involving a natural number n, and
we want to show that P holds for _all_ numbers n, we can
        reason like this:
          - show that [P O] holds
          - show that, if [P n'] holds, then so does [P (S n')]
          - conclude that [P n] holds for all n.
****)
Theorem ind_isResultInQueryResult: 
   (forall (s:subject)(action_from_query:act)(a:asset)(x : result), 
          (isResultInQueryResult (Result Permitted s action_from_query a) [x]) \/
          (isResultInQueryResult (Result Unregulated s action_from_query a) [x]))
             
        -> (forall (s:subject)(action_from_query:act)(a:asset)(x : result)
		  (n : nonemptylist result), 
              ((isResultInQueryResult (Result Permitted s action_from_query a) n) \/ 
                 (isResultInQueryResult (Result Unregulated s action_from_query a) n)) -> 
              ((isResultInQueryResult (Result Permitted s action_from_query a) (x, n)) \/ 
                 (isResultInQueryResult (Result Unregulated s action_from_query a) (x, n))))
                
        -> forall (s:subject)(action_from_query:act)(a:asset)(n : nonemptylist result), 
               ((isResultInQueryResult (Result Permitted s action_from_query a) n) \/ 
                 (isResultInQueryResult (Result Unregulated s action_from_query a) n)).
Proof.
intros hSingle hNewList s action_from_query a n.
induction n.
specialize hSingle with s action_from_query a x.
exact hSingle.

apply hNewList.
exact IHn.
Qed.


Theorem ind_trans_policy_positive: 

       (forall (s:subject)(action_from_query:act)(a:asset)(x : result), 
          (isPermissionGranted s action_from_query a [x]) \/
          (isPermissionUnregulated s action_from_query a [x]))
             
        -> (forall (s:subject)(action_from_query:act)(a:asset)(x : result)
		  (n : nonemptylist result), 
              ((isPermissionGranted s action_from_query a n) \/ (isPermissionUnregulated s action_from_query a n)) -> 
			     ((isPermissionGranted s action_from_query a (x, n)) \/ (isPermissionUnregulated s action_from_query a (x, n))))
                
        -> forall (s:subject)(action_from_query:act)(a:asset)(n : nonemptylist result), 
              (((isPermissionGranted s action_from_query a n) \/ (isPermissionUnregulated s action_from_query a n))).
Proof.
intros hSingle hNewList s action_from_query a n.
induction n.
specialize hSingle with s action_from_query a x.
exact hSingle.

apply hNewList.
exact IHn.
Qed.

Fixpoint isResultInQueryResults (res:result)(results: nonemptylist result): Prop :=
  match results with
    | Single res' => res = res'
    | NewList res' rest => res = res' \/ (isResultInQueryResults res rest)
  end.

Theorem eq_answer_dec : forall (ans ans' : answer), {ans = ans'} + {ans <> ans'}.
Proof.
  intros ans.
  induction ans.

    intros ans'.
    destruct ans'.
    left. reflexivity.
    right. intros contra. inversion contra.
    right. intros contra. inversion contra.

    intros ans'.
    destruct ans'.
    right. intros contra. inversion contra.
    left. reflexivity.
    right. intros contra. inversion contra.


    intros ans'.
    destruct ans'.
    right. intros contra. inversion contra.
    right. intros contra. inversion contra.
    left. reflexivity.

Defined.

Theorem eq_result_dec : forall (n m : result), {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [ans subj ac ass].
    intros m.
    destruct m as [ans' subj' ac' ass'].
    destruct (eq_answer_dec ans ans').
    destruct (pierce_eq_nat_dec subj subj').
    destruct (pierce_eq_nat_dec ac ac').
    destruct (pierce_eq_nat_dec ass ass').
    subst.
    left. reflexivity.
    right. intros contra. inversion contra. contradiction.
    right. intros contra. inversion contra. contradiction.
    right. intros contra. inversion contra. contradiction.
    right. intros contra. inversion contra. contradiction.
Defined.


Theorem resultInQueryResults_dec :
    forall (res:result)(results: nonemptylist result), 
 {isResultInQueryResults res results} + {~isResultInQueryResults res results}.
Proof.
induction results as [| res' results IHresults].
simpl.
apply eq_result_dec.
destruct (eq_result_dec res' res); simpl; auto.
destruct IHresults; simpl; auto.
right; unfold not; intros [Hc1| Hc2]; auto.
Defined.


Theorem trans_policy_positive_dec:
  forall 
(e:environment)(s:subject)(p:policy)(prin_u:prin)(a:asset)
  (action_from_query: act),
  
  
  (isResultInQueryResult 
    (Result Permitted s action_from_query a)
    (trans_policy_positive e s p prin_u a action_from_query)) 
\/

  (isResultInQueryResult 
    (Result Unregulated s action_from_query a)
    (trans_policy_positive e s p prin_u a action_from_query)).

Proof.

destruct p as [primPolicies]. 
intros prin_u a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
simpl.
destruct (trans_preRequisite_dec e s prq' [pid] prin_u).
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
simpl; unfold makeResult; left; reflexivity. 
simpl; unfold makeResult; right; reflexivity.
simpl; unfold makeResult; right; reflexivity.


destruct pp' as [prq' pid actionFromPrimPolicy].
simpl. 
destruct (trans_preRequisite_dec e s prq' [pid] prin_u).
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).

simpl; left; left; unfold makeResult; auto.

simpl; right; left; unfold makeResult; auto.

simpl; right; left; unfold makeResult; auto.

Defined.

Theorem trans_policy_negative_dec:
  forall 
(e:environment)(s:subject)(p:policy)(a:asset)
  (action_from_query: act),
  
  (isResultInQueryResult 
    (Result NotPermitted s action_from_query a)
    (trans_policy_negative e s p a action_from_query)) 
\/
  (isResultInQueryResult 
    (Result Unregulated s action_from_query a)
    (trans_policy_negative e s p a action_from_query)).

Proof.
destruct p as [primPolicies]. 
intros a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
simpl.
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
simpl; unfold makeResult; left; reflexivity. 
simpl; unfold makeResult; right; reflexivity.


destruct pp' as [prq' pid actionFromPrimPolicy].
simpl. 
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).

simpl; left; left; unfold makeResult; auto.

simpl; right; left; unfold makeResult; auto.


Defined.

Theorem trans_policy_unregulated_dec:
  forall 
(e:environment)(s:subject)(p:policy)(a:asset)
  (action_from_query: act),
  
  (isResultInQueryResult 
    (Result Unregulated s action_from_query a)
    (trans_policy_unregulated e s p a action_from_query)).

Proof.
destruct p as [primPolicies]. 
intros a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
simpl.
simpl; unfold makeResult. auto. 
destruct pp' as [prq' pid actionFromPrimPolicy].
simpl; left; unfold makeResult; auto.
Defined.

Theorem trans_policy_PIPS_dec:
  forall
  (e:environment)(prq: preRequisite)(p:policy)(subject_from_query:subject)
  (prin_u:prin)(a:asset)(action_from_query:act),

 (isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query a)
    (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)) 
\/

  (isResultInQueryResult 
    (Result Unregulated subject_from_query action_from_query a)
    (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)).
Proof.

destruct p as [primPolicies]. 
intros subject_from_query prin_u a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
unfold trans_policy_PIPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq
        (getId (Policy [PrimitivePolicy prq' pid actionFromPrimPolicy]))
        prin_u).
apply trans_policy_positive_dec.
right; apply trans_policy_unregulated_dec.
right; apply trans_policy_unregulated_dec.


destruct pp' as [prq' pid actionFromPrimPolicy].
unfold trans_policy_PIPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq
        (getId
           (Policy (PrimitivePolicy prq' pid actionFromPrimPolicy, rest_pp)))
        prin_u).
apply trans_policy_positive_dec.
right; apply trans_policy_unregulated_dec.
right; apply trans_policy_unregulated_dec.
Defined.

Theorem trans_policy_PEPS_dec:
  forall
  (e:environment)(prq: preRequisite)(p:policy)(subject_from_query:subject)
  (prin_u:prin)(a:asset)(action_from_query:act),

 (isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query a)
    (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query)) 
\/

 (isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query a)
    (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query))
\/

 (isResultInQueryResult 
    (Result Unregulated subject_from_query action_from_query a)
    (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query)).

Proof.

destruct p as [primPolicies]. 
intros subject_from_query prin_u a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
unfold trans_policy_PEPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq
        (getId (Policy [PrimitivePolicy prq' pid actionFromPrimPolicy]))
        prin_u).
simpl.
destruct (trans_preRequisite_dec e subject_from_query prq' [pid] prin_u).
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
left; simpl; unfold makeResult; auto.

right; right; simpl; unfold makeResult; auto.
right; right; simpl; unfold makeResult; auto.
right; right; simpl; unfold makeResult; auto.
simpl.
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
right; left; simpl; unfold makeResult; auto.
right; right; simpl; unfold makeResult; auto.


unfold trans_policy_PEPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq
        (getId (Policy (pp', rest_pp))) prin_u).
destruct (trans_policy_positive_dec e subject_from_query (Policy (pp', rest_pp)) prin_u
     a action_from_query).
left. assumption.
right. right. assumption.

right; right. apply trans_policy_unregulated_dec.
right. simpl. 
destruct pp' as [prq' pid actionFromPrimPolicy].
simpl. 
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
simpl.
left. left. unfold makeResult; auto.
right. simpl. left. unfold makeResult; auto.
Defined.

Theorem or_commutes : forall (P Q R : Prop),
  P \/ Q \/ R -> Q \/ P \/ R.
Proof.
intros P Q R. intros H. inversion H as [HP | HQR].
right. left. assumption. destruct HQR as [HQ | HR]. left. assumption.
right. right. assumption. Qed.



Theorem trans_ps_dec:
  forall
  (e:environment)(action_from_query:act)(subject_from_query:subject)(asset_from_query:asset)
  (ps:policySet)
  (prin_u:prin)(a:asset),

 (isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)) 
\/

 (isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)) 
\/

 (isResultInQueryResult 
    (Result Unregulated subject_from_query action_from_query asset_from_query)
    (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)).

Proof.
destruct ps as [pps]. 
intros prin_u a.
induction pps as [pips | peps].

simpl. 
destruct (pierce_eq_nat_dec asset_from_query a).
destruct pips as [prq p].
apply or_commutes.
right. subst. apply trans_policy_PIPS_dec.
right. right. simpl. unfold makeResult; auto.


simpl. 
destruct (pierce_eq_nat_dec asset_from_query a).
destruct peps as [prq p].
subst. apply trans_policy_PEPS_dec.
right. right. simpl. unfold makeResult; auto.
Defined.


Theorem trans_agreement_dec:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),


 (isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
\/

 (isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))
\/

 (isResultInQueryResult 
    (Result Unregulated subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)).

Proof.

 
intros e ag action_from_query subject_from_query asset_from_query. 
unfold trans_agreement.


destruct ag as [prin_u asset_from_agreement ps].
apply trans_ps_dec.
Defined.

Theorem PermittedInQueryResults_dec :
    forall (s:subject)(ac:act)(ass:asset)(res: result), 
 (res = (Result Permitted s ac ass)) -> 
   (res <> (Result NotPermitted s ac ass)) /\
   (res <> (Result Unregulated s ac ass)).
Proof.
intros s ac ass res.
intros H.
split.
subst; apply AnswersNotEqual; intros contra; inversion contra. 
subst; apply AnswersNotEqual; intros contra; inversion contra.
Defined.

Theorem NotPermittedInQueryResults_dec :
    forall (s:subject)(ac:act)(ass:asset)(res: result), 
 (res = (Result NotPermitted s ac ass)) -> 
   (res <> (Result Permitted s ac ass)) /\
   (res <> (Result Unregulated s ac ass)).
Proof.
intros s ac ass res.
intros H.
split.
subst; apply AnswersNotEqual; intros contra; inversion contra. 
subst; apply AnswersNotEqual; intros contra; inversion contra.
Defined.

Theorem UnregulatedInQueryResults_dec :
    forall (s:subject)(ac:act)(ass:asset)(res: result), 
 (res = (Result Unregulated s ac ass)) -> 
   (res <> (Result Permitted s ac ass)) /\
   (res <> (Result NotPermitted s ac ass)).
Proof.
intros s ac ass res.
intros H.
split.
subst; apply AnswersNotEqual; intros contra; inversion contra. 
subst; apply AnswersNotEqual; intros contra; inversion contra.
Defined.

Theorem trans_policy_positive_dec_not:
  forall 
(e:environment)(s:subject)(p:policy)(prin_u:prin)(a:asset)
  (action_from_query: act),
 
  ~(isResultInQueryResult 
    (Result NotPermitted s action_from_query a)
    (trans_policy_positive e s p prin_u a action_from_query)).
Proof.

destruct p as [primPolicies]. 
intros prin_u a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
simpl.
destruct (trans_preRequisite_dec e s prq' [pid] prin_u).
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl.
destruct pp' as [prq' pid actionFromPrimPolicy]. simpl.
destruct (trans_preRequisite_dec e s prq' [pid] prin_u).
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).

simpl. intros contra. unfold makeResult in contra. destruct contra as [H1 | H2]. 
apply AnswersNotEqual in H1. auto.
intros contra. inversion contra. simpl in IHrest_pp. contradiction.

simpl. intros contra. unfold makeResult in contra. destruct contra as [H1 | H2]. 
apply AnswersNotEqual in H1. auto.
intros contra. inversion contra. simpl in IHrest_pp. contradiction.
simpl in IHrest_pp. 
simpl. intros contra. unfold makeResult in contra. destruct contra as [H1 | H2]. 
apply AnswersNotEqual in H1. auto.
intros contra. inversion contra. contradiction.

Defined.

Theorem trans_policy_negative_dec_not:
  forall 
(e:environment)(s:subject)(p:policy)(a:asset)
  (action_from_query: act),
 
  ~(isResultInQueryResult 
    (Result Permitted s action_from_query a)
    (trans_policy_negative e s p a action_from_query)).
Proof.

destruct p as [primPolicies]. 
intros a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
simpl.
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.

destruct pp' as [prq' pid actionFromPrimPolicy]. simpl.
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).

simpl. intros contra. unfold makeResult in contra. destruct contra as [H1 | H2]. 
apply AnswersNotEqual in H1. auto.
intros contra. inversion contra. simpl in IHrest_pp. contradiction.

simpl. intros contra. unfold makeResult in contra. destruct contra as [H1 | H2]. 
apply AnswersNotEqual in H1. auto.
intros contra. inversion contra. simpl in IHrest_pp. contradiction.

Defined.

Theorem trans_policy_unregulated_dec_not:
  forall 
(e:environment)(s:subject)(p:policy)(a:asset)
  (action_from_query: act),
 
  ~(isResultInQueryResult 
    (Result Permitted s action_from_query a)
    (trans_policy_unregulated e s p a action_from_query)) /\
  
  ~(isResultInQueryResult 
    (Result NotPermitted s action_from_query a)
    (trans_policy_unregulated e s p a action_from_query)).
Proof.

destruct p as [primPolicies]. 
intros a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
simpl. unfold makeResult. split.
apply AnswersNotEqual. intros contra. inversion contra.
apply AnswersNotEqual. intros contra. inversion contra.
simpl.
destruct pp' as [prq' pid actionFromPrimPolicy]. 
simpl in IHrest_pp. 
simpl. split.

intros contra. unfold makeResult in contra. destruct contra as [H1 | H2]. 
apply AnswersNotEqual in H1. auto.
intros contra. inversion contra. destruct IHrest_pp as [H H']. contradiction.

intros contra. unfold makeResult in contra. destruct contra as [H1 | H2]. 
apply AnswersNotEqual in H1. auto.
intros contra. inversion contra. destruct IHrest_pp as [H H']. contradiction.
Defined.



Theorem trans_policy_PIPS_dec_not:
  forall
  (e:environment)(prq: preRequisite)(p:policy)(subject_from_query:subject)
  (prin_u:prin)(a:asset)(action_from_query:act),

 ~(isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query a)
    (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)).
Proof.
destruct p as [primPolicies]. 
intros subject_from_query prin_u a action_from_query.
induction primPolicies as [pp | pp' rest_pp].

destruct pp as [prq' pid actionFromPrimPolicy].
unfold trans_policy_PIPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq
        (getId (Policy [PrimitivePolicy prq' pid actionFromPrimPolicy]))
        prin_u).
simpl.
destruct (trans_preRequisite_dec e subject_from_query prq' [pid] prin_u).
destruct (pierce_eq_nat_dec action_from_query actionFromPrimPolicy).
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.

unfold trans_policy_PIPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq
        (getId (Policy (pp', rest_pp))) prin_u).
apply trans_policy_positive_dec_not.
apply trans_policy_unregulated_dec_not.
apply trans_policy_unregulated_dec_not.

Defined.

Section Perm_implies_not_notPerm.

Theorem trans_policy_PIPS_perm_implies_not_notPerm_dec:
  forall
  (e:environment)(prq: preRequisite)(p:policy)(subject_from_query:subject)
  (prin_u:prin)(a:asset)(action_from_query:act),

(isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query a)
    (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)) ->


 ~(isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query a)
    (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)).
Proof.
intros e prq p subject_from_query prin_u a action_from_query.
intros H.
apply trans_policy_PIPS_dec_not.
Defined.


Theorem trans_policy_PEPS_perm_implies_not_notPerm_dec:
  forall
  (e:environment)(prq: preRequisite)(p:policy)(subject_from_query:subject)
  (prin_u:prin)(a:asset)(action_from_query:act),

    (isResultInQueryResult 
      (Result Permitted subject_from_query action_from_query a)
        (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query)) ->

   ~(isResultInQueryResult 
      (Result NotPermitted subject_from_query action_from_query a)
       (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query)).
Proof.

intros e prq p subject_from_query prin_u a action_from_query.

unfold trans_policy_PEPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq (getId p) prin_u).
intros H.
apply trans_policy_positive_dec_not.
intros H.
specialize trans_policy_unregulated_dec_not with e subject_from_query p a action_from_query.
intros H'. destruct H' as [H1 H2]. exact H2.
intros H.
specialize trans_policy_negative_dec_not with 
  e subject_from_query p a action_from_query.
intros H'. contradiction.

Defined.



Theorem trans_ps_perm_implies_not_notPerm_dec:
  forall
  (e:environment)(action_from_query:act)(subject_from_query:subject)
  (asset_from_query:asset)(ps:policySet)(prin_u:prin)(a:asset),


    (isResultInQueryResult 
      (Result Permitted subject_from_query action_from_query asset_from_query)
        (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)) ->

   ~(isResultInQueryResult 
      (Result NotPermitted subject_from_query action_from_query asset_from_query)
       (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)).
Proof.
destruct ps as [prim_policySet]. simpl.
intros prin_u a.
destruct prim_policySet as [proof_of_primInclusivePolicySet | proof_of_primExclusivePolicySet].  

destruct proof_of_primInclusivePolicySet as [prq_from_ps pol]. 
destruct (pierce_eq_nat_dec asset_from_query a).
subst. apply trans_policy_PIPS_perm_implies_not_notPerm_dec. simpl.
unfold makeResult. intros H. intros contra. apply AnswersNotEqual in contra. auto.
intros contra'. inversion contra'.

destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. 
destruct (pierce_eq_nat_dec asset_from_query a).
subst. apply trans_policy_PEPS_perm_implies_not_notPerm_dec. simpl.
unfold makeResult. intros H. intros contra. apply AnswersNotEqual in contra. auto.
intros contra'. inversion contra'.
Defined.

Theorem trans_agreement_perm_implies_not_notPerm_dec:
  forall
    (e:environment)(ag:agreement)(action_from_query:act)
    (subject_from_query:subject)(asset_from_query:asset),

    (isResultInQueryResult 
      (Result Permitted subject_from_query action_from_query asset_from_query)
        (trans_agreement e ag action_from_query subject_from_query asset_from_query)) ->

   ~(isResultInQueryResult 
      (Result NotPermitted subject_from_query action_from_query asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query asset_from_query)).
Proof.
destruct ag as [prin_from_agreement asset_from_agreement ps]. simpl.
intros action_from_query subject_from_query asset_from_query.
apply trans_ps_perm_implies_not_notPerm_dec.
Defined.

End Perm_implies_not_notPerm.

Section NotPerm_implies_not_Perm.

Theorem trans_policy_PIPS_NotPerm_implies_not_Perm_dec:
  forall
  (e:environment)(prq: preRequisite)(p:policy)(subject_from_query:subject)
  (prin_u:prin)(a:asset)(action_from_query:act),

(isResultInQueryResult 
   (Result NotPermitted subject_from_query action_from_query a)
    (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)) ->


 ~(isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query a)
    (trans_policy_PIPS e prq p subject_from_query prin_u a action_from_query)).
Proof.
intros e prq p subject_from_query prin_u a action_from_query.
unfold trans_policy_PIPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq (getId p) prin_u).
intros H'.
specialize trans_policy_positive_dec_not with e subject_from_query p prin_u a action_from_query.
intros H. contradiction.

intros H'.
specialize trans_policy_unregulated_dec_not with e subject_from_query p a action_from_query.
intros H. destruct H as [H1 H2]. contradiction.

intros H'.
specialize trans_policy_unregulated_dec_not with e subject_from_query p a action_from_query.
intros H. destruct H as [H1 H2]. contradiction.
Defined.


Theorem trans_policy_PEPS_NotPerm_implies_not_Perm_dec:
  forall
  (e:environment)(prq: preRequisite)(p:policy)(subject_from_query:subject)
  (prin_u:prin)(a:asset)(action_from_query:act),

    (isResultInQueryResult 
      (Result NotPermitted subject_from_query action_from_query a)
        (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query)) ->

   ~(isResultInQueryResult 
      (Result Permitted subject_from_query action_from_query a)
       (trans_policy_PEPS e prq p subject_from_query prin_u a action_from_query)).
Proof.

intros e prq p subject_from_query prin_u a action_from_query.

unfold trans_policy_PEPS.
destruct (trans_prin_dec subject_from_query prin_u).
destruct (trans_preRequisite_dec e subject_from_query prq (getId p) prin_u).

intros H'.
specialize trans_policy_positive_dec_not with e subject_from_query p prin_u a action_from_query.
intros H. contradiction.

intros H'.
specialize trans_policy_unregulated_dec_not with e subject_from_query p a action_from_query.
intros H. destruct H as [H1 H2]. contradiction.

intros H'.
apply trans_policy_negative_dec_not.
Defined.

Theorem trans_ps_NotPerm_implies_not_Perm_dec:
  forall
  (e:environment)(action_from_query:act)(subject_from_query:subject)
  (asset_from_query:asset)(ps:policySet)(prin_u:prin)(a:asset),


    (isResultInQueryResult 
      (Result NotPermitted subject_from_query action_from_query asset_from_query)
        (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)) ->

   ~(isResultInQueryResult 
      (Result Permitted subject_from_query action_from_query asset_from_query)
       (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)).
Proof.
destruct ps as [prim_policySet]. simpl.
intros prin_u a.
destruct prim_policySet as [proof_of_primInclusivePolicySet | proof_of_primExclusivePolicySet].  

destruct proof_of_primInclusivePolicySet as [prq_from_ps pol]. 
destruct (pierce_eq_nat_dec asset_from_query a).

intros H'.
specialize trans_policy_PIPS_dec_not with e prq_from_ps pol subject_from_query
     prin_u a action_from_query.
intros H. subst. contradiction.

simpl. unfold makeResult. intros contra. apply AnswersNotEqual. intros contra'. 
inversion contra'. 

destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. 
destruct (pierce_eq_nat_dec asset_from_query a).
subst. apply trans_policy_PEPS_NotPerm_implies_not_Perm_dec.

simpl. unfold makeResult. intros contra. apply AnswersNotEqual. intros contra'. 
inversion contra'. 
Defined.

Theorem trans_agreement_NotPerm_implies_not_Perm_dec:
  forall
    (e:environment)(ag:agreement)(action_from_query:act)
    (subject_from_query:subject)(asset_from_query:asset),

    (isResultInQueryResult 
      (Result NotPermitted subject_from_query action_from_query asset_from_query)
        (trans_agreement e ag action_from_query subject_from_query asset_from_query)) ->

   ~(isResultInQueryResult 
      (Result Permitted subject_from_query action_from_query asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query asset_from_query)).
Proof.
destruct ag as [prin_from_agreement asset_from_agreement ps]. simpl.
intros action_from_query subject_from_query asset_from_query.
apply trans_ps_NotPerm_implies_not_Perm_dec.
Defined.

End NotPerm_implies_not_Perm.

(**** set is nicer than pose
set (asset_from_agreement := (get_Asset_From_Agreement agr)).
set (prin_u := (get_Prin_From_Agreement agr)).
****)

Theorem trans_agreement_not_NotPerm_and_not_Perm_implies_Unregulated_dec:
  forall
    (e:environment)(ag:agreement)(action_from_query:act)
    (subject_from_query:subject)(asset_from_query:asset),

    (~(isResultInQueryResult 
      (Result Permitted subject_from_query action_from_query asset_from_query)
        (trans_agreement e ag action_from_query subject_from_query asset_from_query)) /\

    ~(isResultInQueryResult 
      (Result NotPermitted subject_from_query action_from_query asset_from_query)
        (trans_agreement e ag action_from_query subject_from_query asset_from_query))) ->

   (isResultInQueryResult 
      (Result Unregulated subject_from_query action_from_query asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query asset_from_query)).
Proof.
destruct ag as [prin_from_agreement asset_from_agreement ps]. simpl.
intros action_from_query subject_from_query asset_from_query.
destruct ps as [prim_policySet]. simpl.
destruct (pierce_eq_nat_dec asset_from_query asset_from_agreement).
destruct prim_policySet as [proof_of_primInclusivePolicySet | proof_of_primExclusivePolicySet]. 

destruct proof_of_primInclusivePolicySet as [prq_from_ps pol]. 
intros H. destruct H as [H1 H2].
specialize trans_policy_PIPS_dec with 
  e prq_from_ps pol subject_from_query prin_from_agreement asset_from_query action_from_query.
intros HA. destruct HA as [HA1 | HA2]. 
  subst. contradiction. 
  subst. assumption.

destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. 
intros H. destruct H as [H1 H2].
specialize trans_policy_PEPS_dec with 
  e prq_from_ps pol subject_from_query prin_from_agreement asset_from_query action_from_query.
intros HA. destruct HA as [HA1 | HA2]. 
  subst. contradiction. 
  subst. destruct HA2 as [HA21 | HA22]. 
    contradiction. 
    assumption.
intros H. simpl. unfold makeResult. auto.
Defined. 

Theorem trans_agreement_not_Perm_and_NotPerm_at_once:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),


 ~((isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
/\

 (isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))).
Proof.
destruct ag as [prin_from_agreement asset_from_agreement ps]. simpl.
destruct ps as [prim_policySet]. simpl.
destruct prim_policySet as [proof_of_primInclusivePolicySet | proof_of_primExclusivePolicySet]. simpl. 

destruct proof_of_primInclusivePolicySet as [prq_from_ps pol]. simpl.
intros action_from_query subject_from_query asset_from_query.
destruct (pierce_eq_nat_dec asset_from_query asset_from_agreement).
intros H. destruct H as [H1 H2].
specialize trans_policy_PIPS_dec_not with e prq_from_ps pol subject_from_query
     prin_from_agreement asset_from_query action_from_query.
intros H'. subst. contradiction.
simpl.
intros H. destruct H as [H1 H2]. apply AnswersNotEqual in H1. auto.
intros contra. inversion contra.

destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. simpl.
intros action_from_query subject_from_query asset_from_query.
destruct (pierce_eq_nat_dec asset_from_query asset_from_agreement).
intros H. destruct H as [H1 H2].
specialize trans_policy_PEPS_perm_implies_not_notPerm_dec with e prq_from_ps pol 
     subject_from_query prin_from_agreement asset_from_query action_from_query.
intros H. subst. apply H in H1. contradiction.

simpl.
unfold makeResult. intros H. destruct H as [H1 H2].
apply AnswersNotEqual in H1. auto.
intros contra'. inversion contra'.
Defined.

Inductive decidable : environment -> agreement -> act -> subject -> asset -> Prop :=

     | Denied : forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset), 

 (isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
  ->
 ~(isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 

  -> decidable e ag action_from_query subject_from_query asset_from_query

     | Granted : forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset), 
 (isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
 ->
 ~(isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
 
 -> decidable e ag action_from_query subject_from_query asset_from_query

     | NonApplicable : forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset), 

  ~(isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
     ->
  ~(isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
  -> decidable e ag action_from_query subject_from_query asset_from_query.

Theorem decidableAgreeCan: decidable eA1 AgreeCan Print Alice TheReport.
Proof.
apply Granted. simpl.
unfold trans_policy_PIPS.
destruct (trans_prin_dec Alice [Alice]).
destruct (trans_preRequisite_dec eA1 Alice (makePreRequisite TruePrq)
        (getId (Policy [PrimitivePolicy (makePreRequisite 
                                          (Constraint (Count 5)))
                            id1 Print]))
        [Alice]).
simpl.
destruct (trans_preRequisite_dec eA1 Alice 
  (makePreRequisite (Constraint (Count 5))) [id1] [Alice]).
simpl. auto.
simpl. unfold makeResult.

simpl in n.
unfold trans_count in n.
omega.
simpl. unfold makeResult.

simpl in n. firstorder.
simpl. unfold makeResult.
simpl in n. firstorder.

simpl.
unfold trans_policy_PIPS.
destruct (trans_prin_dec Alice [Alice]).
destruct (trans_preRequisite_dec eA1 Alice (makePreRequisite TruePrq)
        (getId (Policy [PrimitivePolicy (makePreRequisite (Constraint (Count 5))) id1 Print]))
        [Alice]).
simpl.
destruct (trans_preRequisite_dec eA1 Alice (makePreRequisite (Constraint (Count 5))) [id1] [Alice]).
simpl. unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.

simpl. unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.
simpl. unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.
simpl. unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.
Qed.

Theorem resultInQueryResult_dec :
    forall (res:result)(results: nonemptylist result), 
 {isResultInQueryResult res results} + {~isResultInQueryResult res results}.
Proof.
unfold isResultInQueryResult.

simpl.
induction results as [| res' results IHresults].
simpl.
apply eq_result_dec.
destruct (eq_result_dec res' res); simpl; auto.
destruct IHresults; simpl; auto.
right; unfold not; intros [Hc1| Hc2]; auto.
Defined.


Theorem trans_agreement_dec_sb_Permitted:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),


 {(isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))} +
 {~(isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))}.
Proof.
intros e ag action_from_query subject_from_query asset_from_query.
specialize resultInQueryResult_dec with 
  (res:= (Result Permitted subject_from_query action_from_query asset_from_query)) 
  (results := (trans_agreement e ag action_from_query subject_from_query
      asset_from_query)).
intros H. exact H.
Defined.

Theorem trans_agreement_dec_sb_NotPermitted:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),


 {(isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))} +
 {~(isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))}.
Proof.
intros e ag action_from_query subject_from_query asset_from_query.
specialize resultInQueryResult_dec with 
  (res:= (Result NotPermitted subject_from_query action_from_query asset_from_query)) 
  (results := (trans_agreement e ag action_from_query subject_from_query
      asset_from_query)).
intros H. exact H.
Defined.

Theorem trans_agreement_dec2:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),

 (isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) 
\/

 (isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))
\/

 (~(isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) /\
  ~(isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))).

Proof.
intros e ag action_from_query subject_from_query asset_from_query. 
specialize trans_agreement_dec_sb_Permitted with 
   e ag action_from_query subject_from_query asset_from_query.
intros P. destruct P as [P1|P2].
specialize trans_agreement_dec_sb_NotPermitted with 
   e ag action_from_query subject_from_query asset_from_query.
intros Q. destruct Q as [Q1|Q2].

specialize trans_agreement_not_Perm_and_NotPerm_at_once with
  e ag action_from_query subject_from_query asset_from_query.
intros K. 
assert (isResultInQueryResult
       (Result Permitted subject_from_query action_from_query
          asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query
          asset_from_query) /\
       
       isResultInQueryResult
       (Result NotPermitted subject_from_query action_from_query
          asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query
          asset_from_query)).

split. exact P1. exact Q1. contradiction.
left. exact P1.
specialize trans_agreement_dec_sb_NotPermitted with 
   e ag action_from_query subject_from_query asset_from_query.
intros Q. destruct Q as [Q1|Q2].
right. left. exact Q1.
right. right.
assert ((~
     isResultInQueryResult
       (Result Permitted subject_from_query action_from_query
          asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query
          asset_from_query)) /\ (~
     isResultInQueryResult
       (Result NotPermitted subject_from_query action_from_query
          asset_from_query)
       (trans_agreement e ag action_from_query subject_from_query
          asset_from_query))).
split. exact P2. exact Q2.
exact H.
Defined.


Theorem trans_agreement_decidable:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),
     decidable e ag action_from_query subject_from_query asset_from_query.
Proof.
intros e ag action_from_query subject_from_query asset_from_query.
specialize trans_agreement_dec2 with 
   e ag action_from_query subject_from_query asset_from_query.
intros H. destruct H as [H1 | H2].

apply Granted. assumption.
simpl. intuition.
apply trans_agreement_perm_implies_not_notPerm_dec in H1. contradiction. 

destruct H2 as [H21 | H22].
apply Denied. assumption.
simpl. intuition.
apply trans_agreement_NotPerm_implies_not_Perm_dec in H21. contradiction. 

apply NonApplicable. 
destruct H22 as [H221 H222].
exact H221.
destruct H22 as [H221 H222].
exact H222.
Defined.



End ZZZ.


Section ReasonablityProperties.

Theorem trans_agreement_deterministic:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset)(d: answer),

   (isResultInQueryResult 
    (Result d subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) ->

   (isResultInQueryResult 
    (Result d subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)).
Proof.
auto.
Defined.


Theorem trans_agreement_deterministic1:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),

  forall (d': answer),
   ((isResultInQueryResult 
    (Result Permitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) /\
   (isResultInQueryResult 
    (Result d' subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))) 
 
 -> (d' <> NotPermitted).

Proof.
intros e ag action_from_query subject_from_query asset_from_query d'.
intros H.
destruct H as [H1 H2].
intros H'. subst. 
apply trans_agreement_not_Perm_and_NotPerm_at_once with 
   e ag action_from_query subject_from_query asset_from_query.
split.
exact H1.
exact H2.
Qed.

Theorem trans_agreement_deterministic2:
  forall
  (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset),

  forall (d': answer),
   ((isResultInQueryResult 
    (Result NotPermitted subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query)) /\
   (isResultInQueryResult 
    (Result d' subject_from_query action_from_query asset_from_query)
    (trans_agreement e ag action_from_query subject_from_query asset_from_query))) 
 
 -> (d' <> Permitted).

Proof.
intros e ag action_from_query subject_from_query asset_from_query d'.
intros H.
destruct H as [H1 H2].
intros H'. subst. 
apply trans_agreement_not_Perm_and_NotPerm_at_once with 
   e ag action_from_query subject_from_query asset_from_query.
split.
exact H2.
exact H1.
Qed.



End ReasonablityProperties.


Section primPolicyFromPS.
Fixpoint is_primPolicy_in_primPolicies (thePrimPolicy:primPolicy)(l:nonemptylist primPolicy){struct l}  : Prop :=
  
  match l with
    | Single pp => thePrimPolicy = pp
    | NewList pp' rest_pp' => (thePrimPolicy = pp') \/
                              (is_primPolicy_in_primPolicies thePrimPolicy rest_pp')
  end.
  
Definition is_primPolicy_in_policy (thePrimPolicy:primPolicy)(p:policy): Prop :=

  match p with     
    | Policy ppolicies => is_primPolicy_in_primPolicies thePrimPolicy ppolicies
  end.

Definition is_primPolicy_in_prim_policySet (thePrimPolicy:primPolicy)(pps:primPolicySet) : Prop :=
  match pps with 
    | PIPS pips => 
        match pips with | PrimitiveInclusivePolicySet _ pol => 
          is_primPolicy_in_policy thePrimPolicy pol
        end
    | PEPS peps => 
        match peps with | PrimitiveExclusivePolicySet _ pol => 
          is_primPolicy_in_policy thePrimPolicy pol
        end
  end.

  
Definition is_primPolicy_in_policySet (thePrimPolicy:primPolicy)(ps:policySet): Prop :=

  match ps with
    | PPS pps => is_primPolicy_in_prim_policySet thePrimPolicy pps       
  end.

Definition get_ID_From_primPolicy (pp:primPolicy): policyId :=
   match pp with 
    | PrimitivePolicy prq pid action => pid
  end.

Definition get_Action_From_primPolicy (pp:primPolicy): act :=
   match pp with 
    | PrimitivePolicy prq pid action => action 
  end.

Theorem primPolicy_in_policySet_dec :
  (forall (x y:primPolicy), {x = y} + {x <> y}) -> 
    forall (thePrimPolicy:primPolicy)(ps:policySet), 
      {is_primPolicy_in_policySet thePrimPolicy ps} + {~ is_primPolicy_in_policySet thePrimPolicy ps}.
Proof.
intros H.
induction ps as [prim_policySet].
destruct prim_policySet as [proof_of_primInclusivePolicySet | proof_of_primExclusivePolicySet]. 

destruct proof_of_primInclusivePolicySet as [prq_from_ps pol]. simpl.
induction pol as [ppolicies].
induction ppolicies as [| pp ppolicies' IHppolicies].
apply H.


destruct (H pp thePrimPolicy). simpl. auto.
destruct IHppolicies. simpl. auto.
right. unfold not. intros [Hc1| Hc2]; auto.

destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. simpl.
induction pol as [ppolicies].
induction ppolicies as [| pp ppolicies' IHppolicies].
apply H.


destruct (H pp thePrimPolicy). simpl. auto.
destruct IHppolicies. simpl. auto.
right. unfold not. intros [Hc1| Hc2]; auto.

Defined.



End primPolicyFromPS.

Theorem BBBBB: 
  forall (sq:single_query)(pp:primPolicy),
    (is_primPolicy_in_policySet pp (get_PS_From_Agreement (get_Sq_Agreement sq))) ->

    if (trans_preRequisite_dec (get_Sq_Env sq) (get_Sq_Subject sq)
          (get_preRequisite_From_primPolicy pp)
          (Single (get_ID_From_primPolicy pp))
          (get_Prin_From_Agreement (get_Sq_Agreement sq)))
    then (* prin /\ prq /\ prq' *)
      if (pierce_eq_nat_dec (get_Sq_Action sq) (get_Action_From_primPolicy pp))
      then
        (isResultInQueryResult 
          (Result Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))
          (trans_policy_positive (get_Sq_Env sq) (get_Sq_Subject sq) 
             (Policy (Single pp))
             (get_Prin_From_Agreement (get_Sq_Agreement sq)) (get_Sq_Asset sq)
             (get_Sq_Action sq)))
      else
        (isResultInQueryResult 
          (Result Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))
          (trans_policy_positive (get_Sq_Env sq) (get_Sq_Subject sq) 
           (Policy (Single pp))
           (get_Prin_From_Agreement (get_Sq_Agreement sq)) (get_Sq_Asset sq)
           (get_Sq_Action sq)))
    else (* prin /\ prq /\ ~prq' *)
      (isResultInQueryResult 
        (Result Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))
        (trans_policy_positive (get_Sq_Env sq) (get_Sq_Subject sq) 
           (Policy (Single pp))
           (get_Prin_From_Agreement (get_Sq_Agreement sq)) (get_Sq_Asset sq)
           (get_Sq_Action sq))).
Proof.

destruct sq as [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.

destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
intros pp H. simpl.
destruct pp as [prq' pid action_from_policy]. simpl.
destruct (pierce_eq_nat_dec action_from_query action_from_policy).
destruct (trans_preRequisite_dec env_from_query subject_from_query prq'
     [pid] prin_from_agreement). 
simpl. unfold makeResult. auto.
simpl. unfold makeResult. auto.
destruct (trans_preRequisite_dec env_from_query subject_from_query prq' [pid]
     prin_from_agreement).
simpl. unfold makeResult. auto.
simpl. unfold makeResult. auto.
Defined.


End ODRL.
