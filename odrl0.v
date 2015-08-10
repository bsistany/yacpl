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
  (*| ForEachMember : prin  -> nonemptylist constraint -> constraint *)
  | Count : nat -> constraint
  | CountByPrin : prin -> nat -> constraint.

(* taking out Condition, replacing with NotCons *)
Inductive preRequisite : Set :=
  | TruePrq : preRequisite
  | Constraint : constraint -> preRequisite
 (* | ForEachMember : prin  -> nonemptylist constraint -> preRequisite *)
  | NotCons : constraint -> preRequisite
  | AndPrqs : nonemptylist preRequisite -> preRequisite
  | OrPrqs : nonemptylist preRequisite -> preRequisite
  | XorPrqs : nonemptylist preRequisite -> preRequisite.

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
  (*| APS : andPolicySet -> policySet.*)


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
(*            
    | APS aps => match aps with 
                 | AndPolicySet ppolicysets => 
                     is_act_in_primPolicySets ac ppolicysets
               end
*)  
end.

Definition is_act_in_agreement (ac:act)(agr: agreement) : Prop :=
  match agr with
    | Agreement pr ass ps => is_act_in_policySet ac ps
  end.

Definition is_asset_in_agreement (a: asset)(agr: agreement) : Prop :=
  match agr with
    | Agreement pr ass ps => ass = a
  end.

(* Example 2.1 *)


Definition p1A1:primPolicySet :=
  PIPS (PrimitiveInclusivePolicySet
    TruePrq
    (Policy (Single (PrimitivePolicy (Constraint (Count  5)) id1 Print)))).

Definition p2A1prq1:preRequisite := (Constraint (Principal (Single Alice))).
Definition p2A1prq2:preRequisite := (Constraint (Count 2)).

Definition p2A1:primPolicySet :=
  PIPS (PrimitiveInclusivePolicySet
    TruePrq
    (Policy 
      (Single 
        (PrimitivePolicy (AndPrqs (NewList p2A1prq1 (Single p2A1prq2))) id2 Print)))).

(*
Definition A1 := Agreement (NewList Alice (Single Bob)) TheReport
		  (APS (AndPolicySet (NewList p1A1 (Single p2A1)))).
*)
Definition A1 := Agreement (NewList Alice (Single Bob)) TheReport (PPS p1A1).
		

(* Example 2.5 *)

Definition tenCount:preRequisite := (Constraint (Count 10)).
Definition fiveCount:constraint := (Count 5).
Definition oneCount:constraint := (Count 1).

Definition prins2_5 := (NewList Alice (Single Bob)).




(*** 2.6 ***)
Definition prins2_6 := prins2_5.

Definition aliceCount10:preRequisite := Constraint (CountByPrin (Single Alice) 10).
Definition primPolicy2_6:policy := Policy (Single (PrimitivePolicy aliceCount10 id3 Play)).
Definition policySet2_6_modified:= 
  PPS (PEPS (PrimitiveExclusivePolicySet TruePrq primPolicy2_6)).


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

(*
Definition environment := nonemptylist count_equality.
*)

(** New getCount: simply return a number since for formal verification purposes
    it doesn't matter what that number is. The only thing that matters
    is whether the current count satisfies what the corresponding policy 
    specifies. Note that this also means we don't need to keep track of 
    environements if we assume that are always cosistent **)



(** Looks for count of a (subject, id) pair.
    Assumes e is consistent, so it returns the first count it sees for a (subject, id) pair.
	If a count for a (subject, id) pair is not found it returns 0. **)

Fixpoint getCount_old
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
	  then if (beq_nat id id1) then n1 else (getCount_old rest s id)
	  else (getCount_old rest s id)
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
(*
Inductive sorted : list nat -> Prop :=
  snil : sorted nil
| s1 : forall x, sorted (x::nil)
| s2 : forall x y l, sorted (y::l) -> x <= y ->
    sorted (x::y::l).
*)


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


(*
Fixpoint get_list_of_pairs_of_count_formulas (e : environment) :
  nonemptylist (Twos count_equality count_equality) :=

    let nullCountFormula:count_equality := make_count_equality NullSubject NullId 0 in
      let list_of_pairs_of_null : nonemptylist (Twos count_equality count_equality)
	:=  Single (mkTwos nullCountFormula nullCountFormula) in

	  match e with
	    | Single f => list_of_pairs_of_null
	    | NewList first (Single f) => Single (mkTwos first f)
	    | NewList first rest =>
	      let twos := process_two_lists (Single first) rest in
		app_nonempty twos (get_list_of_pairs_of_count_formulas rest)

	  end.
*)
(* test the first clause: single count formula should return a pair of null count formulas *)
Definition e1 : environment :=
  (SingleEnv (make_count_equality Alice id1 8)).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e1).
*)

(* test the second clause: two count formulas should return a pair of the two count formulas *)
Definition e2 : environment := (ConsEnv f1 (SingleEnv f2)).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e2).
*)

(* test the third case: three count formulas should return a list of 3 pairs of count formulas *)
Definition e3 : environment :=
  (ConsEnv (make_count_equality Alice id1 8)
     (ConsEnv (make_count_equality Bob id2 9) (SingleEnv (make_count_equality Charlie id3 10)))).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e3).
*)
(* test the third case with 4 count formulas: should return a list of 6 pairs of count formulas *)
Definition e4 : environment :=
  (ConsEnv (make_count_equality Alice id1 8)
     (ConsEnv (make_count_equality Bob id2 9)
	(ConsEnv (make_count_equality Charlie id3 10)
	  (SingleEnv (make_count_equality Bahman id4 11))))).
(*
Eval compute in (get_list_of_pairs_of_count_formulas e4).
*)
(****************************************)
(****************************************)

(*** set of E-relevant models is Empty <=> e is inconsistent ***)
(*** set of E-relevant models is Non-Empty <=> e is consistent ***)
(*
Fixpoint env_consistent_old (e : environment) : Prop :=
  let pairs : nonemptylist (Twos count_equality count_equality) := (get_list_of_pairs_of_count_formulas e) in
    let pairs_consistent :=
      (fix pairs_consistent (pairs : nonemptylist (Twos count_equality count_equality)) : Prop :=
	match pairs with
	  | Single p => inconsistent (left p) (right p)
	  | NewList p rest =>  inconsistent (left p) (right p) /\ (pairs_consistent rest)
	end) in
  pairs_consistent pairs.
*)


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


(*
Parameter Permitted : subject -> act -> asset -> Prop.


Parameter Unregulated : subject -> act -> asset -> Prop.
*)

(* Parameter getCount : subject -> policyId -> nat. *)


(*** Environments: in odrl0 are simply a conjunction of positive ground literals of the form count(s, id)= n ***)

(** A clause is a list (disjunction) of literals. *)
(* Definition formula := Prop. *)


(** A formula is a list (conjunction) of clauses. *)
(* Definition formula := list clause. *)(** conjuction *)




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
(*
    | PP pp => 
       match pp with
         | PrimitivePolicy prereq pid action => Single pid
       end
*)
    | Policy policies => getIds policies
end.


Fixpoint trans_count_aux_old (e:environment)(ids_and_subjects : nonemptylist (Twos policyId subject)) : nat :=
  match ids_and_subjects with
	| Single pair1 => getCount_old e (right pair1) (left pair1)
	| NewList pair1 rest_pairs =>
	    (getCount_old e (right pair1)(left pair1)) +
	    (trans_count_aux_old e rest_pairs)
  end.


Fixpoint trans_count_old
  (e:environment)(n:nat)(IDs:nonemptylist policyId)
  (prin_u:prin) : Prop :=
  let ids_and_subjects := process_two_lists IDs prin_u in
  let running_total := trans_count_aux_old e ids_and_subjects in
  running_total < n.


Definition trans_count_333 (n:nat) : nat -> Prop :=
  (fun running_total : nat => running_total < n).

Definition trans_count_444 (n:nat) : Prop :=
 exists (running_total:nat), running_total < n.

Definition trans_count (n:nat) : Prop :=
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

    | Count n => trans_count n

    | CountByPrin prn n => trans_count n

  end.



Definition trans_notCons
  (e:environment)(x:subject)(const:constraint)(IDs:nonemptylist policyId)(prin_u:prin) : Prop :=
  ~ (trans_constraint e x const IDs prin_u).

Definition trans_preRequisite
  (e:environment)(x:subject)(prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin) : Prop :=

  match prq with
    | TruePrq => True
    | Constraint const => trans_constraint e x const IDs prin_u
(*
    | ForEachMember prn const_list => trans_forEachMember e x prn const_list IDs
*)
    | NotCons const => trans_notCons e x const IDs prin_u
    | AndPrqs prqs => True (*trans_andPrqs x prq IDs prin_u a*)
    | OrPrqs prqs => True (*trans_orPrqs x prq IDs prin_u a*)
    | XorPrqs prqs => True (*trans_xorPrqs x prq IDs prin_u a*)
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
 
          if (eq_nat_dec action_from_query action)
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
(*
let process_single_pp := 
 (fix process_single_pp (pp: primPolicy) : nonemptylist result :=
  match pp with
    | PrimitivePolicy prq policyId action => 
        if (eq_nat_dec action_from_query action)
        then 
            (Single 
              (makeResult NotPermitted x action_from_query a))
        else 
            (Single 
              (makeResult Unregulated x action_from_query a))
  end) in

let trans_pp_list := 
  (fix trans_pp_list (pp_list:nonemptylist primPolicy)(a:asset){struct pp_list}:=
		  match pp_list with
		    | Single pp1 => process_single_pp_trans_policy_negative pp1
		    | NewList pp pp_list' => app_nonempty
			(p pp) 
			(trans_pp_list pp_list' a)
		  end) in
*)

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
apply eq_nat_dec.
destruct (eq_nat_dec a0 a); simpl; auto.
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

(*From Pierce: SF*)

Theorem eq_nat_dec : forall (n m : nat), {n = m} + {n <> m}.
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


(*
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
*)




Theorem trans_count_dec :
   forall (n:nat),
     {trans_count n} + {~trans_count n}.

Proof.
intros.
apply lt_dec. 

Defined.


(*** HERE I am : May 22, 2015, 1:04. ***)


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

(***
Theorem trans_forEachMember_Aux_dec :
  forall (e:environment)
         (x:subject)
         (prins_and_constraints : nonemptylist (Twos subject constraint))
	 (IDs:nonemptylist policyId),
   {trans_forEachMember_Aux e x prins_and_constraints IDs} +
   {~ trans_forEachMember_Aux e x prins_and_constraints IDs}.
Proof.
intros e x prins_and_constraints IDs. 
unfold trans_forEachMember_Aux.
induction prins_and_constraints.
apply trans_constraint_dec.
simpl. 


Theorem trans_forEachMember_dec :
 forall (e:environment)(x:subject)
  (principals: nonemptylist subject)
  (const_list:nonemptylist constraint)
  (IDs:nonemptylist policyId),
    {trans_forEachMember e x principals const_list IDs} +
    {~trans_forEachMember e x principals const_list IDs}.

Proof.
intros e x principals const_list IDs.
unfold trans_forEachMember. simpl.

***)





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
  

Theorem trans_preRequisite_dec :
  forall (e:environment)(x:subject)
    (prq:preRequisite)(IDs:nonemptylist policyId)(prin_u:prin),
       {trans_preRequisite e x prq IDs prin_u} +
       {~ trans_preRequisite e x prq IDs prin_u}.
Proof.
intros e x prq IDs prin_u.
induction prq as [theTruePrq | theConst | theNotConst| 
                  theAndPrqs | theOrPrqs | theXorPrqs].
simpl. auto.
simpl. apply trans_constraint_dec.
simpl. apply trans_notCons_dec.
simpl. auto.
simpl. auto.
simpl. auto.
Qed. 

Theorem act_in_primPolicy_dec :
    forall (ac:act) (p:primPolicy), 
      {is_act_in_prim_policy ac p} + {~ is_act_in_prim_policy ac p}.

Proof.
intros ac p. destruct p. simpl. apply eq_nat_dec. Defined.

Theorem act_in_primPolicies_dec:
   forall (ac:act) (l:nonemptylist primPolicy), 
      {is_act_in_primPolicies ac l} + {~ is_act_in_primPolicies ac l}.

Proof.
induction l as [| a0 l IHl].

destruct x; apply eq_nat_dec.

destruct a0. destruct (eq_nat_dec a ac). simpl. auto.

destruct IHl. simpl. auto.

right. unfold not. intros [Hc1| Hc2]. auto. auto.
Defined.



Theorem act_in_policy_dec :
    forall (ac:act) (p:policy), 
      {is_act_in_policy ac p} + {~ is_act_in_policy ac p}.

Proof.
intros ac p. induction p.

 apply act_in_primPolicies_dec.
 (*
 destruct a. 
 pose (proof_of_act_in_primPolicies_dec := act_in_primPolicies_dec ac n).
 unfold is_act_in_policy. apply proof_of_act_in_primPolicies_dec. 
 *)
Defined.

Theorem act_in_primPolicySet_dec :
    forall (ac:act) (pps:primPolicySet), 
      {is_act_in_prim_policySet ac pps} + {~ is_act_in_prim_policySet ac pps}.

Proof.
intros ac pps. destruct pps. 
 destruct p; apply act_in_policy_dec.
 destruct p; apply act_in_policy_dec. Defined.


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
(* 
 destruct a. 
 pose (proof_of_act_in_primPolicySets_dec := act_in_primPolicySets_dec ac n).
 unfold is_act_in_policySet; apply proof_of_act_in_primPolicySets_dec. 
*)
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
          if (eq_nat_dec action_from_query action)
          then
            (Single 
              (makeResult Permitted x action_from_query a))
            (*(Permitted x action_from_query a)*)
          else
            (Single 
              (makeResult Unregulated x action_from_query a))
            (*(Unregulated x action_from_query a)*)
        else (* prin /\ prq /\ ~prq' *)
          (Single 
              (makeResult Unregulated x action_from_query a))
          (*(Unregulated x action_from_query a)*)
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
(*
let process_single_pp := 
  (fix process_single_pp (pp: primPolicy) : nonemptylist result :=
  match pp with
    | PrimitivePolicy prq' policyId action =>
        if (trans_preRequisite_dec e x prq' (Single policyId) prin_u)
        then (* prin /\ prq /\ prq' *)
          if (eq_nat_dec action_from_query action)
          then
            (Single 
              (makeResult Permitted x action_from_query a))
            (*(Permitted x action_from_query a)*)
          else
            (Single 
              (makeResult Unregulated x action_from_query a))
            (*(Unregulated x action_from_query a)*)
        else (* prin /\ prq /\ ~prq' *)
          (Single 
              (makeResult Unregulated x action_from_query a))
          (*(Unregulated x action_from_query a)*)
  end) in 

let trans_pp_list := 
  (fix trans_pp_list (pp_list:nonemptylist primPolicy)(prin_u:prin)(a:asset){struct pp_list}:=
		  match pp_list with
		    | Single pp1 => process_single_pp_trans_policy_positive pp1
		    | NewList pp pp_list' => app_nonempty
			(process_single_pp_trans_policy_positive pp) 
			(trans_pp_list pp_list' prin_u a)
		  end) in
*)
  match p with
(*
  | PP pp => process_single_pp pp 
*)  
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

if (eq_nat_dec asset_from_query a)
then (* asset_from_query = a *)  
    match ps with
      | PPS pps => process_single_ps pps
    end
else (* asset_from_query <> a *)
       (Single 
          (makeResult 
             Unregulated subject_from_query action_from_query asset_from_query))
    (*(Unregulated subject_from_query action_from_query asset_from_query)*).
  

Definition trans_agreement
   (e:environment)(ag:agreement)(action_from_query:act)
   (subject_from_query:subject)(asset_from_query:asset) : nonemptylist result :=

   match ag with
   | Agreement prin_u a ps => 
       (trans_ps e action_from_query subject_from_query asset_from_query ps prin_u a)
   end.
End Sems.

(********
Inductive nonemptylist (A : Set) : Set :=
  | Single : A -> nonemptylist
  | NewList : A -> nonemptylist -> nonemptylist.

if a property is true for the Single case, and if it holds for a list l 
then it also holds for cons a l for any a, then it holds for all lists.

fun (A : Set) (P : nonemptylist A -> Prop) => nonemptylist_rect P
     : forall (A : Set) (P : nonemptylist A -> Prop),

       (forall x : A, P [x]) // if a property is true for x
       // and if it holds for a nonemptylist n then it also holds for 'NewList x n' for any x
       -> (forall (x : A) (n : nonemptylist A), P n -> P (x, n)) 
       -> forall n : nonemptylist A, P n // then it holds for all nonemptylists.

Theorem ind_nonemptylist : 

forall (X : Set) 
       (P : environment -> preRequisite -> nonemptylist X -> prin -> asset -> act -> Prop),
       (forall (e:environment)(prq: preRequisite)
          (prin_u:prin)(a:asset)(action_from_query:act)(x : X), 
             (P e prq [x] prin_u a action_from_query))
        -> (forall (e:environment)(prq: preRequisite)
          (prin_u:prin)(a:asset)(action_from_query:act)(x : X)(n : nonemptylist X), 
              (P e prq n prin_u a action_from_query) -> 
                 (P e prq (x, n) prin_u a action_from_query))
        -> forall (e:environment)(prq: preRequisite)
          (prin_u:prin)(a:asset)(action_from_query:act)(n : nonemptylist X), 
              (P e prq n prin_u a action_from_query).
Proof.
intros X P hSingle hNewList e prq prin_u a action_from_query n.
induction n.
specialize hSingle with e prq prin_u a action_from_query x.
exact hSingle.

apply hNewList.
exact IHn.
Qed.
*****)

(*
Theorem trans_policy_PIPS_dec:
  forall (e:environment)(prq: preRequisite)(p:policy)
  (prin_u:prin)(a:asset)(action_from_query:act)(sub:subject),

(trans_policy_PIPS e prq p prin_u a action_from_query) ->
  ((Permitted sub action_from_query a) \/
  ~(Permitted sub action_from_query a) \/
   (Unregulated sub action_from_query a)).
Proof.
intros e prq p prin_u a action_from_query sub.
destruct p. 
induction n as [| x rest IHn].
unfold trans_policy_PIPS. 
intros H.
specialize H with sub.
destruct (trans_prin_dec sub prin_u).
destruct (trans_preRequisite_dec e sub prq (getId (Policy [x])) prin_u).
simpl in H.
destruct x as [prq' pid action_from_policy].
destruct (trans_preRequisite_dec e sub prq' [pid] prin_u).
destruct (eq_nat_dec action_from_query action_from_policy).
left. exact H.
right. right. exact H.
right. right. exact H.
simpl in H.
right. right. exact H.
simpl in H.
right. right. exact H.
intros H. 

apply IHn.

assert (trans_policy_PIPS e prq (Policy [x]) prin_u a action_from_query).
destruct x as [prq' pid action_from_policy].
unfold trans_policy_PIPS. 
intros.
destruct (trans_prin_dec x prin_u).
destruct (trans_preRequisite_dec e x prq
     (getId (Policy [PrimitivePolicy prq' pid action_from_policy])) prin_u). simpl.
destruct (trans_preRequisite_dec e x prq' [pid] prin_u).
destruct (eq_nat_dec action_from_query action_from_policy).


simpl.
destruct (trans_preRequisite_dec e sub prq' [pid] prin_u).
destruct (eq_nat_dec action_from_query action_from_policy).
left. exact H.
right. right. exact H.
right. right. exact H.
simpl in H.
right. right. exact H.
destruct x. 

unfold trans_policy_PIPS in H.
specialize H with sub.
destruct (trans_prin_dec sub prin_u).
destruct (trans_preRequisite_dec e sub prq (getId (Policy (p, n))) prin_u).
simpl in H.

*)




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

(***** 3.1 *****)

(**
Eval simpl in (trans_ps e1 policySet2_5 prins2_5 ebook).

Eval compute in (trans_ps e2 policySet2_5 prins2_5 ebook).

**)


(*** Canonical Agreement example ***)
Section A1.

Definition psA1:policySet :=
  PPS (PIPS (PrimitiveInclusivePolicySet
             TruePrq
            (Policy (Single (PrimitivePolicy (Constraint (Count  5)) id1 Print))))).

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
  PPS (PIPS (PrimitiveInclusivePolicySet TruePrq 
   (Policy (Single (PrimitivePolicy TruePrq id1 Print))))).

Definition agr := Agreement (Single Alice) TheReport ps_alice.
Definition e_agr : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement e_agr agr).

Definition ps_bob:policySet := 
   PPS (PEPS (PrimitiveExclusivePolicySet TruePrq 
   (Policy (Single (PrimitivePolicy TruePrq id2 Print))))).
Definition agr' := Agreement (Single Bob) TheReport ps_bob.
Definition e_agr' : environment := (SingleEnv (make_count_equality NullSubject NullId 0)).
Eval compute in (trans_agreement e_agr' agr').

End Example4_3.

Section A2.

(**  getCount Alice "id1" = 5,	and see if you can prove ~(Permitted Alice ...). **)
Definition eA2 : environment :=
  (SingleEnv (make_count_equality Alice id1 3)).

Definition psA2:policySet :=
  PPS (PIPS (PrimitiveInclusivePolicySet
             TruePrq
            (Policy (Single (PrimitivePolicy (Constraint (Count  5)) id1 Print))))).

Definition AgreeA2 := Agreement (Single Alice) TheReport psA2.

Eval compute in (trans_agreement eA2 AgreeA2).

Eval simpl in (trans_agreement eA2 AgreeA2).

(* Hypothesis AliceCount : getCount Alice "id1" = 5. *)

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


(*
Hypothesis BobNotInPrin: not (trans_prin Bob (get_Prin_From_Agreement AgreeA2)).

Theorem BobUnregulated: 
(QueryResult (Single (makeResult Unregulated Bob Print TheReport))).

Proof.
simpl in H.
simpl in BobNotInPrin.

specialize H with Bob TheReport.


destruct (eq_nat_dec TheReport TheReport).
specialize H with Print.
unfold trans_policy_PIPS in H.
specialize H with Bob. simpl in H.
exact H. specialize H with Print.
exact H. 
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

(***
Theorem FFF: 8<10.
Proof. apply le_S. apply le_n. Qed.

le_n : forall n : nat, n <= n
le_S : : forall n m : nat, n <= m -> n <= S m.
***)

(**
Definition AgreeA3 := Agreement prins2_5 ebook policySet2_5.
**)

(**
Definition eA3 : environment :=
  (NewList (make_count_equality Alice id1 3)
     (NewList (make_count_equality Alice id2 11)
	(NewList (make_count_equality Bob id1 6)
	  (Single (make_count_equality Bob id2 1))))).
Eval compute in (trans_agreement eA3 AgreeA3).

forall x : nat,
       (x = 101 \/ x = 102) /\ 22 <= 10 ->
       (4 <= 5 /\ 7 <= 5 -> Permitted x "Display" "ebook") /\
       (12 <= 1 /\ 2 <= 1 -> Permitted x "Print" "ebook")
     : Prop

**)
Definition eA3 : environment :=
  (ConsEnv (make_count_equality Alice id1 3)
     (ConsEnv (make_count_equality Alice id2 0)
	(ConsEnv (make_count_equality Bob id1 4)
	  (SingleEnv (make_count_equality Bob id2 0))))).
(**
Eval compute in (trans_agreement eA3 AgreeA3).
Hypothesis H: trans_agreement eA3 AgreeA3.

Theorem T1_A3: Permitted Alice Print ebook.
Proof. simpl in H. apply H. intuition. intuition. Qed.
**)
End A3.



Section A5.

Definition prin_bob := (Single Bob). 
Definition single_pol:policy := Policy (Single (PrimitivePolicy TruePrq id3 Print)).
Definition two_pols:policy := Policy 
  (NewList (PrimitivePolicy TruePrq id1 Display)
     (Single (PrimitivePolicy TruePrq id3 Print))).

Definition single_pol_set:policySet := 
  PPS (PEPS (PrimitiveExclusivePolicySet TruePrq single_pol)).
Definition two_pol_set:policySet := 
  PPS (PEPS (PrimitiveExclusivePolicySet TruePrq two_pols)).

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
destruct (trans_preRequisite_dec eA5 x TruePrq (getId two_pols) prin_bob).
simpl.
destruct (trans_preRequisite_dec eA5 x TruePrq [id1] prin_bob).
destruct (trans_preRequisite_dec eA5 x TruePrq [id3] prin_bob).
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
destruct (trans_preRequisite_dec eA5 x TruePrq (getId two_pols) prin_bob).
simpl in t. contradiction.
simpl in n. intuition.
simpl. unfold makeResult.
right. auto. Qed.
(*
destruct (Peano_dec.eq_nat_dec sub Bob).
destruct (trans_preRequisite_dec eA5 sub TruePrq (id1, [id3]) prin_bob).
destruct (trans_preRequisite_dec eA5 sub TruePrq [id1] prin_bob).
destruct (eq_nat_dec ac Display).
destruct H as [H1 H2]. 
destruct (trans_preRequisite_dec eA5 sub TruePrq [id3] prin_bob).
destruct (eq_nat_dec ac Print).
*)
Theorem T2_A5: isPermissionDenied Alice Print LoveAndPeace 
  (trans_agreement eA5 AgreeA5_two Print Alice LoveAndPeace).


Proof. 

apply T1_A5. 

intuition. inversion H. Qed.

(*
simpl in H. 

specialize H with Alice LoveAndPeace.
destruct (eq_nat_dec LoveAndPeace LoveAndPeace).

specialize H with Print Alice.

destruct (Peano_dec.eq_nat_dec Alice Bob). 
destruct (trans_preRequisite_dec eA5 Alice TruePrq [id3] prin_bob).

assert (Alice <> Bob). intuition. inversion H0. contradiction.
assert (trans_preRequisite eA5 Alice TruePrq [id3] prin_bob).
simpl. auto. contradiction.
specialize H with Print.
destruct (Peano_dec.eq_nat_dec Print Print).
exact H. 
assert (Print=Print). auto. contradiction.
assert (LoveAndPeace=LoveAndPeace). auto. contradiction.

Qed.
*)
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








(*

Parameter even: nat -> Prop.
Parameter divides: nat -> nat -> Prop.

Theorem th1 : forall (x y: nat),
 (even x) -> (divides x y) -> (even y).

Theorem th2 : forall (x y: nat), divides x (x * y).

Check even.

Check fun (x:nat) => fun (h: even x) => h.

Definition evenn (x:nat) : Prop :=
  forall (P: nat -> Prop), forall (y:nat), P(2*y)-> P x.

Check evenn.

Theorem th3: forall (x:nat), evenn 2.
Proof. unfold evenn. intros. apply H.
*)
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


(*
Fixpoint get_act_from_policy(p:policy) : act
 let getAct
    := (fix getAct (policies: nonemptylist policy) : nonemptylist policyId :=
	  match policies with
	    | Single p => get_act_from_policy p
	    | NewList p rest => (get_act_from_policy p) (getIds rest)
	  end) in
  match p with
    | PrimitivePolicy prereq pid action => action
    | AndPolicy policies =>
  end.
*)
Section ZZZ.



(*
Need to add to hypo facts:

act from sq = one of the acts in one of the policies
asset from sq = asset from agreement
*)

(*****
Hypothesis subjectNotInPrin:
  forall (sq:single_query),
(~trans_prin (get_Sq_Subject sq)
	      (get_Prin_From_Agreement ((get_Sq_Agreement sq)))).


Fixpoint actInPolicy (ac:act)(p:policy) : Prop :=
let actInPolicyAux
    := (fix actInPolicyAux (ac:act)(policies: nonemptylist policy) : Prop :=
	  match policies with
	    | Single p => actInPolicy ac p
	    | NewList p rest => (actInPolicy ac p) \/ (actInPolicyAux ac rest)
	  end) in

  match p with
    | PrimitivePolicy prereq pid action => action = ac
    | AndPolicy policies => actInPolicyAux ac policies
  end.

Fixpoint actInPolicySet (ac:act)(ps:policySet) : Prop :=
let trans_ps_list := (fix trans_ps_list (ac:act)(ps_list:nonemptylist policySet){struct ps_list}:=
		  match ps_list with
		    | Single ps1 => actInPolicySet ac ps1
		    | NewList ps ps_list' => (actInPolicySet ac ps) \/ (trans_ps_list ac ps_list')
		  end) in
    match ps with
    | PrimitivePolicySet prq p => actInPolicy ac p
    | PrimitiveExclusivePolicySet prq p => actInPolicy ac p
    | AndPolicySet ps_list => trans_ps_list ac ps_list
  end.



Fixpoint policyInPolicySet (pol:policy)(ps:policySet) : Prop :=
let trans_ps_list := (fix trans_ps_list (ps_list:nonemptylist policySet){struct ps_list}:=
		  match ps_list with
		    | Single ps1 => policyInPolicySet pol ps1
		    | NewList ps ps_list' => (policyInPolicySet pol ps) \/ (trans_ps_list ps_list')
		  end) in
    match ps with
    | PrimitivePolicySet prq p => p = pol
    | PrimitiveExclusivePolicySet prq p => p = pol
    | AndPolicySet ps_list => trans_ps_list ps_list
  end.

****)

(*

Lemma ifActMentionedInPSTheActExistsInSomePolicy : 
forall (ac1:act)(pset : policySet), 
(actInPolicySet ac1 pset) -> exists (pol:policy), (policyInPolicySet pol pset) /\ (actInPolicy  ac1 pol).
Proof. intros.
destruct pset in H.
exists p0. simpl in H. exact H.
exists p0. simpl in H. exact H.
(* unfold actInPolicySet in H. *)
induction n as [| n'].
induction x.  
   exists p0. simpl in H. exact H.
   exists p0. simpl in H. exact H.
   exists p0. simpl in H. exact H.
simpl in H. 



 
induction pset.
  simpl. exists p0. auto.
  simpl. exists p0. auto.
  Print policySet.
  destruct n as [| l' l''].
  induction n.
     simpl. induction x.
  unfold actInPolicySet. 
auto. Qed.
*)
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

(*
          (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq)) -> 
                           forall (ac:act),
                             (Unregulated (get_Sq_Subject sq) ac (get_Sq_Asset sq)).
*)
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

destruct (eq_nat_dec asset_from_query asset_from_agreement).
contradiction.

unfold makeResult. simpl. auto.

destruct ps as [prim_policySet]. simpl.
split.
destruct (eq_nat_dec asset_from_query asset_from_agreement).
contradiction.
unfold permittedResult.
simpl.
unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.


destruct (eq_nat_dec asset_from_query asset_from_agreement).
contradiction.

unfold notPermittedResult.
simpl.
unfold makeResult.
apply AnswersNotEqual. intuition. inversion H.



(*
simpl in H'; destruct H' as [H1 H2];
specialize H1 with asset_from_query ac0 sub;
refine (H1 _); left; exact H.
*)
Qed.







(*** July 1st, 2015: It should now be possible to proof the one below ****)
(*
Theorem queryWithNonReleveantActionIsUnregulated:
  forall (sq:single_query)(ac:act),
     ~(is_act_in_policySet ac 
        (get_PS_From_Agreement 
            (get_Sq_Agreement sq)))
-> 
  isPermissionUnregulated (get_Sq_Subject sq) ac (get_Sq_Asset sq)
   (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ac (get_Sq_Subject sq) (get_Sq_Asset sq)).


Proof.
destruct sq as 
  [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
intros ac. 
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.

unfold isPermissionUnregulated.


destruct ps as [prim_policySet].
destruct prim_policySet as [proof_of_primInclusivePolicySet | proof_of_primExclusivePolicySet]. 
destruct proof_of_primInclusivePolicySet as [prq_from_ps pol]. simpl.
intros H.

destruct (eq_nat_dec asset_from_query asset_from_agreement).
simpl.

unfold trans_policy_PIPS. 
destruct (trans_prin_dec subject_from_query prin_from_agreement).
destruct (trans_preRequisite_dec env_from_query subject_from_query prq_from_ps
        (getId pol) prin_from_agreement).



unfold trans_policy_positive.

intros H. simpl in H.


specialize H with subject_from_query asset_from_query.


destruct (eq_nat_dec asset_from_query asset_from_agreement).
specialize H with ac subject_from_query.
destruct (trans_prin_dec subject_from_query prin_from_agreement).
destruct (trans_preRequisite_dec env_from_query subject_from_query prq_from_ps
         (getId pol) prin_from_agreement). 
induction pol as [ppolicies].

induction ppolicies.

destruct x as [prq' pid action_from_policy].
simpl in H.
destruct (trans_preRequisite_dec env_from_query subject_from_query prq' 
         [pid] prin_from_agreement).

destruct (eq_nat_dec ac action_from_policy).
simpl in H'. contradiction.
subst; exact H.
subst; exact H.
apply IHppolicies.
simpl. simpl in H'. intuition.



elim H.
simpl.
Hint Resolve Single NewList.
simple induction 2 in H; auto.

destruct andPol as [primPolicies].
simpl in H.
induction primPolicies.
simpl in H.






destruct primPol as [prq' pid action_from_policy]. simpl in H.
subst; exact H.

destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy]. simpl in H.
subst; exact H.
specialize H with ac.
exact H.
intros H' H.

specialize H with subject_from_query asset_from_query.

destruct (eq_nat_dec asset_from_query asset_from_agreement).
specialize H with ac.
destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. simpl.
specialize H with subject_from_query.
destruct (trans_prin_dec subject_from_query prin_from_agreement).
destruct (trans_preRequisite_dec env_from_query subject_from_query prq_from_ps
         (getId pol) prin_from_agreement).
destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy]. 

destruct (trans_preRequisite_dec env_from_query subject_from_query prq' [pid]
         prin_from_agreement).

destruct (eq_nat_dec ac action_from_policy).
simpl in H'. contradiction.
subst; exact H.
subst; exact H.

destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy]. simpl in H.
subst; exact H.

destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy]. simpl in H.
specialize H with ac.
simpl in H'.
destruct (Peano_dec.eq_nat_dec ac action_from_policy). contradiction.
subst; exact H.

specialize H with ac.
exact H.
*)
(*
intros H H'; simpl in H'; destruct H' as [H1 H2];
unfold is_act_in_policySet in H;
specialize H1 with asset_from_query ac subjet_from_query;
refine (H1 _); right; exact H.
*)


Section preRequisiteFromPS.

Definition get_preRequisite_From_primPolicy (p:primPolicy) : 
                  preRequisite :=
  match p with 
    | PrimitivePolicy prq pid action => prq
  end.


Fixpoint get_preRequisite_From_primPolicies 
  (l:nonemptylist primPolicy){struct l}  : preRequisite :=
  
         match l with
           | Single pp => get_preRequisite_From_primPolicy pp
	   | NewList pp rest => 
               AndPrqs (app_nonempty
                         (Single (get_preRequisite_From_primPolicy pp)) 
                         (Single (get_preRequisite_From_primPolicies rest)))
         end.
  
Definition get_preRequisite_From_policy (p:policy): preRequisite :=

  match p with
    (*| PP pp => get_preRequisite_From_primPolicy pp *)           
    | Policy ppolicies => 
        get_preRequisite_From_primPolicies ppolicies
  end.

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
    (*               
    | APS aps => match aps with 
                 | AndPolicySet ppolicysets => 
                     get_preRequisite_From_primPolicySets ppolicysets
               end
    *)
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
(*               
    | APS aps => match aps with 
                 | AndPolicySet ppolicysets => 
                     get_policy_preRequisite_From_primPolicySets ppolicysets
               end
*)
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
(*               
    | APS aps => match aps with 
                 | AndPolicySet ppolicysets => 
                     get_IDs_From_primPolicySets ppolicysets
               end
*)
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
(*               
    | APS aps => match aps with 
                 | AndPolicySet ppolicysets => 
                     get_policy_preRequisite_From_primPolicySets ppolicysets
               end
*)
  end.

End preRequisiteFromPS.

(*
Theorem trans_policy_positive_implies_PermOrUnregulated:
  forall (sq:single_query)(pol: policy),

if (trans_preRequisite_dec (get_Sq_Env sq) (get_Sq_Subject sq)
          (get_preRequisite_From_policy pol)
          (get_ID_From_policy pol)
          (get_Prin_From_Agreement (get_Sq_Agreement sq)))
    then (*  *)
      ((trans_policy_positive (get_Sq_Env sq) (get_Sq_Subject sq) pol
          (get_Prin_From_Agreement (get_Sq_Agreement sq))
          (get_Asset_From_Agreement (get_Sq_Agreement sq))) ->
       (Permitted (get_Sq_Subject sq) (get_act_From_policy pol) 
          (get_Asset_From_Agreement (get_Sq_Agreement sq))))
    else (*  *)
      ((trans_policy_positive (get_Sq_Env sq) (get_Sq_Subject sq) pol
          (get_Prin_From_Agreement (get_Sq_Agreement sq))
          (get_Asset_From_Agreement (get_Sq_Agreement sq))) ->
       (Unregulated (get_Sq_Subject sq) (get_act_From_policy pol)
          (get_Asset_From_Agreement (get_Sq_Agreement sq)))).

Proof.
intros sq pol.
destruct sq as 
 [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
induction pol as [aPrimPolicy]. induction aPrimPolicy as [prq pid ac]. simpl.
destruct (trans_preRequisite_dec env_from_query subject_from_query
     prq (Single pid)
     prin_from_agreement). 
intros H. destruct H as [H1 H2]. 
pose (proof_of_Permitted := H1 t).

exact proof_of_Permitted.

intros H. destruct H as [H1 H2]. 
pose (proof_of_Unregulated := H2 n).
exact proof_of_Unregulated.

Qed.
*)
(*
Theorem trans_policy_unregulated_implies_Unregulated:
  forall (sq:single_query)(pol: policy),

(trans_policy_unregulated (get_Sq_Env sq) (get_Sq_Subject sq) pol
          (get_Prin_From_Agreement (get_Sq_Agreement sq))
          (get_Asset_From_Agreement (get_Sq_Agreement sq))) ->
       (Unregulated (get_Sq_Subject sq) (get_act_From_policy pol)
          (get_Asset_From_Agreement (get_Sq_Agreement sq))).

Proof.
intros sq pol.
destruct sq as 
 [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
induction pol as [aPrimPolicy]. induction aPrimPolicy as [prq pid ac]. simpl.
auto. Qed.

Theorem trans_policy_negative_implies_NotPermitted:
  forall (sq:single_query)(pol: policy),

(trans_policy_negative (get_Sq_Env sq) (get_Sq_Subject sq) pol
          (get_Asset_From_Agreement (get_Sq_Agreement sq))) ->
       not (Permitted (get_Sq_Subject sq) (get_act_From_policy pol)
             (get_Asset_From_Agreement (get_Sq_Agreement sq))).

Proof.
intros sq pol.
destruct sq as 
 [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
induction pol as [aPrimPolicy]. induction aPrimPolicy as [prq pid ac]. simpl.
auto. Qed.
*)

(*
Definition PermittedOrNotPermittedOrUnregulated (sq:single_query) :=
  ((Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq)) \/
   (Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq)) \/
  ~(Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))).

Definition trans_agr_implies_Unregulated (agr:agreement)
  (env_from_query:environment)
  (subject_from_query:subject)(action_from_query:act)
  (asset_from_query:asset)  := 
 (trans_agreement env_from_query agr -> 
   (Unregulated subject_from_query action_from_query asset_from_query)).

Definition trans_agr_implies_Permitted (agr:agreement)
  (env_from_query:environment)
  (subject_from_query:subject)(action_from_query:act)
  (asset_from_query:asset)  := 
 (trans_agreement env_from_query agr -> 
   (Permitted subject_from_query action_from_query asset_from_query)).

Definition trans_agr_implies_NotPermitted (agr:agreement)
  (env_from_query:environment)
  (subject_from_query:subject)(action_from_query:act)
  (asset_from_query:asset)  :=  
 (trans_agreement env_from_query agr ->  
   (~Permitted subject_from_query action_from_query asset_from_query)).

*)

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
    destruct (eq_nat_dec subj subj').
    destruct (eq_nat_dec ac ac').
    destruct (eq_nat_dec ass ass').
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
destruct (eq_nat_dec action_from_query actionFromPrimPolicy).
simpl; unfold makeResult; left; reflexivity. 
simpl; unfold makeResult; right; reflexivity.
simpl; unfold makeResult; right; reflexivity.


destruct pp' as [prq' pid actionFromPrimPolicy].
simpl. 
destruct (trans_preRequisite_dec e s prq' [pid] prin_u).
destruct (eq_nat_dec action_from_query actionFromPrimPolicy).

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
destruct (Peano_dec.eq_nat_dec action_from_query actionFromPrimPolicy).
simpl; unfold makeResult; left; reflexivity. 
simpl; unfold makeResult; right; reflexivity.


destruct pp' as [prq' pid actionFromPrimPolicy].
simpl. 
destruct (Peano_dec.eq_nat_dec action_from_query actionFromPrimPolicy).

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
destruct (eq_nat_dec action_from_query actionFromPrimPolicy).
left; simpl; unfold makeResult; auto.

right; right; simpl; unfold makeResult; auto.
right; right; simpl; unfold makeResult; auto.
right; right; simpl; unfold makeResult; auto.
simpl.
destruct (Peano_dec.eq_nat_dec action_from_query actionFromPrimPolicy).
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
destruct (Peano_dec.eq_nat_dec action_from_query actionFromPrimPolicy).
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
destruct (eq_nat_dec asset_from_query a).
destruct pips as [prq p].
apply or_commutes.
right. subst. apply trans_policy_PIPS_dec.
right. right. simpl. unfold makeResult; auto.


simpl. 
destruct (eq_nat_dec asset_from_query a).
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
destruct (eq_nat_dec action_from_query actionFromPrimPolicy).
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl.
destruct pp' as [prq' pid actionFromPrimPolicy]. simpl.
destruct (trans_preRequisite_dec e s prq' [pid] prin_u).
destruct (eq_nat_dec action_from_query actionFromPrimPolicy).

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
destruct (Peano_dec.eq_nat_dec action_from_query actionFromPrimPolicy).
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.
simpl. unfold makeResult. apply AnswersNotEqual. intros contra. inversion contra.

destruct pp' as [prq' pid actionFromPrimPolicy]. simpl.
destruct (Peano_dec.eq_nat_dec action_from_query actionFromPrimPolicy).

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
destruct (eq_nat_dec action_from_query actionFromPrimPolicy).
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
destruct (eq_nat_dec asset_from_query a).
subst. apply trans_policy_PIPS_perm_implies_not_notPerm_dec. simpl.
unfold makeResult. intros H. intros contra. apply AnswersNotEqual in contra. auto.
intros contra'. inversion contra'.

destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. 
destruct (eq_nat_dec asset_from_query a).
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
destruct (eq_nat_dec asset_from_query a).

intros H'.
specialize trans_policy_PIPS_dec_not with e prq_from_ps pol subject_from_query
     prin_u a action_from_query.
intros H. subst. contradiction.

simpl. unfold makeResult. intros contra. apply AnswersNotEqual. intros contra'. 
inversion contra'. 

destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. 
destruct (eq_nat_dec asset_from_query a).
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

Theorem blah_dec:
  forall (sq:single_query),

let results :=
  (trans_agreement (get_Sq_Env sq)(get_Sq_Agreement sq) 
     (get_Sq_Action sq)(get_Sq_Subject sq)(get_Sq_Asset sq)) in
 (isPermissionGranted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq) results) \/
 (isPermissionDenied (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq) results) \/
 (isPermissionUnregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq) results).


Proof.
destruct sq as 
  [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
destruct ps as [prim_policySet]. simpl.

destruct (eq_nat_dec asset_from_query asset_from_agreement).

destruct prim_policySet as [proof_of_primInclusivePolicySet | proof_of_primExclusivePolicySet]. simpl. 
destruct proof_of_primInclusivePolicySet as [prq_from_ps pol]. simpl.

destruct (trans_policy_PIPS_dec env_from_query prq_from_ps pol subject_from_query
     prin_from_agreement asset_from_agreement action_from_query).





left. 
destruct (eq_nat_dec asset_from_query asset_from_agreement).
unfold isPermissionGranted.
unfold isResultInQueryResult in H. 
unfold permittedResult.
split. subst. exact H.
unfold notPermittedResult. intuition.

Bahman 
unfold trans_policy_PIPS. 
destruct (trans_prin_dec subject_from_query prin_from_agreement).
destruct (trans_preRequisite_dec env_from_query subject_from_query prq_from_ps
        (getId pol) prin_from_agreement).
split.
induction pol as [ppolicies]. 
unfold trans_policy_positive.

intros H. simpl in H.





intros H.
specialize H with subject_from_query asset_from_query.

destruct (eq_nat_dec asset_from_query asset_from_agreement). simpl in H.
specialize H with action_from_query subject_from_query.



destruct (trans_prin_dec subject_from_query prin_from_agreement). 
destruct (trans_preRequisite_dec env_from_query subject_from_query prq_from_ps
          (getId pol) prin_from_agreement).
destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy].

destruct (trans_preRequisite_dec env_from_query subject_from_query prq' 
         [pid] prin_from_agreement).
destruct (eq_nat_dec action_from_query action_from_policy).
left; subst; exact H.
right; right; subst; exact H.
right; right; subst; exact H.
destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy].
simpl in H.
right; right; subst; exact H.

destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy].
simpl in H.
right; right; subst; exact H.

specialize H with action_from_query.
right; right; subst; exact H.

intros H.
specialize H with subject_from_query asset_from_query.

destruct (eq_nat_dec asset_from_query asset_from_agreement). simpl in H.
specialize H with action_from_query.
destruct proof_of_primExclusivePolicySet as [prq_from_ps pol]. simpl.
specialize H with subject_from_query.

destruct (trans_prin_dec subject_from_query prin_from_agreement). 
destruct (trans_preRequisite_dec env_from_query subject_from_query prq_from_ps
          (getId pol) prin_from_agreement).
destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy].

destruct (trans_preRequisite_dec env_from_query subject_from_query prq' 
         [pid] prin_from_agreement).
destruct (eq_nat_dec action_from_query action_from_policy).
left; subst; exact H.
right; right; subst; exact H.
right; right; subst; exact H.
destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy].
simpl in H.
right; right; subst; exact H.

destruct pol as [primPol].
destruct primPol as [prq' pid action_from_policy].
simpl in H.
specialize H with action_from_query.
destruct (Peano_dec.eq_nat_dec action_from_query action_from_policy).
right; left; subst; exact H.
right; right; subst; exact H.
specialize H with action_from_query.
right; right; subst; exact H.
(*
set (asset_from_agreement := (get_Asset_From_Agreement agr)).
set (prin_u := (get_Prin_From_Agreement agr)).
*)
Qed.

Theorem ActIsInAndAssetIsTheSameImpliesUnregulated_dec:
  forall (sq:single_query),

if (act_in_agreement_dec (get_Sq_Action sq) (get_Sq_Agreement sq))
then
 if (eq_nat_dec (get_Sq_Asset sq) (get_Asset_From_Agreement (get_Sq_Agreement sq)))
 then
   True 
(* True to delay this case to later: 
   replace with more if/else and PermittedOrNotPermittedOrUnregulated*)
 else
   (trans_agr_implies_Unregulated (get_Sq_Agreement sq)
     (get_Sq_Env sq) (get_Sq_Subject sq) 
     (get_Sq_Action sq) (get_Sq_Asset sq))
else
   if (eq_nat_dec (get_Sq_Asset sq) (get_Asset_From_Agreement (get_Sq_Agreement sq)))
 then
      (trans_agr_implies_Unregulated (get_Sq_Agreement sq)
     (get_Sq_Env sq) (get_Sq_Subject sq) 
     (get_Sq_Action sq) (get_Sq_Asset sq))

 else
      (trans_agr_implies_Unregulated (get_Sq_Agreement sq)
     (get_Sq_Env sq) (get_Sq_Subject sq) 
     (get_Sq_Action sq) (get_Sq_Asset sq)).

Proof.
intros sq. simpl.

destruct sq as 
 [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
destruct (act_in_agreement_dec action_from_query agr).
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
destruct (eq_nat_dec asset_from_query asset_from_agreement).
auto.
destruct ps as [prim_policySet]. 
 
intros H.
simpl in H.
destruct H as [H1 H2].
specialize H1 with asset_from_query action_from_query subject_from_query.

apply H1. left. assumption.
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
destruct (eq_nat_dec asset_from_query asset_from_agreement).
destruct ps as [prim_policySet]. simpl.
intros H.
destruct H as [H1 H2].
specialize H1 with asset_from_query action_from_query subject_from_query.
apply H1. right. simpl in n. assumption.

destruct ps as [prim_policySet]. simpl.
intros H.
destruct H as [H1 H2].
specialize H1 with asset_from_query action_from_query subject_from_query.
apply H1. right. simpl in n. assumption.

Defined.


Theorem Agreement_dec:
  forall (sq:single_query),
     (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
        PermittedOrNotPermittedOrUnregulated sq).
Proof.
intros sq.
destruct sq as 
 [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.

destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
destruct ps as [prim_policySet]. simpl. 

intros H.
destruct H as [H1 H2].
specialize H1 with asset_from_query action_from_query subject_from_query.














Theorem PermNotOrUnregulated:
  forall (sq:single_query),
if (act_in_agreement_dec (get_Sq_Action sq) (get_Sq_Agreement sq))
then
 if (eq_nat_dec (get_Sq_Asset sq) (get_Asset_From_Agreement (get_Sq_Agreement sq)))
 then
  if (trans_prin_dec (get_Sq_Subject sq)
		    (get_Prin_From_Agreement ((get_Sq_Agreement sq))))
  then (* prin *)
   if (trans_preRequisite_dec (get_Sq_Env sq) (get_Sq_Subject sq)
          (get_preRequisite_From_policySet 
             (get_PS_From_Agreement (get_Sq_Agreement sq)))
          (get_IDs_From_policySet 
             (get_PS_From_Agreement (get_Sq_Agreement sq)))
          (get_Prin_From_Agreement (get_Sq_Agreement sq)))
   then (* prin /\ prq *)
    if (trans_preRequisite_dec (get_Sq_Env sq) (get_Sq_Subject sq)
          (get_policy_preRequisite_From_policySet
             (get_PS_From_Agreement (get_Sq_Agreement sq)))
          (get_IDs_From_policySet 
             (get_PS_From_Agreement (get_Sq_Agreement sq)))
          (get_Prin_From_Agreement (get_Sq_Agreement sq)))
    then (* prin /\ prq /\ prq' *)
      (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
       (Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq)))
    else (* prin /\ prq /\ ~prq' *)
      (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
       (Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq)))
   else (* prin /\ ~prq *)
     (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
      (Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq)))
  else (* ~prin *)
   ((trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (~Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))) \/
   (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))))
 else (* asset from query is not the same as the asset from the agreement *)
  (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq)))
else (* the action from query is not in the agreement *)
 (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) -> 
   (Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))).

Proof.
destruct sq as [agr subject_from_query action_from_query asset_from_query env_from_query]. simpl.
destruct (act_in_agreement_dec action_from_query agr).
destruct agr as [prin_from_agreement asset_from_agreement ps]. simpl.
destruct (eq_nat_dec asset_from_query asset_from_agreement).
destruct (trans_prin_dec subject_from_query prin_from_agreement). simpl. 
destruct (trans_preRequisite_dec env_from_query subject_from_query
     (get_preRequisite_From_policySet ps) (get_IDs_From_policySet ps) prin_from_agreement). simpl.
destruct (trans_preRequisite_dec env_from_query subject_from_query
     (get_policy_preRequisite_From_policySet ps) (get_IDs_From_policySet ps)
     prin_from_agreement). 

induction ps. intros K. simpl in K. 
destruct K as [K1 K2].

specialize K1 with asset_from_query action_from_query subject_from_query.



induction p. destruct p. 
specialize K2 with subject_from_query.
destruct K2 as [H1 H2]. simpl in H1. 
assert (
pose (proof_of_trans_policy_positive := H1 t).

specialize H2 with subject_from_query.
destruct H2 as [H21 H22]. 
induction p0 in H21. simpl in H21. destruct p1 in H21.
destruct H21 as [HA HB HC]. split. assumption. simpl in t0. simpl in t1.
destruct p0. destruct p0. simpl in t0. 
(*
destruct (eq_nat_dec p4 p3). subst. assumption.
*)
induction p. simpl. auto. simpl. induction c as [princ | count | count_by_prin]. simpl.
induction princ. simpl. 
destruct (eq_nat_dec subject_from_query x). assumption.


intros. destruct H as [H1 H2].
specialize H2 with subject_from_query.
destruct H2 as [H21 H22]. unfold not in H22.



Theorem PermNotOrUnregulated:
  forall (sq:single_query),
((~trans_prin (get_Sq_Subject sq)
	      (get_Prin_From_Agreement ((get_Sq_Agreement sq))))
/\ ((get_Sq_Asset sq) = (get_Asset_From_Agreement (get_Sq_Agreement sq)))
/\ (is_act_in_policySet (get_Sq_Action sq) (get_PS_From_Agreement (get_Sq_Agreement sq))))

->
((trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (~Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))) \/
(trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (Unregulated (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq)))).

Proof.
intros. destruct H. destruct H0. unfold trans_agreement. 
destruct sq as [agr subjet_from_query action_from_query asset_from_query e]. simpl.
destruct agr as [pr asset_from_agreement ps]. simpl.
simpl in H0. simpl in H1.
induction ps as [primPS | andPS]. right. unfold trans_ps. intros. 
destruct H2. 
destruct primPS as [primIPS|primEPS]. 
destruct primIPS as [prq pol].
specialize H3 with subjet_from_query.
destruct H3 as [H31 H32].
unfold trans_policy_unregulated in H32.
destruct pol. simpl in H32.

unfold not in H32. subst.

simpl in H. destruct p as [preq id actionFromPrimPolicy] in H32. 
apply H32.
unfold trans_policy_positive in H31. simpl in H31.

unfold not in H32. left. elimtype False. 
contradiction. simpl. auto. right. unfold not. simpl. exact H1.
specialize H2 with s a0 s. 

(* induction p1.  *)
simpl in H.
apply notTransImpliesUnregulated with (t:= (trans_preRequisite e s p0 (getId p1) p)) in H.
apply H3 in H. rewrite H0. induction p1.
apply ifActMentionedInPSWithOneAct with (ac1:= a0) (ac2:=a2)(prq:=p1)(id:=p2) in H1. subst.

unfold trans_policy_unregulated in H. destruct H. exact H.
unfold trans_policy_unregulated in H. destruct H. exact H.




compute in subjectNotInPrin. simpl in subjectNotInPrin. intuition.
unfold trans_policy_unregulated in H3.







(*******)
right. intros.
unfold trans_agreement in H0.
destruct sq. destruct a.
subst.
simpl. red in H0.

induction p0 in H0.
unfold trans_ps in H0.
(* specialize (H0 (get_Sq_Subject (SingletonQuery (Agreement p a p0) s a0 a1 e))). *)
pose proof (H0 s) as Hke.

destruct Hke as [H1 H2]. intuition.



simpl in H1. induction p2 in H1.

unfold trans_policy_unregulated in H1.

destruct H1. destruct H2. specialize H6 with a0. specialize H2 with a1.

assert (a0=a2). assert (a1=a).




Theorem PermOrNot:
  forall (sq:single_query),
if (trans_prin_dec (get_Sq_Subject sq)
		    (get_Prin_From_Agreement ((get_Sq_Agreement sq))))

then
((trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))) \/
 (trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (~Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))))
else
(trans_agreement (get_Sq_Env sq) (get_Sq_Agreement sq) ->
    (~Permitted (get_Sq_Subject sq) (get_Sq_Action sq) (get_Sq_Asset sq))).
Proof.
intros. left. unfold trans_agreement. destruct sq. destruct a. simpl.
unfold trans_ps. induction p0.
intros.
specialize (H s). assert (H': trans_prin s p /\ trans_preRequisite e s p0 (getId p1) p).
induction p0. unfold trans_preRequisite. induction p1.
apply and_comm.
split. apply I.
destruct (trans_prin_dec s p). exact t.
split in H.

apply trans_prin_dec.  split. apply trans_prin_True. apply I.
split. apply trans_prin_True.
unfold trans_preRequisite. unfold trans_constraint.
induction c. apply trans_prin_True.
unfold getId. induction p1.


destruct (le_lt_dec (trans_count_aux e (process_two_lists [p1] p)) n). subst.


Abort.
(*
unfold trans_policy_positive in H.


unfold trans_agreement in H. red in H. destruct sq in H. destruct a in H.
unfold trans_ps in H. induction p0 in H.
specialize (H s). simpl in H.

 inversion sq.

*)

Hypothesis e_is_consistent: forall (e:environment), env_consistent e.



Theorem allQueriesWillGetAnAnswer:
		forall (sq:single_query),
   let myagre := (get_Sq_Agreement sq) in
   let myenv := (get_Sq_Env sq) in
   let mysubj := (get_Sq_Subject sq) in
   let myact := (get_Sq_Action sq) in
   let myasset := (get_Sq_Asset sq) in
   let thePrin := (get_Prin_From_Agreement myagre) in
   let theAsset := (get_Asset_From_Agreement myagre) in
((is_subject_in_prin mysubj thePrin) /\
 ((get_Asset_From_Agreement myagre=get_Sq_Asset sq))) ->
(
(permissionGranted myenv [myagre] mysubj myact myasset) \/
(permissionDenied  myenv [myagre] mysubj myact myasset) \/
(queryInconsistent myenv [myagre] mysubj myact myasset) \/
(permissionUnregulated myenv [myagre] mysubj myact myasset)).

Proof. intros. left. split. induction myagre. right. split.



destruct H as [H1 H2]. apply H1. split.
destruct H as [H1 H2]. subst myasset. unfold get_Asset_From_Agreement in H2. symmetry.
exact H2. simpl.



induction p0. red. induction p0.

(**** SO FAR SO GOOD ****)

simpl. destruct p1. simpl. unfold isPrqAndPrq'_evalid2. simpl. split. apply I.
unfold trans_preRequisite.
induction p0.
apply I.
unfold trans_constraint.
induction c.
unfold trans_prin.
destruct p0.
(** Here we go again: we cannot really prove
mysubj = s

this is like proving x=y forall x and y...

So should I just assume I have the proof for 'trans_prin mysubj p0'?

**)
destruct H as [H1 H2].
(**** SO FAR SO GOOD 2 ****)

(*
intros.
firstorder.

cbv beta. red.
unfold getSplus.
unfold getPrqAndTheRestTuple.
cbv beta.

red.








symmetry. subst. rewrite <- H2.


apply subject_in_prin_dec.

induction p. unfold is_subject_in_prin.
*)
(** Using eq_nat_dec instead of dec_eq_nat simply for understanding purposes otherwise
they are equivalent **)
(*
elim (eq_nat_dec mysubj x).

intro h. exact h.
*)

(****** IGNORE THE REST: I am stuck at proving subgoal: mysubj <> x -> mysubj = x





intro.

generalize (eq_nat_dec mysubj x). intro h. contradiction. intro. subst.

intuition. auto.



apply
P_neq_a.

 intro h. elim h.

intro. exact H.

intro. intuition. destruct H. auto.



intro.
apply e_is_consistent.

specialize e_is_consistent with (1:=myenv).

intro. elim H. intuition.


induction f.

destruct (e_is_consistent (fun myenv => env_consistent myenv)).
apply e_is_consistent.

inversion myagre.

 auto. simpl. unfold is_fplus_single_query_evalid. induction sq.
*****)
Abort.
End ZZZ.

Section May2015.

(*

a constraint can be built 3 ways in ODRL0:

Inductive constraint : Set :=
  | Principal : prin  -> constraint
  | Count : nat -> constraint
  | CountByPrin : prin -> nat -> constraint.

In all three cases we conjecture that [[cons]] => [[preRequisite]]
*)

(*
Theorem prq_is_evalid : forall (e:environment),
		forall (agr: agreement),
		forall (s:subject),
		forall (action:act),
		forall (a:asset),

trans_constraint e s cons IDs prin_u -> trans_preRequisite e s prq IDs prin_u.

*)
















End May2015.


End ODRL.
