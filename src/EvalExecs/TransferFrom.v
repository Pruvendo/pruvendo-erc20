Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UMLang.ExecGenerator.

Require Import EIP20.
Require Import Common.
Require Import Templates.TransferFrom.
Import EIP20.

Definition transferFrom_ls_template_exec_sig (_from :  address)
                                             (_to :  address)
                                             (_value :  uint256)
                                             (l : LedgerLRecord rec) :
           {t | t = exec_state (Uinterpreter (@transferFrom_ls_template rec def _ _ _ _ _from _to _value )) l}.
  unfold transferFrom_ls_template. unfold dynamicAssignL. unfold fromUReturnExpression.
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_ls_template_exec (_from :  address)
                                             (_to :  address)
                                             (_value :  uint256)
                                             (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @transferFrom_ls_template_exec_sig (transferFrom_ls_template_exec_sig _from _to _value l).
Defined.

Lemma transferFrom_ls_template_exec_prf : forall (_from :  address)
                                                 (_to :  address) 
                                                 (_value :  uint256) 
                                                 (l : LedgerLRecord rec),
  transferFrom_ls_template_exec _from _to _value l = 
  exec_state (Uinterpreter (@transferFrom_ls_template rec def _ _ _ _ _from _to _value)) l.
Proof.
  intros.  
  proof_of_2 transferFrom_ls_template_exec transferFrom_ls_template_exec_sig 
             (transferFrom_ls_template_exec_sig _from _to _value l).
Qed.

Definition transferFrom_ls_pre_payload_computed' 
                              (_from :  address)
                              (_to :  address) 
                              (_value :  uint256)
                              (l: LedgerLRecord rec): True.
    assert (LedgerLRecord rec).
    remember (transferFrom_ls_template_exec _from _to _value {$$ l with Ledger_LocalState := default $$}) as exec.
    destruct_ledger l.

    time "transferFrom_ls_template_exec unfold" unfold transferFrom_ls_template_exec in Heqexec. idtac.
    
    time "remember" match goal with
    | Heql0 : exec = ?L |- _ => match L with
                                | context [exec_state (Uinterpreter (transferFrom_ls_payload rec def _ _ _ _ _ )) ?LL] => 
                                        remember LL as pre_exec
                                end
    end. idtac.

    time "transferFrom_ls_pre_payload_computed compute" vm_compute in Heqpre_exec. idtac.
    match goal with
    | Heql0: pre_exec = ?LL |- _ => transparent_abstract exact_no_check LL using transferFrom_ls_pre_payload_computed_curried
    end.
    exact I.
Defined.


Definition transferFrom_ls_pre_payload_computed
                              (_from :  address)
                              (_to :  address) 
                              (_value :  uint256)
                              (l: LedgerLRecord rec): LedgerLRecord rec.     
remember l as ledger. destruct_ledger l.
Print transferFrom_ls_pre_payload_computed_curried.

refine (uncurry (f:=_GlobalClass) (transferFrom_ls_pre_payload_computed_curried _from _to _value)
      (s, (s0, (s1, (s2, (s3, (s4,
             (c0,
              (m,
               (m0,
                (v0,
                 (v1,
                  (v2,
                   (v3,
                    (v4,
                     (v5,
                      (v6,
                       (v7, (v8, (v9, (v10, (v11, (v12, (v13, (v14, (v15, (v16, (v17,
                       l1)))))))))))))))))))))))))))%xprod).
Defined.

About transferFrom_ls_payload.

Lemma transferFrom_ls_template_by_payload: 
                       forall (_from_value :  address)
                              (_to_value :  address) 
                              (_value_value :  uint256)
                              (l: LedgerLRecord rec), 
  let _from := local_left_field _ _ _ ("_from", 1%nat) in
  let _to := local_left_field _ _ _ ("_to", 1%nat) in
  let _value := local_left_field _ _ _ ("_value", 1%nat) in
  let _allowance := local_left_field _ _ _ ("allowance", 1%nat) in
  let _success := local_left_field _ _ _ ("success", 1%nat) in
  let pre_exec := transferFrom_ls_pre_payload_computed _from_value _to_value _value_value l in  

  transferFrom_ls_template_exec _from_value _to_value _value_value {$$ l with Ledger_LocalState := default $$} =
  exec_state (Uinterpreter (@transferFrom_ls_payload rec def _  _from _to _value _success _allowance)) pre_exec.
Proof.
  intros.
  destruct_ledger l.
  time "transferFrom_ls_template_exec unfold" unfold transferFrom_ls_template_exec. idtac.  
  time "remember" match goal with
    | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember LL as pre_exec' 
  end. idtac.

  time "transferFrom_ls_pre_payload_computed compute" vm_compute in Heqpre_exec'. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a1 as u1
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                        remember a2 as u2
  
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a3 as u3
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a4 as u4
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (transferFrom_ls_payload rec def ?a1 ?a2 ?a3 ?a4 ?a5 )) ?LL] => 
                                      remember a5 as u5
  end. idtac.

  assert (forall l, exec_state (sRReader (ULtoRValue u4)) l = l). 
  intros. subst u4. auto.
  rewrite H.

  assert (forall X (x:X) (b: bool), (if b then x else x) = x). intros; destruct b; auto.
  rewrite H0.

  assert (u1 = _from) as H1 by auto.
  assert (u2 = _to) as H2.
  subst u2 u1. auto.
  assert (u3 = _value) as H3.
  subst u3 u2 u1. auto.
  assert (u4 = _success ) as H4.
  subst u4 u3 u2 u1. auto.
  assert (u5 = _allowance) as H5.
  subst u5 u4 u3 u2 u1. auto.

  rewrite H1, H2, H3, H4, H5.   
  f_equal. auto.  
Qed.  

(* payload *)

Definition transferFrom_ls_payload_exec_sig (_from : ULValue address) 
                                            (_to : ULValue address) 
                                            (_value : ULValue uint256)
                                            (_success: ULValue boolean)
                                            (_allowance : ULValue uint256) 
                                            (l : LedgerLRecord rec):
           {t | t = exec_state (Uinterpreter (@transferFrom_ls_payload rec def _  _from _to _value _success _allowance)) l}.
  unfold transferFrom_ls_payload. 
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_ls_payload_exec (_from : ULValue address) 
                                        (_to : ULValue address) 
                                        (_value : ULValue uint256)
                                        (_success: ULValue boolean) 
                                        (_allowance : ULValue uint256)
                                        (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @transferFrom_ls_payload_exec_sig (transferFrom_ls_payload_exec_sig  _from _to _value _success _allowance l).
Defined.

Lemma transferFrom_ls_payload_prf : forall (_from : ULValue address) 
                                       (_to : ULValue address) 
                                       (_value : ULValue uint256)
                                       (_success: ULValue boolean) 
                                       (_allowance : ULValue uint256)
                                       (l : LedgerLRecord rec) ,
      transferFrom_ls_payload_exec _from _to _value  _success _allowance l = 
      exec_state (Uinterpreter (@transferFrom_ls_payload rec def _  _from _to _value _success _allowance)) l.
Proof. 
  intros.     
  proof_of_2 transferFrom_ls_payload_exec transferFrom_ls_payload_exec_sig (transferFrom_ls_payload_exec_sig _from _to _value _success _allowance l).
Qed.

Tactic Notation "lift_all" "in" hyp(H) := (repeat  
(rewrite exec_if_lift in H || 
 rewrite eval_if_lift in H || 
 rewrite toValue_if_lift in H )). 

Opaque Common.hmapFindWithDefault
       CommonInstances.addAdjustListPair
       N.add N.sub N.leb N.ltb N.eqb Z.eqb N.pow.

Definition transferFrom_ls_payload_exec_computed' (_from_value _to_value: address)
                                                  (_value_value : uint256)
                                                  (l: LedgerLRecord rec): True.  
  assert (LedgerLRecord rec).
  remember (local_left_field _ _ _ ("_from", 1%nat): ULValue address) as _from.
  remember (local_left_field _ _ _ ("_to", 1%nat): ULValue address) as _to.
  remember (local_left_field _ _ _ ("_value", 1%nat): ULValue uint256) as _value.
  remember (local_left_field _ _ _ ("success", 1%nat): ULValue boolean) as _success.
  remember (local_left_field _ _ _ ("allowance", 1%nat): ULValue uint256) as _allowance.
  remember (transferFrom_ls_pre_payload_computed _from_value _to_value _value_value l) as pre_exec.
  remember (transferFrom_ls_payload_exec  _from _to _value  _success _allowance pre_exec) as exec.

  destruct_ledger l.

  time "transferFrom_ls_payload_exec unfold" unfold transferFrom_ls_payload_exec in Heqexec. 
  time "transferFrom_ls_pre_payload_computed unfold" unfold transferFrom_ls_pre_payload_computed in Heqpre_exec.

  unfold xBoolIfElse in Heqexec.
  unfold boolFunRec in Heqexec. idtac.  
  subst pre_exec _from _to _value _success _allowance; idtac.

  time "lift" lift_all in Heqexec; idtac.
  time "compute" compute in Heqexec; idtac.
  time "buint" buint_all in Heqexec; idtac.
   
  (* symmetry in Heql1. idtac. *)     
  match goal with
  | Heql1: exec = ?LL |- _ => 
    transparent_abstract exact_no_check LL using transferFrom_ls_payload_exec_computed_curried
  end.
  exact I.
Defined.


Definition transferFrom_ls_payload_exec_computed
                              (_from :  address)
                              (_to :  address) 
                              (_value :  uint256)
                              (l: LedgerLRecord rec): LedgerLRecord rec.
remember l as ledger. destruct_ledger l.
refine (uncurry (f:=_GlobalClass) (transferFrom_ls_payload_exec_computed_curried _from _to _value)
      (s, (s0, (s1, (s2, (s3, (s4,
             (c0,
              (m,
               (m0,
                (v0,
                 (v1,
                  (v2,
                   (v3,
                    (v4,
                     (v5,
                      (v6,
                       (v7, (v8, (v9, (v10, (v11, (v12, (v13, (v14, (v15, (v16, (v17,
                       l1)))))))))))))))))))))))))))%xprod).
Defined.

Lemma transferFrom_ls_payload_exec_computed_correct: forall (_from_value _to_value: address)
                                                            (_value_value : uint256)
                                                            (l: LedgerLRecord rec),
  let _from := local_left_field _ _ _ ("_from", 1%nat) in
  let _to := local_left_field _ _ _ ("_to", 1%nat) in
  let _value := local_left_field _ _ _ ("_value", 1%nat) in
  let _success := local_left_field _ _ _ ("success", 1%nat) in
  let _allowance := local_left_field _ _ _ ("allowance", 1%nat) in  
  let pre_exec := transferFrom_ls_pre_payload_computed _from_value _to_value _value_value l in
      transferFrom_ls_payload_exec_computed _from_value _to_value _value_value l = 
      transferFrom_ls_payload_exec _from _to _value _success _allowance pre_exec.
Proof.
  intros.
  
  remember (transferFrom_ls_payload_exec  _from _to _value  _success _allowance pre_exec) as exec.
  destruct_ledger l.  

  time "transferFrom_ls_payload_exec unfold" unfold transferFrom_ls_payload_exec in Heqexec.
  time "transferFrom_ls_pre_payload_computed unfold" unfold transferFrom_ls_pre_payload_computed in pre_exec.

  unfold xBoolIfElse in Heqexec.
  unfold boolFunRec in Heqexec. idtac.

  unfold transferFrom_ls_pre_payload_computed in pre_exec.  
  subst pre_exec _from _to _value _success _allowance. idtac.

  time "lift" lift_all in Heqexec. idtac.
  time "compute" compute in Heqexec. idtac.
  time "buint" buint_all in Heqexec. idtac.
  
  auto.
Qed. 
     

(* Definition transferFrom_exec_sig (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l}.
  unfold transferFrom. unfold dynamicAssignL.  unfold fromUReturnExpression.
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_exec_let (_from :  address)
                             (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
Defined.

Definition transferFrom_exec (_from :  address)
                         (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @transferFrom_exec_let (transferFrom_exec_let _from _to _value l).
Defined.

Definition transferFrom_prf (_from :  address)
                         (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transferFrom_exec _from _to _value l = 
  exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l.
  proof_of_2 transferFrom_exec transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
Defined. *)

Lemma transferFrom_exec_computed: forall
                            (_from :  address)
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
      exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value))  {$$ l with Ledger_LocalState := default $$} =
      transferFrom_ls_payload_exec_computed _from _to _value l. 
Proof.
  intros.
  rewrite transferFrom_ls_template_exec_correct.
  rewrite transferFrom_ls_payload_exec_computed_correct.
  rewrite transferFrom_ls_payload_prf.
  rewrite <- transferFrom_ls_template_by_payload.
  rewrite transferFrom_ls_template_exec_prf.
  reflexivity.
Qed.


(* (* template left *)

(* Definition transferFromTemplate_exec_sig1 
                                 (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (@transferFromTemplate_left rec def _ _ _ _ false (URScalar _from) false (URScalar _to) false (URScalar _value) bool )) l}.
  unfold transferFromTemplate_left.
  unfold wrapULExpressionL.
  unfold wrapULExpression.
  unfold ursus_call_with_argsL.

  match goal with
  | |- context [@ursus_call_with_args ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 ?a13 ?a14 ?a15 ?a16 ?a17 ?a18 ?a19 ?a20] =>
            remember (@ursus_call_with_args a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20)
  end.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_1 in u.
  change (transferFromTemplate rec def) with (fun (_from _to : address) (_value : uint256) => transferFromTemplate rec def _from _to _value) in Hequ.
  Opaque transferFromTemplate.
  
  simpl in Hequ.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_4 in Hequ.  
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_4 in Hequ.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_5 in Hequ.
  unfold ursus_call_with_rargs0 in Hequ.
  simpl in Hequ.
  unfold simple_state_bind,  simple_state_unit in Hequ.
  unfold simple_state_run in Hequ.
  unfold compose in Hequ.
  unfold SML_NG32.UExpressionP0_LedgerableWithArgs_obligation_7 in Hequ.
  unfold sRReader in Hequ.
  simpl in Hequ.

  change Datatypes.list with XList.

  auto_build_P listInfinite.
  all: subst u.  
  1: refine (exist _ (exec_state (UinterpreterUnf listInfinite (transferFromTemplate rec def _from _to _value)) l) _).
  2: refine (exist _ (eval_state (UinterpreterUnf listInfinite (transferFromTemplate rec def _from _to _value)) l) _).

  all: remember (UinterpreterUnf listInfinite (transferFromTemplate rec def _from _to _value)) as ll.
  all: destruct ll.
  1: unfold exec_state.
  2: unfold eval_state.
  all: simpl.
  all: remember (x l) as xx.
  all: destruct xx. 
  all: simpl. 
  1: reflexivity.
  dependent destruction c; reflexivity.
Defined.



Definition transferFromTemplate_exec_sig2 
                                 (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (@transferFromTemplate_left rec def _ _ _ _ false (URScalar _from) false (URScalar _to) false (URScalar _value) bool )) l}.
remember (proj1_sig (transferFromTemplate_exec_sig1 _from _to _value l)).
pose proof (proj2_sig (transferFromTemplate_exec_sig1 _from _to _value l)).
unfold transferFromTemplate_exec_sig1 in Heql0, H.
setoid_rewrite <- Heql0 in H.
simpl in Heql0.

symmetry in Heql0.

match goal with 
| Heql0: ?L = l0 |- _ => refine (exist _ L _)
end.
rewrite Heql0.
assumption.
Defined.


Definition transferFromTemplate_exec_sig3
                                 (_from :  address)
                                 (_to :  address) 
                                 (_value :  uint256) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (@transferFromTemplate_left rec def _ _ _ _ false (URScalar _from) false (URScalar _to) false (URScalar _value) bool )) l}.
remember (proj1_sig (transferFromTemplate_exec_sig2 _from _to _value l)).
pose proof (proj2_sig (transferFromTemplate_exec_sig2 _from _to _value l)).
unfold transferFromTemplate_exec_sig2 in Heql0, H.
setoid_rewrite <- Heql0 in H.
simpl in Heql0.
Admitted. *)