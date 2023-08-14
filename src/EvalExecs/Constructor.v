Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UMLang.ExecGenerator.

Require Import EIP20.
Require Import Common.
Require Import Templates.Constructor.
Import EIP20.


Definition constructor_ls_template_exec_sig (_initialAmount :  uint256) 
                                (_tokenName :  string) 
                                (_decimalUnits :  uint8) 
                                (_tokenSymbol :  string) (l : LedgerLRecord rec) :
  {t | t = exec_state (Uinterpreter (@constructor_ls_template rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l}.
  unfold constructor_ls_template. unfold dynamicAssignL. unfold fromUReturnExpression.
  repeat auto_build_P listInfinite.
Defined.

Definition constructor_ls_template_exec (_initialAmount :  uint256) 
                                (_tokenName :  string) 
                                (_decimalUnits :  uint8) 
                                (_tokenSymbol :  string) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @constructor_ls_template_exec_sig (constructor_ls_template_exec_sig _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Defined.

Lemma constructor_ls_template_exec_prf: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string) (l : LedgerLRecord rec),
  constructor_ls_template_exec _initialAmount _tokenName _decimalUnits _tokenSymbol l = 
  exec_state (Uinterpreter (@constructor_ls_template rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l.
Proof.
  intros.
  proof_of_2 constructor_ls_template_exec constructor_ls_template_exec_sig 
             (constructor_ls_template_exec_sig _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Qed.

Definition constructor_ls_pre_payload_computed' 
                              (_initialAmount :  uint256) 
                              (_tokenName :  string) 
                              (_decimalUnits :  uint8) 
                              (_tokenSymbol :  string)
                              (l: LedgerLRecord rec): True.
    assert (LedgerLRecord rec).
    remember (constructor_ls_template_exec _initialAmount _tokenName _decimalUnits _tokenSymbol 
              {$$ l with Ledger_LocalState := default $$}) as exec.
    destruct_ledger l. 

    time "constructor_ls_template_exec unfold" unfold constructor_ls_template_exec in Heqexec. idtac.
    
    time "remember" match goal with
    | Heql0 : exec = ?L |- _ => match L with
                                | context [exec_state (Uinterpreter (constructor_ls_payload rec def _ _ _ _ )) ?LL] => 
                                        remember LL as pre_exec
                                end
    end. idtac.

    time "constructor_ls_pre_payload_computed compute" vm_compute in Heqpre_exec. idtac.
    match goal with
    | Heql0: pre_exec = ?LL |- _ => transparent_abstract exact_no_check LL using constructor_ls_pre_payload_computed_curried
    end.
    exact I.
Defined.

Definition constructor_ls_pre_payload_computed
                              (_initialAmount :  uint256) 
                              (_tokenName :  string) 
                              (_decimalUnits :  uint8) 
                              (_tokenSymbol :  string)
                              (l: LedgerLRecord rec): LedgerLRecord rec.     
remember l as ledger. destruct_ledger l.
refine (uncurry (f:=_GlobalClass) (constructor_ls_pre_payload_computed_curried _initialAmount _tokenName _decimalUnits _tokenSymbol )
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

About constructor_ls_payload.

Lemma constructor_ls_template_by_payload: 
                       forall (_initialAmount_value :  uint256) 
                              (_tokenName_value :  string) 
                              (_decimalUnits_value :  uint8) 
                              (_tokenSymbol_value :  string)
                              (l: LedgerLRecord rec), 
  let _initialAmount: ULValue uint256 := local_left_field _ _ _ ("_initialAmount", 1%nat) in
  let _tokenName: ULValue string := local_left_field _ _ _ ("_tokenName", 1%nat) in
  let _decimalUnits: ULValue uint8 := local_left_field _ _ _ ("_decimalUnits", 1%nat) in
  let _tokenSymbol: ULValue string := local_left_field _ _ _ ("_tokenSymbol", 1%nat) in  
  let pre_exec := constructor_ls_pre_payload_computed _initialAmount_value _tokenName_value _decimalUnits_value _tokenSymbol_value l in  

  constructor_ls_template_exec _initialAmount_value _tokenName_value _decimalUnits_value _tokenSymbol_value 
                               {$$ l with Ledger_LocalState := default $$} =
  exec_state (Uinterpreter (@constructor_ls_payload rec def _initialAmount _tokenName _decimalUnits _tokenSymbol)) pre_exec.
Proof.
  intros.
  destruct_ledger l.
  time "constructor_ls_template_exec unfold" unfold constructor_ls_template_exec. idtac.  
  time "remember" match goal with
    | |- context [exec_state (Uinterpreter (constructor_ls_payload rec def ?a1 ?a2 ?a3 ?a4 )) ?LL] => 
                                        remember LL as pre_exec' 
  end. idtac.

  time "constructor_ls_pre_payload_computed compute" vm_compute in Heqpre_exec'. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (constructor_ls_payload rec def ?a1 ?a2 ?a3 ?a4 )) ?LL] => 
                                      remember a1 as u1
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (constructor_ls_payload rec def ?a1 ?a2 ?a3 ?a4 )) ?LL] => 
                                        remember a2 as u2
  
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (constructor_ls_payload rec def ?a1 ?a2 ?a3 ?a4 )) ?LL] => 
                                      remember a3 as u3
  end. idtac.

  time "remember" match goal with
  | |- context [exec_state (Uinterpreter (constructor_ls_payload rec def ?a1 ?a2 ?a3 ?a4 )) ?LL] => 
                                      remember a4 as u4
  end. idtac.  

  
  assert (u1 = _initialAmount) as H1 by auto.
  assert (u2 = _tokenName) as H2.
  subst u2 u1. auto.
  assert (u3 = _decimalUnits) as H3.
  subst u3 u2 u1. auto.
  assert (u4 = _tokenSymbol) as H4.
  subst u4 u3 u2 u1. auto.
  
  rewrite H1, H2, H3, H4. 
  f_equal. auto.  
Qed.


(* payload *)

Definition constructor_ls_payload_exec_sig (_initialAmount : ULValue uint256) 
                                           (_tokenName : ULValue string) 
                                           (_decimalUnits : ULValue uint8) 
                                           (_tokenSymbol : ULValue string)
                                           (l : LedgerLRecord rec):
           {t | t = exec_state (Uinterpreter (@constructor_ls_payload rec def _initialAmount _tokenName _decimalUnits _tokenSymbol)) l}.
  unfold constructor_ls_payload. 
  repeat auto_build_P listInfinite.
Defined.

Definition constructor_ls_payload_exec (_initialAmount : ULValue uint256) 
                                       (_tokenName : ULValue string) 
                                       (_decimalUnits : ULValue uint8) 
                                       (_tokenSymbol : ULValue string)
                                       (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2_fast @constructor_ls_payload_exec_sig (constructor_ls_payload_exec_sig _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Defined.

Lemma constructor_ls_payload_prf : forall (_initialAmount : ULValue uint256) 
                                          (_tokenName : ULValue string) 
                                          (_decimalUnits : ULValue uint8) 
                                          (_tokenSymbol : ULValue string)
                                          (l : LedgerLRecord rec) ,
      constructor_ls_payload_exec _initialAmount _tokenName _decimalUnits _tokenSymbol l = 
      exec_state (Uinterpreter (@constructor_ls_payload rec def _initialAmount _tokenName _decimalUnits _tokenSymbol)) l.
Proof. 
  intros.     
  proof_of_2 constructor_ls_payload_exec constructor_ls_payload_exec_sig (constructor_ls_payload_exec_sig _initialAmount _tokenName _decimalUnits _tokenSymbol l).
Qed.

Tactic Notation "lift_all" "in" hyp(H) := (repeat  
(rewrite exec_if_lift in H || 
 rewrite eval_if_lift in H || 
 rewrite toValue_if_lift in H )). 

Opaque Common.hmapFindWithDefault
       CommonInstances.addAdjustListPair
       N.add N.sub N.leb N.ltb N.eqb Z.eqb N.pow.

Definition constructor_ls_payload_exec_computed' (_initialAmount_value :  uint256)
                                                 (_tokenName_value :  string)
                                                 (_decimalUnits_value :  uint8)
                                                 (_tokenSymbol_value :  string)
                                                 (l: LedgerLRecord rec): True.  
  assert (LedgerLRecord rec).
  remember (local_left_field _ _ _ ("_initialAmount", 1%nat): ULValue uint256) as _initialAmount.
  remember (local_left_field _ _ _ ("_tokenName", 1%nat): ULValue string) as _tokenName.
  remember (local_left_field _ _ _ ("_decimalUnits", 1%nat): ULValue uint8) as _decimalUnits.
  remember (local_left_field _ _ _ ("_tokenSymbol", 1%nat): ULValue string) as _tokenSymbol.
  
  remember (constructor_ls_pre_payload_computed _initialAmount_value _tokenName_value _decimalUnits_value _tokenSymbol_value l) as pre_exec.
  remember (constructor_ls_payload_exec _initialAmount _tokenName _decimalUnits _tokenSymbol pre_exec) as exec.

  destruct_ledger l.

  time "constructor_ls_payload_exec unfold" unfold constructor_ls_payload_exec in Heqexec. 
  time "constructor_ls_pre_payload_computed unfold" unfold constructor_ls_pre_payload_computed in Heqpre_exec.

  unfold xBoolIfElse in Heqexec.
  unfold boolFunRec in Heqexec. idtac.  
  subst pre_exec _initialAmount _tokenName _decimalUnits _tokenSymbol. idtac.

  time "lift" lift_all in Heqexec. idtac.
  time "compute" compute in Heqexec. idtac.
  time "buint" buint_all in Heqexec. idtac.
   
  (* symmetry in Heql1. idtac. *)     
  match goal with
  | Heql1: exec = ?LL |- _ => 
    transparent_abstract exact_no_check LL using constructor_ls_payload_exec_computed_curried
  end.
  exact I.
Defined.

Check constructor_ls_payload_exec_computed_curried.
About constructor_ls_payload_exec_computed_curried.
(* mapping address uint256 ->
       mapping address (mapping address uint256) ->
       ContractLRecord ->
       MessagesAndEventsLRecord ->
       MessagesAndEventsLRecord ->
       uint256 ->
       uint256 ->
       uint32 ->
       uint64 ->
       uint256 ->
       address ->
       uint128 ->
       uint128 ->
       address ->
       cell_ ->
       slice_ ->
       boolean ->
       uint128 ->
       cell_ ->
       boolean ->
       boolean ->
       Datatypes.list TracingTree -> uint32 -> rec *)


Definition constructor_ls_payload_exec_computed
                              (_initialAmount:  uint256)
                              (_tokenName:  string)
                              (_decimalUnits:  uint8)
                              (_tokenSymbol:  string)
                              (l: LedgerLRecord rec): LedgerLRecord rec.
remember l as ledger. destruct_ledger l.
refine (uncurry (f:=_GlobalClass) (constructor_ls_payload_exec_computed_curried _initialAmount _tokenName _decimalUnits _tokenSymbol)
      (s, (s0, (* (s1, (s2, (s3, (s4, *)
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
                       l1)))))))))))))))))))))))%xprod).
Defined.


Lemma constructor_ls_payload_exec_computed_correct: forall (_initialAmount_value :  uint256)
                                                           (_tokenName_value :  string)
                                                           (_decimalUnits_value :  uint8)
                                                           (_tokenSymbol_value :  string)
                                                           (l: LedgerLRecord rec),
  let _initialAmount := local_left_field _ _ _ ("_initialAmount", 1%nat) in
  let _tokenName := local_left_field _ _ _ ("_tokenName", 1%nat) in
  let _decimalUnits := local_left_field _ _ _ ("_decimalUnits", 1%nat) in
  let _tokenSymbol := local_left_field _ _ _ ("_tokenSymbol", 1%nat) in  
  let pre_exec := constructor_ls_pre_payload_computed _initialAmount_value _tokenName_value _decimalUnits_value _tokenSymbol_value l in
      constructor_ls_payload_exec_computed _initialAmount_value _tokenName_value _decimalUnits_value _tokenSymbol_value l = 
      constructor_ls_payload_exec _initialAmount _tokenName _decimalUnits _tokenSymbol pre_exec.
Proof.
  intros.
  
  remember (constructor_ls_payload_exec  _initialAmount _tokenName _decimalUnits _tokenSymbol pre_exec) as exec.
  destruct_ledger l.  

  time "constructor_ls_payload_exec unfold" unfold constructor_ls_payload_exec in Heqexec.
  time "constructor_ls_pre_payload_computed unfold" unfold constructor_ls_pre_payload_computed in pre_exec.

  unfold xBoolIfElse in Heqexec.
  unfold boolFunRec in Heqexec. idtac.

  unfold constructor_ls_pre_payload_computed in pre_exec.  
  subst pre_exec _initialAmount _tokenName _decimalUnits _tokenSymbol. idtac.

  time "lift" lift_all in Heqexec. idtac.
  time "compute" compute in Heqexec. idtac.
  time "buint" buint_all in Heqexec. idtac.
  
  auto.
Qed. 


Lemma constructor_exec_computed: forall
                            (_initialAmount:  uint256)
                            (_tokenName:  string)
                            (_decimalUnits:  uint8)
                            (_tokenSymbol:  string)
                            (l: LedgerLRecord rec), 
      exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol))  
                               {$$ l with Ledger_LocalState := default $$} =
      constructor_ls_payload_exec_computed _initialAmount _tokenName _decimalUnits _tokenSymbol l. 
Proof.
  intros.
  rewrite constructor_ls_template_exec_correct.
  rewrite constructor_ls_payload_exec_computed_correct.
  rewrite constructor_ls_payload_prf.

  rewrite <- (constructor_ls_template_by_payload _initialAmount _tokenName _decimalUnits
     _tokenSymbol l).

  (* pose proof (constructor_ls_template_by_payload _initialAmount _tokenName _decimalUnits
     _tokenSymbol l).
  cbv zeta in H. rewrite <- H.   
  rewrite <- constructor_ls_template_by_payload. *)

  rewrite constructor_ls_template_exec_prf.
  reflexivity.
Qed.


