Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UMLang.ExecGenerator.


Require Import Common.
Require Import EIP20.
Import EIP20.


Definition var_test3_exec_sig (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) :
                               {t | t = exec_state (Uinterpreter (@var_test3 rec def _ arg1 arg2 arg3 arg4 arg5 arg6 )) l}.
  unfold var_test3. unfold dynamicAssignL.  unfold fromUReturnExpression.
  repeat auto_build_P listInfinite.
Defined.

Definition var_test3_exec_let (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  time "var3 let_term" let_term_of_2_fast @var_test3_exec_sig (var_test3_exec_sig arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Definition var_test3_exec (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @var_test3_exec_let (var_test3_exec_let arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Definition var_test3_prf (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) :
  var_test3_exec arg1 arg2 arg3 arg4 arg5 arg6 l = 
  exec_state (Uinterpreter (@var_test3 rec def _ arg1 arg2 arg3 arg4 arg5 arg6 )) l.
  time "var3 proof" proof_of_2 var_test3_exec var_test3_exec_sig (var_test3_exec_sig arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Tactic Notation "lift_all" "in" hyp(H) := (repeat  
(rewrite exec_if_lift in H || 
 rewrite eval_if_lift in H || 
 rewrite toValue_if_lift in H )). 


Opaque var_test2.
Definition var_test3_exec_computed: forall (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256)
                            (l: LedgerLRecord rec), 
                            {t: LedgerLRecord rec | t = var_test3_exec arg1 arg2 arg3 arg4 arg5 arg6 {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (var_test3_exec arg1 arg2 arg3 arg4 arg5 arg6 {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p. idtac.

    time "var3 unfold" unfold var_test3_exec in Heql0.

    unfold xBoolIfElse in Heql0.
    unfold boolFunRec in Heql0. idtac.

    time "remember" match goal with
    | Heql0 : l0 = ?L |- _ => match L with
                         | context [exec_state (Uinterpreter (var_test2 rec def)) ?LL] => remember LL
                         end
    end.

    time "var3 compute" vm_compute in Heql3. idtac.    

    subst l3.

    (* time "var3 buit_all" buint_all in Heql0. *)
    symmetry in Heql0. idtac.
    (* time "var3 compute" compute in Heql0. *)
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.






Definition var_test4_exec_sig (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) :
                               {t | t = exec_state (Uinterpreter (@var_test4 rec def _ arg1 arg2 arg3 arg4 arg5 arg6 )) l}.
  unfold var_test4. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition var_test4_exec_let (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  time "var4 let_term" let_term_of_2_fast @var_test4_exec_sig (var_test4_exec_sig arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Definition var_test4_exec (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @var_test4_exec_let (var_test4_exec_let arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Definition var_test4_prf (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) :
  var_test4_exec arg1 arg2 arg3 arg4 arg5 arg6 l = 
  exec_state (Uinterpreter (@var_test4 rec def _ arg1 arg2 arg3 arg4 arg5 arg6 )) l.
  time "var4 proof" proof_of_2 var_test4_exec var_test4_exec_sig (var_test4_exec_sig arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Definition var_test4_exec_computed: forall (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256)
                            (l: LedgerLRecord rec), 
                            {t: LedgerLRecord rec | t = var_test4_exec arg1 arg2 arg3 arg4 arg5 arg6 {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (var_test4_exec arg1 arg2 arg3 arg4 arg5 arg6 {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p. idtac.

    time "var4 unfold" unfold var_test4_exec in Heql0.
    time "var4 lift_all" lift_all in Heql0.    
    time "var4 compute" compute in Heql0.
    time "var4 buit_all" buint_all in Heql0.
    symmetry in Heql0. idtac.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.


Definition var_test1_exec_sig (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) :
                                {t | t = exec_state (Uinterpreter (@var_test1 rec def _ arg1 arg2 arg3 arg4 arg5 arg6)) l}.
  unfold var_test1. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition var_test1_exec_let (arg1: uint256) (arg2: uint256) 
                              (arg3: uint256) (arg4: uint256)
                              (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  time "var1 let_term" let_term_of_2_fast @var_test1_exec_sig (var_test1_exec_sig arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Definition var_test1_exec (arg1: uint256) (arg2: uint256) 
                          (arg3: uint256) (arg4: uint256)
                          (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @var_test1_exec_let (var_test1_exec_let arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.

Definition var_test1_prf (arg1: uint256) (arg2: uint256) 
                        (arg3: uint256) (arg4: uint256)
                        (arg5: uint256) (arg6: uint256) (l : LedgerLRecord rec) :
  var_test1_exec arg1 arg2 arg3 arg4 arg5 arg6 l = 
  exec_state (Uinterpreter (@var_test1 rec def _ arg1 arg2 arg3 arg4 arg5 arg6)) l.
  time "var1 proof" proof_of_2 var_test1_exec var_test1_exec_sig (var_test1_exec_sig arg1 arg2 arg3 arg4 arg5 arg6 l).
Defined.


Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Definition var_test1_exec_computed: forall
                            (arg1: uint256) (arg2: uint256) 
                            (arg3: uint256) (arg4: uint256)
                            (arg5: uint256) (arg6: uint256)
                            (l: LedgerLRecord rec), 
                            {t: LedgerLRecord rec | t = var_test1_exec arg1 arg2 arg3 arg4 arg5 arg6 {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (var_test1_exec arg1 arg2 arg3 arg4 arg5 arg6 {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p. idtac.

    time "var1 unfold" unfold var_test1_exec in Heql0.
    time "var1 lift_all" lift_all in Heql0.    
    time "var1 compute" compute in Heql0.
    time "var1 buit_all" buint_all in Heql0.
    symmetry in Heql0. idtac.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.



Definition var_test2_exec_sig  (l : LedgerLRecord rec) :
                               {t | t = exec_state (Uinterpreter (@var_test2 rec def _ )) l}.
  unfold var_test2. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition var_test2_exec_let (l : LedgerLRecord rec) : LedgerLRecord rec.
  time "var2 let_term" let_term_of_2_fast @var_test2_exec_sig (var_test2_exec_sig l).
Defined.

Definition var_test2_exec (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @var_test2_exec_let (var_test2_exec_let l).
Defined.

Definition var_test2_prf (l : LedgerLRecord rec) :
  var_test2_exec l = 
  exec_state (Uinterpreter (@var_test2 rec def _ )) l.
  time "var2 proof" proof_of_2 var_test2_exec var_test2_exec_sig (var_test2_exec_sig l).
Defined.

Definition var_test2_exec_computed: forall
                            (l: LedgerLRecord rec), 
                            {t: LedgerLRecord rec | t = var_test2_exec  {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (var_test2_exec {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.
    destruct v. repeat destruct p.
    destruct c. repeat destruct p. idtac.

    time "var2 unfold" unfold var_test2_exec in Heql0.
    time "var2 lift_all" lift_all in Heql0.    
    time "var2 compute" compute in Heql0.
    time "var2 buit_all" buint_all in Heql0.
    symmetry in Heql0. idtac.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.



