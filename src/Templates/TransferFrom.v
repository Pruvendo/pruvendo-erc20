Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UMLang.ExecGenerator.

Require Import EIP20.
Require Import Common.
Require Import UrsusProofs.
Import EIP20.

(* Set Mangle Names. *)
(* Set Mangle Names Prefix "TF". *)

Tactic Notation "destruct_ledger"  constr(ll) :=
    (
    let c := fresh "c" in
    let c0 := fresh "c" in
    let m := fresh "m" in
    let m0 := fresh "m" in
    let v := fresh "v" in
    let l := fresh "l" in
    let l0 := fresh "l" in
    let v0 := fresh "v" in
    let v1 := fresh "v" in
    let v2 := fresh "v" in
    let v3 := fresh "v" in
    let v4 := fresh "v" in
    let v5 := fresh "v" in
    let v6 := fresh "v" in
    let v7 := fresh "v" in
    let v8 := fresh "v" in
    let v9 := fresh "v" in
    let v10 := fresh "v" in
    let v11 := fresh "v" in
    let v12 := fresh "v" in
    let v13 := fresh "v" in
    let v14 := fresh "v" in
    let v15 := fresh "v" in
    let v16 := fresh "v" in
    let v17 := fresh "v" in

    let s0 := fresh "s" in
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    let s3 := fresh "s" in
    let s4 := fresh "s" in
    let s5 := fresh "s" in

    destruct ll as [c p]; destruct p as [c0 p];
    destruct p as [m p]; destruct p as [m0 p];
    destruct p as [v p]; destruct p as [l l0];

    destruct v as [v0 p]; destruct p as [v1 p]; 
    destruct p as [v2 p]; destruct p as [v3 p]; 
    destruct p as [v4 p]; destruct p as [v5 p]; 
    destruct p as [v6 p]; destruct p as [v7 p]; 
    destruct p as [v8 p]; destruct p as [v9 p]; 
    destruct p as [v10 p]; destruct p as [v11 p]; 
    destruct p as [v12 p]; destruct p as [v13 p]; 
    destruct p as [v14 p]; destruct p as [v15 p]; 
    destruct p as [v16 v17];

    destruct c as [s0 p]; destruct p as [s1 p];
    destruct p as [s2 p]; destruct p as [s3 p];
    destruct p as [s4 s5]).


Lemma transferFrom_ls_template_exec_correct_helper: forall l l' (u: URValue _ false),
    l.(Ledger_MainState) = l'.(Ledger_MainState) ->
    l.(Ledger_VMState) = l'.(Ledger_VMState) ->
    eval_state (sRReader u) l = eval_state (sRReader u) l' ->
    (forall l, (exec_state (sRReader u) l).(Ledger_MainState) = l.(Ledger_MainState)) ->
    eval_state (sRReader (URIndex \\ msg->sender \\ (URIndex u (allowed_right rec def)))) l = 
    eval_state (sRReader (URIndex \\ msg->sender \\ (URIndex u (allowed_right rec def)))) l'.
Proof.
  intros. destruct_ledger l. destruct_ledger l'.  

  compute in H. compute in H0.
  inversion H. subst s s0 s1 s2 s3 s4. 
  inversion H0. subst v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17.
  clear H H0.

  assert (forall X (c1: ControlResult X false) c2,
          toValue c1 = toValue c2 -> c1 = c2 ).
  -
    intros. 
    dependent destruction c2; dependent destruction c3.
    compute in H. congruence.
  -
    apply H.
    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    symmetry.
    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    
    unfold msg_sender. unfold wrapURValue.
    unfold SML_NG32.wrapURValue.
    erewrite <- ?R_state_exec_P_helper.

    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    symmetry.
    erewrite <- R_index_eval_false_P_helper; [|reflexivity|reflexivity|reflexivity].
    rewrite H1.

    f_equal. f_equal. f_equal.

    match goal with
    | |- context [eval_state _ (exec_state _ ?l) = 
                  eval_state _ (exec_state _ ?l1)]
        => remember l; remember l1
    end.

    pose proof (H2 x).
    pose proof (H2 x0).
    remember (exec_state (sRReader u) x).
    remember (exec_state (sRReader u) x0).
    setoid_rewrite <- Heqx1 in H0.
    setoid_rewrite <- Heqx2 in H3.
    setoid_rewrite <- Heqx1.
    setoid_rewrite <- Heqx2.

    destruct_ledger x1. destruct_ledger x2.
        
    subst x0 x.
    compute in H0, H3.

    inversion H0.
    subst s s0 s1 s2 s3 s4.

    inversion H3.
    subst s11 s12 s13 s14 s15 s16.
    auto.
Qed.

Lemma transferFrom_ls_template_exec_correct: forall (_from :  address)
                                                    (_to :  address) 
                                                    (_value :  uint256) 
                                                    (l : LedgerLRecord rec),
      exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l = 
      exec_state (Uinterpreter (@transferFrom_ls_template rec def _ _ _ _  _from _to _value)) l.
Proof.
  intros.
  unfold transferFrom.
  unfold transferFrom_ls_template.
  unfold transferFrom_ls_payload.
  unfold fromUReturnExpression.

  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.
  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.
  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.
  eapply remove_first_assigment; intros.
  eapply remove_first_expression; intros.

  unfold dynamicAssignL.
  
  match goal with
  | |- context [@DynamicBinding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  ?f] => remember f
  end.
  symmetry.
  match goal with
  | |- context [@DynamicBinding _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _  ?f] => remember f
  end.

  match goal with
  | |- context [ // {?u1} ; {?u2} //  ] => remember u1; remember u2
  end.
  symmetry.
  match goal with
  | |- context [ // {?u1} ; {?u2} //  ] => remember u1
  end.

  apply remove_second_expression with  (u1:=u2) (u2:=u3) (u3:=u1); intros.
  
  all: subst u3 u1 u u0.
  1: erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  1: erewrite <- E_dynamic_binding_exec_P_helper; [|reflexivity|reflexivity|reflexivity].
  2: erewrite <- E_dynamic_binding_err_P_helper; [|reflexivity|reflexivity|reflexivity].
  2: erewrite <- E_dynamic_binding_err_P_helper; [|reflexivity|reflexivity|reflexivity].
  
  all: remember (eval_state (SML_NG32.new_lvalue "allowance") l4).  
  all: symmetry.
  all: match goal with
  | |- context [ // {?x} ; {?y} := {?a} ; {?z} // ] => remember a; remember z
  end.
  all: remember (exec_state (SML_NG32.new_lvalue "allowance") l4).
  
  1: apply double_assigment_exec with 
           (lv := u) 
           (u := u1) (y:=u0) (l:=l5).
  6: f_equal; apply double_assigment_eval with 
           (lv := u) 
           (u := u1) (y:=u0) (l:=l5).

  1,6: refine LocalStateField0.
  1,5: refine ubint_default.
  1,4: auto.
  1,3: ( intros ; subst u0 lv; destruct_ledger l6; auto ).        
  all: (intros; subst u u0 lv;
        remember ((eval_state (new_lvalue "_from") l1)) ;
        apply transferFrom_ls_template_exec_correct_helper ).
  all: try now destruct_ledger l5.

  Opaque Common._hmapFindWithDefault _addAdjustListPair.

  all: now (destruct_ledger l5; destruct_ledger l;
  compute; repeat destruct l5 ; repeat destruct l6 ). 
  
  Transparent Common._hmapFindWithDefault _addAdjustListPair.  
Qed.