Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

#[local]
Existing Instance BoolEq.pair_eqb_spec.

#[global, program]
Instance listInfinite : listInfiniteFunRec_gen XList.
Next Obligation.
(* TODO: we need to analyze all while/for cycles
   and find upper bound for number of iterations *)
exact (repeat PhantomPoint 0).
Defined.

Notation rec := LocalStateLRecord.

Definition computed : LocalStateLRecord := Eval vm_compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 

Definition VMStateDefault : VMStateLRecord  := Eval vm_compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval vm_compute in default. 

Elpi Accumulate rec_def lp:{{
  get_rec {{ rec }}.
  get_def {{ def }}.
}}.

(* *********************************************************************************************** *)

Lemma exec_if_lift: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  exec_state f (if b then x else y) = if b then exec_state f x else exec_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma exec_if_lift2: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  exec_state f (xBoolIfElse b x y) = if b then exec_state f x else exec_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma eval_if_lift: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  eval_state f (if b then x else y) = if b then eval_state f x else eval_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma eval_if_lift2: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  eval_state f (xBoolIfElse b x y) = if b then eval_state f x else eval_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma toValue_if_lift: forall X (b: bool) (x y: ControlResult X false), 
  toValue (if b then x else y) = if b then toValue x else toValue y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma toValue_if_lift2: forall X (b: bool) (x y: ControlResult X false), 
  toValue (xBoolIfElse b x y) = if b then toValue x else toValue y.
Proof.
  intros.
  destruct b; auto.
Qed.

Tactic Notation "lift_all" := (repeat  (rewrite exec_if_lift || rewrite exec_if_lift2 ||
             rewrite eval_if_lift || rewrite eval_if_lift2 ||
             rewrite toValue_if_lift || rewrite  toValue_if_lift2)).

Tactic Notation "lift_all" "in" hyp(H) := (repeat  (rewrite exec_if_lift in H || rewrite exec_if_lift2 in H||
             rewrite eval_if_lift in H || rewrite eval_if_lift2 in H ||
             rewrite toValue_if_lift in H || rewrite  toValue_if_lift2 in H)).             

Lemma buint2 : forall n (v1 v: XUBInteger n) (T11 T12: _ -> Type) T2 f w w1, 
    ((let 'Build_XUBInteger a as a'' := v
    return T11 a'' -> T2 in
    fun _: T11 a'' => (let 'Build_XUBInteger b as b'' := v1
    return T12 b''-> T2 in fun _ : T12 b'' => f b a) w) w1) = 
    f (uint2N v1) (uint2N v).
Proof.    
  intros.
  destruct v, v1. auto.
Qed.  

Lemma buint1 : forall n (v: XUBInteger n) (T11: _ -> Type) T2 f w, 
(let 'Build_XUBInteger a as a'' := v
return T11 a'' -> T2 in
fun _: T11 a'' => f a) w = 
f (uint2N v).
Proof.
intros.
destruct v. auto.
Qed.

Lemma buint0 : forall X n (v: XUBInteger n) (f : _ -> X), 
match v with 
 | Build_XUBInteger x => f x
 end = f (uint2N v) .
Proof.
intros.
destruct v. auto.
Qed.

Tactic Notation "buint_all" := (repeat (rewrite buint2 || rewrite buint1 || rewrite buint0)).

Tactic Notation "buint_all" "in" hyp(H) := (repeat (rewrite buint2 in H || rewrite buint1 in H || rewrite buint0 in H)).


Check fold_left.

Definition hmapSum {K} (m: mapping K N) := 
match m with 
| wrap _ l => fold_left (fun s x => snd x + s) l 0
end.

Search fold_left.

Lemma fold_left_addable: forall X (l: Datatypes.list X) a (f: X -> N ),
      fold_left (fun s x => f x + s) l a = a + fold_left (fun s x => f x + s) l 0.
Proof.
  intros. generalize dependent a.
  induction l; intros.
  - simpl. lia.
  - simpl. rewrite IHl. symmetry.
  rewrite IHl. lia.
Qed.

Check BoolEq.eqb_spec.

Import ListNotations.

Lemma hmapSumDelete: forall {K}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (m: mapping K N) k, 
keysDistinct m ->
hmapSum m = m [k] + hmapSum (deleteListPair k m).
Proof.
intros.
destruct m. induction l.
- auto.
- unfold Common.hmapFindWithDefault. unfold hmapLookup.
  simpl. destruct a. simpl. remember (eqb k k0).
  case_eq y; intros.
  + simpl. rewrite fold_left_addable.
  setoid_rewrite IHl.  
  rewrite lookup_none_find. unfold Datatypes.id. simpl default. 
  unfold hmapSum. simpl. lia.
  rewrite <- keysDistinct_cons_lookup_none with (t:=n). auto.
  destruct H0. rewrite H2 in Heqy. symmetry in Heqy.
  apply eqb_spec_intro in Heqy. rewrite Heqy. assumption.
  enough (keysDistinct_list ((([ (k0, n) ])%list ++ l))%list).
  apply keysDistinct_app in H3.
  tauto. apply H1.
  + simpl. rewrite fold_left_addable.
    symmetry. rewrite fold_left_addable.
    setoid_rewrite IHl.
    unfold Common.hmapFindWithDefault. unfold hmapLookup.
    simpl. lia.
    enough (keysDistinct_list ((([ (k0, n) ])%list ++ l))%list).
    apply keysDistinct_app in H3.
    tauto. apply H1.
Qed.


Lemma hmapSumEqual: forall {K}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (m1 m2: mapping K N), keysDistinct m1 -> keysDistinct m2 -> (forall k, m1[k] = m2[k]) -> 
hmapSum m1 = hmapSum m2.
Proof.
intros.
destruct m1, m2.
generalize dependent l0.
induction l; intros.
- simpl. simpl in H3. unfold Common.hmapFindWithDefault at 1 in H3.
  simpl in H3. induction l0.
  + auto.
  + simpl. rewrite fold_left_addable.
    rewrite <- IHl0.
    enough (snd a = 0). lia. 
    pose proof (H3 (fst a)).
    unfold Common.hmapFindWithDefault in H4.
    simpl in H4. unfold hmapLookup in H4.
    simpl in H4. destruct H0.
    replace (eqb (fst a) (fst a)) with true in H4.
    simpl in H4. auto. symmetry.
    apply eqb_spec_intro. auto.
    enough (keysDistinct_list ((([ a ])%list ++ l0))%list).
    apply keysDistinct_app in H4.
    tauto. apply H2. intros.    
    unfold Common.hmapFindWithDefault in H3.
    simpl in H3. unfold hmapLookup in H3.
    simpl in H3. pose proof (H3 k).
    remember (eqb k (fst a)).
    case_eq y; intros.
    * rewrite H5 in H4. simpl in H4.
      rewrite lookup_none_find. auto.
      rewrite <- keysDistinct_cons_lookup_none with (t:=snd a). auto.
      destruct a. simpl. simpl in Heqy. 
      rewrite H5 in Heqy. symmetry in Heqy. 
      destruct H0.
      apply eqb_spec_intro in Heqy. rewrite Heqy.
      assumption.
    * rewrite H5 in H4. setoid_rewrite <- H4. auto.
- remember (deleteListPair (fst a) (wrap Map l0)).
  enough (forall k : K, (wrap Map l) [k] = l1 [k]).      
  enough (hmapSum (wrap Map (a :: l)) = snd a + hmapSum (wrap Map l)).
  rewrite H5. destruct l1. rewrite IHl with (l0:=l1).
  rewrite Heql1. symmetry.
  rewrite hmapSumDelete with (k:=fst a).
  pose proof (H3 (fst a)).
  simpl in H6.  unfold Common.hmapFindWithDefault in H6.
  unfold hmapLookup in H6.
  simpl in H6. replace (eqb (fst a) (fst a)) with true in H6.
  simpl in H6. setoid_rewrite <- H6.
  auto.
  destruct H0. symmetry. apply eqb_spec_intro. auto.
  assumption.
  enough (keysDistinct_list ((([ a ])%list ++ l))%list).
  apply keysDistinct_app in H6.
  tauto. apply H1.
  rewrite Heql1. apply delete_kd. assumption.
  assumption.
  simpl. rewrite fold_left_addable. lia.
  intros. rewrite Heql1.
  remember (eqb k (fst a)).
  case_eq y; intros.
  + rewrite H4 in Heqy. symmetry in Heqy.
    destruct H0. apply eqb_spec_intro in Heqy.
    rewrite ?lookup_none_find. auto. rewrite Heqy.
    rewrite lookup_delete_none. auto.
    erewrite <- keysDistinct_cons_lookup_none with (t:=snd a). auto.
    destruct a. simpl. rewrite Heqy. apply H1.
  + remember ((wrap Map l0) [k]?). pose proof (H3 k).
    unfold Common.hmapFindWithDefault in H5.
    unfold hmapLookup in H5. simpl in H5.
    rewrite H4 in Heqy. rewrite <- Heqy in H5.
    unfold Common.hmapFindWithDefault.
    rewrite lookup_delete_another.  
    assumption.
    unfold not. intros.
    symmetry in H6. destruct H0. apply eqb_spec_intro in H6.
    rewrite H6 in Heqy.
    discriminate.
    Unshelve. split; assumption.
Qed.

Lemma hmapSumGE: forall {K}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (m: mapping K N) k, 
(* keysDistinct m -> *)
hmapSum m >= m[k].
Proof.
    intros.
    destruct m.

    induction l.
    - unfold Common.hmapFindWithDefault. simpl. lia.
    - simpl. rewrite fold_left_addable.
      match goal with
      | IHl: ?x >= ?y |- _ => remember x; remember y
      end.
      setoid_rewrite <- Heqn. 
      unfold Common.hmapFindWithDefault. 
      unfold hmapLookup.
      simpl.
      remember (eqb k (fst a)).
      destruct y.
      + simpl. unfold Datatypes.id. lia.
      + setoid_rewrite <- Heqn0. lia.
Qed.


Lemma hmapSumAdjust: forall {K}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (m: mapping K N) k a, 
keysDistinct m ->
hmapSum (m[k] ← a) = a + hmapSum m - m[k].
Proof.
intros. rewrite hmapSumDelete with (k:=k).
symmetry. rewrite hmapSumDelete with (k:=k).
symmetry.
rewrite lookup_some_find with (v:=a).
(* remember (deleteListPair k m). *)
rewrite delete_insert. lia.
rewrite lookup_addAdjust with (v:=a). auto.
assumption.
apply insert_kd.
assumption.
Qed.

Require Import FinProof.Lib.Tactics.

Definition mapBN2N {K} {n} (m: mapping K (XUBInteger n)) := 
match m with 
    | wrap _ l => (wrap Map (List.map (fun x => let 'Build_XUBInteger n := snd x in (fst x, n)) l))
end.

Definition hmapBSum {K} {n} (m: mapping K (XUBInteger n)) := 
    @Build_XUBInteger n of hmapSum (mapBN2N m).

Lemma mapBN2N_keys: forall {K} {n} (m: mapping K (XUBInteger n)),
    xHMapKeys m = xHMapKeys (mapBN2N m).
Proof. 
    intros.
    destruct m.
    induction l; auto.
    simpl.
    destruct a. destruct x. simpl.
    setoid_rewrite IHl. auto.
Qed.

Lemma keysDistinct_ignores_values2 : forall K V1 V2  (m1: listMap K V1) 
                                                    (m2: listMap K V2),
  xHMapKeys m1 = xHMapKeys m2 -> keysDistinct m1 -> keysDistinct m2.
Proof.
  destruct m1 as [m1]. destruct m2 as [m2].
  generalize dependent m2.
  induction m1.
  - intros. unfoldHMap xHMapKeys in H. unfoldHMap xHMapEmpty in H.
    unfoldList xListMap in H. inversion H.
    symmetry in H2. apply map_eq_nil in H2. subst. constructor.
  - intros. unfoldHMap xHMapKeys in H. unfoldList xListMap in H.
    simpl in H. destruct m2. discriminate.
    simpl in H. inversion H. destruct a, p. simpl in H2. subst.
    constructor. apply IHm1. auto. inversion H0. auto.
    inversion H0. unfoldHMap xHMapKeys in H6. unfoldHMap xHMapKeys.
    unfoldList xListMap. unfoldList xListMap in H6. 
    simpl. rewrite <- H3. auto.
Qed.


Lemma mapBN2N_keysDistinct: forall {K} {n} (m: mapping K (XUBInteger n)),
    keysDistinct m -> keysDistinct (mapBN2N m).
Proof.
    intros.
    apply keysDistinct_ignores_values2 with (m1:=m).
    rewrite mapBN2N_keys. auto.
    assumption.
Qed.

(* Import ListNotations.
Transparent addAdjustListPair. *)
Lemma mapBN2N_addAdjust: forall K`{XBoolEquable bool K}`{BoolEq.eqb_spec K} n (m: mapping K (XUBInteger n)) k a,
    keysDistinct m ->
    mapBN2N (m[k]← a) = 
    (mapBN2N m) [k] ← (uint2N a).
Proof.
    intros.
    destruct m.
    induction l.
    - simpl. destruct a. auto.
    - destruct a. simpl.
    unfold addAdjustListPair.
    simpl.
    destruct a0.
    destruct x. simpl.
    remember (eqb k k0).
    destruct y.
    + simpl.
    erewrite 2keysDistinct_addAdjustListPair__true.
    auto.
    all: cycle 1.
    symmetry in Heqy. rewrite BoolEq.eqb_spec_intro in Heqy.
    rewrite Heqy.
    apply H1.
    apply mapBN2N_keysDistinct in H1.
    simpl in H1.
    symmetry in Heqy. rewrite BoolEq.eqb_spec_intro in Heqy.
    rewrite Heqy.
    apply H1.
    + simpl.
    remember ((wrap Map l) [k]← (Build_XUBInteger n0)).
    destruct y. unfold xHMapInsert in Heqy0.
    simpl in Heqy0. unfold addAdjustListPair in Heqy0.
    inversion Heqy0. rewrite <- H3.
    unfold mapBN2N in IHl.
    f_equal. f_equal.
    About wrap.
    match goal with
    | |- ?x = ?y => enough (wrap Map x = wrap Map y)
    end.
    inversion H2. auto.
    rewrite IHl.
    unfold xHMapInsert. simpl.
    unfold addAdjustListPair. simpl. auto.
    enough (keysDistinct_list ((([ (k0, Build_XUBInteger n1)  ])%list ++ l))%list).
    apply keysDistinct_app in H2.
    tauto. apply H1.
Qed.    

(* Transparent Common.hmapFindWithDefault. *)

Lemma mapBN2N_hmapLookup: forall K`{XBoolEquable bool K}`{BoolEq.eqb_spec K} 
                           n (m: mapping K (XUBInteger n)) k,    
    (mapBN2N m) [k] = uint2N (m[k]).
Proof.
    intros.    
    destruct m.
    induction l; auto.
    simpl. destruct a. destruct x. simpl.
    unfold Common.hmapFindWithDefault.
    simpl. unfold hmapLookup.
    simpl.
    remember (eqb k k0).
    destruct y.
    - simpl. auto. 
    - auto.
Qed.    


Lemma mapBN2N_hmapLookup2: forall K`{XBoolEquable bool K}`{BoolEq.eqb_spec K} 
                           n (m: mapping K (XUBInteger n)) k,    
    ((mapBN2N m) [k] ?)  = xMaybeMap uint2N (m[k]?) .
Proof.
    intros.    
    destruct m.
    induction l; auto.
    simpl. destruct a. destruct x. simpl.
    (* unfold Common.hmapFindWithDefault. *)
    simpl. unfold hmapLookup.
    simpl.
    remember (eqb k k0).
    destruct y.
    - simpl. auto. 
    - auto.
Qed.  





















Check (* FinProof.MonadTransformers21. *)TransEmbedded.    
Check LedgerLEmbeddedType.
Print ContractFields.

Check (@TransEmbedded _ _ _ (LedgerLEmbeddedType rec Ledger_MainState) 
                            (ContractLEmbeddedType _decimals) ).


Definition mappingProj {K V}`{XBoolEquable bool K}`{XDefault V} (k: K) (m: mapping K V) : V := m[k].
Definition mappingInj {K V}`{XBoolEquable bool K} (k: K) (v: V) (m: mapping K V) : mapping K V :=  m[k] ← v.

Check projinj.

Transparent Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Lemma mappingProjInj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K}`{XDefault V}  (k: K) (v: V) (m: mapping K V), 
                      mappingProj k (mappingInj k v m) = v.
Proof.
  intros.
  unfold mappingInj, mappingProj.
  rewrite lookup_some_find with (v:=v). auto.
  unshelve erewrite lookup_addAdjust with (k:=k). auto.
Qed.

Lemma mappingInjProj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K}`{XDefault V} (k: K) (m: mapping K V), 
keysDistinct m ->
mappingInj k (mappingProj k m) m = m.
Proof.
  intros.
  unfold mappingInj, mappingProj.  
  - case_eq (m [k] ?); intros.
  + rewrite lookup_some_find with (v:=v).
    (* rewrite lookup_some_find with (v:=v). *)
    unfold xHMapInsert. simpl. destruct m.
    apply member_addAdjust. assumption. assumption. assumption.
  + admit.
Admitted.  

Check injinj.

Lemma mappingInjInj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K) (v1 v2: V) (m: mapping K V), 
(* keysDistinct m -> *)
mappingInj k v1 (mappingInj k v2 m) = mappingInj k v1 m.
Proof.
  intros.
  unfold mappingInj.  
  rewrite insert_insert. auto.
Qed.

Obligation Tactic := intros.

#[global]
Program Instance mapping_embedded: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K}`{XDefault V} (k: K),
EmbeddedType (mapping K V) V | 0.
Next Obligation.
apply mappingProj. exact k. exact X.
Defined.
Next Obligation.
apply mappingInj. exact k. exact X. exact X0.
Defined.
Next Obligation.
unfold mapping_embedded_obligation_1, mapping_embedded_obligation_2.
apply mappingProjInj.
Defined.
Next Obligation.
unfold mapping_embedded_obligation_1, mapping_embedded_obligation_2.
apply mappingInjProj.
admit.
Admitted.
Next Obligation.
unfold mapping_embedded_obligation_1, mapping_embedded_obligation_2.
apply mappingInjInj.
Defined.
Fail Next Obligation.


(* Definition mappingProj {K V}`{XBoolEquable bool K} (k: K) (m: mapping K V) : option V := m[k]?.
Definition mappingInj {K V}`{XBoolEquable bool K} (k: K) (ov: option V) (m: mapping K V) : mapping K V := 
match ov with 
| None => deleteListPair k m
| Some v => m[k] ← v
end.

Check projinj.

Transparent Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Lemma mappingProjInj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K) (ov: option V) (m: mapping K V), 
                      mappingProj k (mappingInj k ov m) = ov.
Proof.
  intros.
  unfold mappingInj, mappingProj.
  destruct ov.
  - unshelve erewrite lookup_addAdjust with (k:=k). auto.
  - unshelve erewrite lookup_delete_none with (k:=k). auto.
Qed.


Lemma mappingInjProj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K) (m: mapping K V), 
keysDistinct m ->
mappingInj k (mappingProj k m) m = m.
Proof.
  intros.
  unfold mappingInj, mappingProj.  
  - case_eq (m [k] ?); intros.
  + destruct m.
    apply member_addAdjust. assumption. assumption.
  + unfold deleteListPair. rewrite delete_not_member_list.
    destruct m. auto. assumption. 
Qed.  

Check injinj.

Lemma mappingInjInj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K) (ov1 ov2: option V) (m: mapping K V), 
(* keysDistinct m -> *)
mappingInj k ov1 (mappingInj k ov2 m) = mappingInj k ov1 m.
Proof.
  intros.
  unfold mappingInj.
  destruct ov1, ov2.
  - rewrite insert_insert. auto.
  - remember (m[k]?).
    destruct y.
    + admit.
    + unfold deleteListPair. rewrite delete_not_member_list.
      auto. auto.
  - unfold xHMapInsert. simpl.
    rewrite delete_insert. auto.
  - rewrite delete_not_member. auto.
    rewrite lookup_delete_none.
    auto.
Admitted. *)

(* Obligation Tactic := intros.

#[global]
Program Instance mapping_embedded: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K),
EmbeddedType (mapping K V) (option V).
Next Obligation.
apply mappingProj. exact k. exact X.
Defined.
Next Obligation.
apply mappingInj. exact k. exact X. exact X0.
Defined.
Next Obligation.
unfold mapping_embedded_obligation_1, mapping_embedded_obligation_2.
apply mappingProjInj.
Defined.
Next Obligation.
unfold mapping_embedded_obligation_1, mapping_embedded_obligation_2.
apply mappingInjProj.
admit.
Admitted.
Next Obligation.
unfold mapping_embedded_obligation_1, mapping_embedded_obligation_2.
apply mappingInjInj.
Defined.
Fail Next Obligation.

Definition mappingOptProj {K V}`{XBoolEquable bool K} (k: K) (om: option (mapping K V)) : option V := 
match om with
| Some m => m[k]?
| None => None
end.

Definition mappingOptInj {K V}`{XBoolEquable bool K} (k: K) (ov: option V) (om: option (mapping K V)) : option (mapping K V) := 
match ov, om with 
| None, None => None
| None, Some m => Some (deleteListPair k m)
| Some v, None => (* Some (default[k] ← v) *) None
| Some v, Some m => Some (m[k] ← v)
end.

Lemma mappingOptProjInj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K) (ov: option V) (om: option(mapping K V)), 
                      mappingOptProj k (mappingOptInj k ov om) = ov.
Proof.
  intros.
  unfold mappingOptInj, mappingOptProj.
  destruct ov, om.
  - unshelve erewrite lookup_addAdjust with (k:=k). auto.
  - unshelve erewrite lookup_addAdjust with (k:=k). auto.
  - unshelve erewrite lookup_delete_none with (k:=k). auto.
  - auto.
Qed.

Lemma mappingOptInjProj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K) (om: option(mapping K V)), 
(match om with
 | None => True
 | Some m => keysDistinct m
end) ->
mappingOptInj k (mappingOptProj k om) om = om.
Proof.
  intros.
  unfold mappingOptInj, mappingOptProj. 
  destruct om; [|auto].
  - case_eq (x [k] ?); intros.
  + f_equal. destruct x.
    apply member_addAdjust. assumption. assumption.
  + f_equal. unfold deleteListPair. rewrite delete_not_member_list.
    destruct x. auto. assumption. 
  (* - exfalso. assumption.   *)
Qed.  

Lemma mappinOptgInjInj: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K) (ov1 ov2: option V) 
  (om: option(mapping K V)), 
(* keysDistinct m -> *)
mappingOptInj k ov1 (mappingOptInj k ov2 om) = mappingOptInj k ov1 om.
Proof.
  intros.
  unfold mappingOptInj.
  destruct ov1, ov2, om; auto.
  - rewrite insert_insert. auto.
  - f_equal. rewrite insert_insert. auto.
  - f_equal. remember (x[k]?).
    destruct y.
    + admit.
    + unfold deleteListPair. rewrite delete_not_member_list.
      auto. auto.
  - f_equal. unfold xHMapInsert. simpl.
    rewrite delete_insert. auto.
  - f_equal. unfold xHMapInsert. simpl.
    rewrite delete_insert. auto.
  - f_equal. rewrite delete_not_member. auto.
    rewrite lookup_delete_none.
    auto.
Admitted.

#[global]
Program Instance opt_mapping_embedded: forall {K V}`{XBoolEquable bool K}`{BoolEq.eqb_spec K} (k: K),
EmbeddedType (option(mapping K V)) (option V).
Next Obligation.
apply mappingOptProj. exact k. exact X.
Defined.
Next Obligation.
apply mappingOptInj. exact k. exact X. exact X0.
Defined.
Next Obligation.
unfold opt_mapping_embedded_obligation_1, opt_mapping_embedded_obligation_2.
apply mappingOptProjInj.
Defined.
Next Obligation.
unfold opt_mapping_embedded_obligation_1, opt_mapping_embedded_obligation_2.
apply mappingOptInjProj.
admit.
Admitted.
Next Obligation.
unfold mapping_embedded_obligation_1, mapping_embedded_obligation_2.
apply mappingInjInj.
Defined.
Fail Next Obligation. *)

Notation "':>' f , g" := (@TransEmbedded _ _ _ (_ f: EmbeddedType _ _) (_ g: EmbeddedType _ _)) (at level 20, only parsing).
Notation "':>' 'μ' f , g" := (@TransEmbedded _ _ _ (mapping_embedded f: EmbeddedType _ _) (_ g: EmbeddedType _ _)) (at level 20, only parsing).
Notation "':>' f , 'μ' g" := (@TransEmbedded _ _ _ (_ f: EmbeddedType _ _) (mapping_embedded g: EmbeddedType _ _)) (at level 20, only parsing).
Notation "':>' 'μ' f , 'μ' g" := (@TransEmbedded _ _ _ (mapping_embedded f: EmbeddedType _ _) (mapping_embedded g: EmbeddedType _ _)) (at level 20, only parsing).

Notation "v '-->' r 'with' et":= (@injEmbed _ _ et v r) (at level 22, only parsing).
Notation "'<--' r 'with' et":= (@projEmbed _ _ et r) (at level 22, only parsing).

Check :> Ledger_VMState , :> VMState_ι_msg_sender , add_std_ι_address.

Check default --> (_:LedgerLRecord rec) with :> Ledger_VMState , :> VMState_ι_msg_sender , add_std_ι_address.
Compute field_type add_std_ι_address.
Check ((<-- (_:LedgerLRecord rec) with :> Ledger_VMState , :> VMState_ι_msg_sender , add_std_ι_address) : field_type add_std_ι_address) : uint256.

Check 5: uint256.
Check (0%Z, 8: uint256): address.
Check mapping_embedded  ((0%Z, 8: uint256): address).
(* Check :> _balances , ((0%Z, 8: uint256): address). *)
Check ((5:uint256)) --> (_:LedgerLRecord rec) 
      with :> Ledger_MainState , :> _balances , ((0%Z, 8: uint256): address).

Compute ((5:uint256)) --> (default:LedgerLRecord rec) 
      with :> Ledger_MainState , :> _balances , ((0%Z, 8: uint256): address).      

Set Typeclasses Debug.
Unset Typeclasses Iterative Deepening.

Check _ _allowed: EmbeddedType _ _.
Print ContractLEmbeddedType.
Check _ _allowed: EmbeddedType _ (field_type _allowed).

Check TransEmbedded. 
Arguments TransEmbedded {S} {T} {U} & _ _.

Check @TransEmbedded ContractLRecord _ _ (_ _allowed: EmbeddedType _ _)   (mapping_embedded (_:address)).
Check  :> Ledger_MainState, :> _allowed , :> μ (_: address) , μ (_: address).      


Notation "l :: f , g <-- v" := (@injEmbed _ _ (@TransEmbedded _ _ _ (_ f: EmbeddedType _ _) (_ g: EmbeddedType _ _)) v l) (at level 20, only parsing).
Notation "l :: 'μ' f , g <-- v" := (@injEmbed _ _ (@TransEmbedded _ _ _ (mapping_embedded f: EmbeddedType _ _) (_ g: EmbeddedType _ _)) v l) (at level 20, only parsing).
Notation "l :: f , 'μ' g <-- v" := (@injEmbed _ _ (@TransEmbedded _ _ _ (_ f: EmbeddedType _ _) (mapping_embedded g: EmbeddedType _ _)) v l) (at level 20, only parsing).
Notation "l :: 'μ' f , 'μ' g <-- v" := (@injEmbed _ _ (@TransEmbedded _ _ _ (mapping_embedded f: EmbeddedType _ _) (mapping_embedded g: EmbeddedType _ _)) v l) (at level 20, only parsing).

(* Notation "v '-->' r 'with' et":= (@injEmbed _ _ et v r) (at level 22, only parsing). *)
Notation "'<--' r 'with' et":= (@projEmbed _ _ et r) (at level 22, only parsing).

Check (default:LedgerLRecord rec) :: Ledger_MainState , _allowed <-- _.

Compute (4:uint256) --> 
      ((5:uint256) --> (default:LedgerLRecord rec) 
      with :> Ledger_MainState , :> _allowed , :> μ ((0%Z, 8: uint256): address), μ ((0%Z, 8: uint256): address)) 
      with :> Ledger_MainState , :> _allowed , :> μ ((0%Z, 7: uint256): address), μ ((0%Z, 6: uint256): address).      

(* Check :> Ledger_MainState , 
              :> _allowed , (_: address).  *)     

(* Check ((5:uint256) ) --> (_:LedgerLRecord rec) 
      with :> Ledger_MainState , 
              :> _allowed ,               
                  :> ((0%Z, 8: uint256): address), ((0%Z, 8: uint256): address).    *)   