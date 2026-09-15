From iris.algebra Require Import auth cmra ofe gmap gset local_updates.
From cryptis.core Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive state :=
  | Private (ts : gset term)
  | Public (t : term)
  | Invalid.

Section StateCmra.

  Context {SI : sidx}.

  Canonical Structure stateO := leibnizO state.

  #[global] Instance stateO_discrete : OfeDiscrete state.
  Proof. apply _. Qed.

  #[local] Instance state_op_instance : Op state := λ s1 s2,
    match s1, s2 with
    | Private ts1, Private ts2 => Private (ts1 ∪ ts2)
    | Private ts, Public t | Public t, Private ts =>
      if bool_decide (ts ⊆ {[ t ]}) then Public t else Invalid
    | Public t1, Public t2 =>
      if bool_decide (t1 = t2) then Public t1 else Invalid
    | _, _ => Invalid
    end.

  #[local] Instance state_pcore_instance : PCore state := Some.

  #[local] Instance state_valid_instance : Valid state := λ s,
    match s with
    | Invalid => False
    | _ => True
    end.

  #[local] Instance state_unit_instance : Unit state := Private ∅.

  Lemma state_ra_mixin : RAMixin state.
  Proof.
  split.
  - solve_proper.
  - naive_solver.
  - solve_proper.
  - intros [] [] [];
    rewrite /op /state_op_instance;
    repeat case_bool_decide;
    try (f_equiv; set_solver);
    try (exfalso; set_solver).
  - intros [] [];
    rewrite /op /state_op_instance;
    repeat case_bool_decide; simplify_eq;
    f_equiv; set_solver.
  - intros [] ? [= <-];
    rewrite /op /state_op_instance;
    repeat case_bool_decide; simplify_eq;
    f_equiv; set_solver.
  - by move=> [] [].
  - rewrite /pcore /state_pcore_instance.
    move=> ? ? ? ? H.
    apply Some_inj in H as ->; eauto.
  - by move=> [] [].
  Qed.

  Lemma state_ucmra_mixin : UcmraMixin state.
  Proof.
  split=> // s.
  change (ε ⋅ s) with (state_op_instance ε s).
  case: s => [ts|t|] //=.
  + f_equiv; set_solver.
  + case_bool_decide=> //; set_solver.
  Qed.

  Canonical Structure stateR := discreteR state state_ra_mixin.
  Canonical Structure stateUR := Ucmra state state_ucmra_mixin.

  #[global] Instance stateR_discrete : CmraDiscrete stateR.
  Proof. by split; first apply _. Qed.

  #[global] Instance state_core_id (st : state) : CoreId st.
  Proof. by constructor. Qed.

End StateCmra.

Section StateUpdates.

  Context {SI : sidx}.

  Lemma state_local_update_grow ts t :
  (● Private ts ⋅ ◯ Private ts, ● Private ts ⋅ ◯ Private ts) ~l~>
  (● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]}), ● Private (ts ∪ {[ t ]}) ⋅ ◯ Private (ts ∪ {[ t ]})).
  Proof.
  apply auth_local_update=> //. apply local_update_discrete.
  move=> mz Hval Heq; split; first done.
  case: mz Hval Heq=> [[ts1|t1|]|] //= Hval Heq.
  - change (Private ts ⋅ Private ts1) with (state_op_instance (Private ts) (Private ts1)) in Heq.
    change (Private (ts ∪ {[ t ]}) ⋅ Private ts1) with (state_op_instance (Private (ts ∪ {[ t ]})) (Private ts1)).
    simpl in *. f_equal. set_solver.
  - change (Private ts ⋅ Public t1) with (state_op_instance (Private ts) (Public t1)) in Heq.
    simpl in Heq.
    by case_bool_decide.
  Qed.

  Lemma state_local_update_lock t :
    (● Private {[ t ]} ⋅ ◯ Private {[ t ]}, ● Private {[ t ]} ⋅ ◯ Private {[ t ]}) ~l~>
    (● Public t ⋅ ◯ Public t, ● Public t ⋅ ◯ Public t).
  Proof.
  apply auth_local_update=> //. apply local_update_discrete.
  move=> mz Hval Heq; split; first done.
  case: mz Hval Heq=> [[ts1|t1|]|] //= Hval Heq.
  - change (Private {[ t ]} ⋅ Private ts1) with (state_op_instance (Private {[ t ]}) (Private ts1)) in Heq.
    change (Public t ⋅ Private ts1) with (state_op_instance (Public t) (Private ts1)).
    simpl in *. injection Heq as Heq.
    case_bool_decide; set_solver.
  - change (Private {[ t ]} ⋅ Public t1) with (state_op_instance (Private {[ t ]}) (Public t1)) in Heq.
    simpl in Heq.
    by case_bool_decide.
  Qed.

  Lemma state_core_id_local_update (st : state) :
    (● st ⋅ ◯ st, ● st) ~l~>
    (● st ⋅ ◯ st, ● st ⋅ ◯ st).
  Proof.
  apply core_id_local_update; first apply _.
  by rewrite auth_frag_included.
  Qed.

End StateUpdates.
