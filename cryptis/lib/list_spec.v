From reloc Require Import reloc.
From stdpp Require Import sorting list lexico.
From cryptis.lib Require Import repr list list_sort.

Section ListLemmas.

Context `{!Repr A, !Repr B, !relocG Σ}.

Implicit Types (x : A) (xs : list A).

Lemma rel_get_list_l E K e (l: list A) (n: nat) Ψ :
  (REL fill K (repr (l !! n)%stdpp : expr) << e @ E : Ψ) -∗
  REL fill K (repr l !! #n) << e @ E : Ψ.
Proof.
rewrite /= repr_list_unseal.
elim: n l => [|n IH] [|x l] /=; iIntros "H";
rel_rec_l; rel_pures_l; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma rel_get_list_r E K e (l: list A) (n: nat) Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (l !! n)%stdpp : expr) @ E : Ψ) -∗
  REL e << fill K (repr l !! #n) @ E : Ψ.
Proof.
move=> ?.
rewrite /= repr_list_unseal.
elim: n l => [|n IH] [|x l] /=; iIntros "H";
rel_rec_r; rel_pures_r; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma rel_nil_l E K e Ψ :
  (REL fill K (repr (@nil A) : expr) << e @ E : Ψ) -∗
  REL fill K (Val []%V) << e @ E : Ψ .
Proof. by rewrite /NILV /= repr_list_unseal; iIntros "?"; rel_pures_l. Qed.

Lemma rel_nil_r E K e Ψ :
  (REL e << fill K (repr (@nil A) : expr) @ E : Ψ) -∗
  REL e << fill K (Val []%V) @ E : Ψ .
Proof. by rewrite /NILV /= repr_list_unseal; iIntros "?"; rel_pures_r. Qed.

Lemma rel_cons_l E K e x xs Ψ :
  (REL fill K (repr (x :: xs)%list : expr) << e @ E : Ψ) -∗
  REL fill K (repr x :: repr xs) << e @ E : Ψ.
Proof. by rewrite /= repr_list_unseal; iIntros "?"; rewrite /CONS; rel_pures_l. Qed.

Lemma rel_cons_r E K e x xs Ψ :
  ↑specN ⊆ E →
  (REL e << fill K (repr (x :: xs)%list : expr) @ E : Ψ) -∗
  REL e << fill K (repr x :: repr xs) @ E : Ψ.
Proof.
move=> ?.
by rewrite /= repr_list_unseal; iIntros "?"; rewrite /CONS; rel_pures_r.
Qed.

Lemma rel_eq_list_l `{EqDecision A} E K e (f : val) (l1 l2 : list A) Ψ :
  (∀ K (x1 x2 : A) Ψ,
      x1 ∈ l1 →
      (REL fill K (#(bool_decide (x1 = x2)) : expr) << e @ E : Ψ) -∗
      REL fill K (f (repr x1) (repr x2)) << e @ E : Ψ) →
  (REL fill K (#(bool_decide (l1 = l2)) : expr) << e @ E : Ψ) -∗
  REL fill K (eq_list f (repr l1) (repr l2)) << e @ E : Ψ.
Proof.
rewrite repr_list_unseal /=.
elim: l1 l2 Ψ => [|x1 l1 IH] [|x2 l2] Ψ rel_f_l /=;
  iIntros "post" ; rel_rec_l; rel_pures_l; do 1?by iApply "post".
rel_bind_l (f _ _). iApply (rel_f_l _ x1 x2); first by set_solver.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2] /=; rel_pures_l; last first.
  rewrite bool_decide_decide decide_False; by [iApply "post"|congruence].
iApply IH; first by move=> *; iApply rel_f_l; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

Lemma rel_eq_list_r `{EqDecision A} E K e (f : val) (l1 l2 : list A) Ψ :
  ↑specN ⊆ E →
  (∀ K (x1 x2 : A),
      ↑specN ⊆ E →
      x1 ∈ l1 →
      (REL e << fill K (#(bool_decide (x1 = x2)) : expr) @ E : Ψ) -∗
      REL e << fill K (f (repr x1) (repr x2)) @ E : Ψ) →
  (REL e << fill K (#(bool_decide (l1 = l2)) : expr) @ E : Ψ) -∗
  REL e << fill K (eq_list f (repr l1) (repr l2)) @ E : Ψ.
Proof.
move=> HE.
rewrite repr_list_unseal /=.
elim: l1 l2 Ψ => [|x1 l1 IH] [|x2 l2] Ψ rel_f_r /=;
  iIntros "post" ; rel_rec_r; rel_pures_r; do 1?by iApply "post".
rel_bind_r (f _ _). iApply (rel_f_r _ x1 x2 HE); first by set_solver.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2] /=; rel_pures_r; last first.
  rewrite bool_decide_decide decide_False; by [iApply "post"|congruence].
iApply IH; first by move=> *; iApply rel_f_r; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

Lemma tp_scan_list `{Repr A} E j φ ψ (f : val) (l : list A) :
  ↑specN ⊆ E →
  □ (∀ j (x : A), ψ NONEV ∗ φ x ∗
        refines_right j (f (repr x)) ={E}=∗
      ∃ (ov : option val), ψ (repr ov) ∗ refines_right j (repr ov)) -∗
  ψ NONEV ∗ ([∗ list] x ∈ l, φ x) ∗
    refines_right j (scan_list f (repr l)) ={E}=∗
  ∃ (ov : option val), ψ (repr ov) ∗ refines_right j (repr ov).
Proof.
move=> HE.
elim: l => [|h t IHt] /=; rewrite repr_list_unseal /=;
iIntros "#Hf (Hψ & Hφ & Hj)"; tp_rec j; tp_pures j;
  first by iExists None; iFrame.
iDestruct "Hφ" as "[Hφ_h Hφ_t]".
tp_bind j (f _).
rewrite refines_right_bind.
iPoseProof ("Hf" with "[Hψ Hφ_h Hj]") as ">(%r & Hψ & Hj)";
  first by iFrame.
case: r => [r|]; tp_pures j.
all: rewrite -refines_right_bind /=; tp_pures j.
by iExists (Some r); iFrame.
iPoseProof (IHt with "Hf [Hψ Hφ_t Hj]") as ">(%r & Hψ & Hj)";
  first by rewrite /= repr_list_unseal; iFrame.
by iFrame.
Qed.

Lemma tp_find_list E j (f : A → bool) (fimpl : val) (l : list A) :
  ↑specN ⊆ E →
  (∀ j (x : A), refines_right j (fimpl (repr x)) ={E}=∗
    refines_right j #(f x)) →
  refines_right j (find_list fimpl (repr l)) ={E}=∗
    refines_right j (repr (find f l)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
elim: l => [|h t IHt] /=;
iIntros "%Hf"; iIntros "Hj"; tp_rec j; tp_pures j; eauto.
tp_bind j (fimpl _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj".
rewrite -refines_right_bind.
case: (f h) => // /=; tp_pures j => //.
iPoseProof (IHt with "Hj") as "Hj" => //.
Qed.

Lemma tp_filter_list E j (f : A → bool) (fimpl : val) (l : list A) :
  ↑specN ⊆ E →
  (∀ j (x : A), refines_right j (fimpl (repr x)) ={E}=∗
    refines_right j #(f x)) →
  refines_right j (filter_list fimpl (repr l)) ={E}=∗
    refines_right j (repr (List.filter f l)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
elim: l j => [|h t IHt] j /=;
iIntros "%Hf"; iIntros "Hj"; tp_rec j; tp_pures j; eauto.
tp_bind j (filter_list _ _).
rewrite refines_right_bind.
iPoseProof (IHt with "Hj") as ">Hj"; eauto.
rewrite -refines_right_bind /=.
tp_pures j.
tp_bind j (fimpl _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
case : (f h) => // /=; tp_pures j; done.
Qed.

Lemma tp_append_lists E j (l1 l2 : list A) :
  ↑specN ⊆ E →
  refines_right j (append_lists (repr l1) (repr l2)) ={E}=∗
    refines_right j (repr (l1 ++ l2)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
elim: l1 j => /= [| h l1' IH] j /=;
iIntros "Hj"; tp_rec j; tp_pures j.
  by [].
tp_bind j (append_lists _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj"; eauto.
rewrite -refines_right_bind /=.
by tp_pures j.
Qed.

Lemma tp_map_list E j (f : A -> B) (fimpl : val) xs :
  ↑specN ⊆ E →
  (∀ j, Forall (λ y, refines_right j (fimpl (repr y)) ={E}=∗
     refines_right j (repr (f y))) xs) →
  refines_right j (map_list fimpl (repr xs)) ={E}=∗
    refines_right j (repr (map f xs)).
Proof.
move=> HE.
rewrite !repr_list_unseal /=.
iIntros "%tp_fimpl_all Hj"; iStopProof.
elim: xs tp_fimpl_all j => [| h xs' IH] tp_fimpl_all j /=; iIntros "Hj";
  tp_rec j; tp_pures j.
    by iApply "Hj".
have tp_fimpl j := Forall_inv (tp_fimpl_all j);
have tp_fimpl_rest j := Forall_inv_tail (tp_fimpl_all j);
clear tp_fimpl_all.
tp_bind j (map_list _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj"; eauto.
tp_bind j (fimpl _).
rewrite refines_right_bind.
iPoseProof (tp_fimpl with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
by tp_pures j.
Qed.

Lemma tp_foldr_list E j (f : B -> A -> A) (fimpl : val) (l : list B) x :
  ↑specN ⊆ E →
  (∀ j (b : B) (a : A), refines_right j (fimpl (repr b) (repr a)) ={E}=∗
    refines_right j (repr (f b a))) →
  refines_right j (foldr_list fimpl (repr x) (repr l)) ={E}=∗
    refines_right j (repr (foldr f x l)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
iIntros "%tp_f Hj"; iStopProof.
elim: l j => [| h l' IH] j /=; iIntros "Hj"; tp_rec j; tp_pures j; first done.
tp_bind j (foldr_list _ _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj".
tp_bind j (fimpl _ _).
by iPoseProof (tp_f with "Hj") as ">Hj".
Qed.

End ListLemmas.

Section ListLemmasEq.

Context `{!EqDecision A, !Repr A, !relocG Σ}.

Implicit Types (v x : A) (l : list A).

Lemma tp_mem_list E j (eqImpl : val) v l :
  ↑specN ⊆ E →
  (∀ j x y, refines_right j (eqImpl (repr x) (repr y)) ={E}=∗
    refines_right j #(bool_decide (x = y))) →
  refines_right j (mem_list eqImpl (repr v) (repr l)) ={E}=∗
    refines_right j #(bool_decide (v ∈ l)).
Proof.
move=> HE.
iIntros "%tp_eqImpl Hj".
tp_lam j; tp_pures j.
tp_bind j (find_list _ _).
rewrite refines_right_bind.
iPoseProof (tp_find_list _ _ (λ x, bool_decide (v = x)) with "Hj") as ">Hj"=> //.
  iIntros "%j' %x Hj'"; tp_pures j'.
  iPoseProof (tp_eqImpl with "Hj'") as ">Hj'"=> //.
rewrite -refines_right_bind => /=.
rewrite find_if_in.
case: (List.find (λ x, bool_decide (v = x)) l) => *; by tp_pures j.
Qed.

Lemma tp_rem_list E j (eqImpl : val) v l :
  ↑specN ⊆ E →
  (∀ j x y, refines_right j (eqImpl (repr x) (repr y)) ={E}=∗
    refines_right j #(bool_decide (x = y))) →
  refines_right j (rem_list eqImpl (repr v) (repr l)) ={E}=∗
    refines_right j (repr (rem v l)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
iIntros "%tp_eqImpl Hj".
iStopProof; elim: l j => [|x l IH] j /=; iIntros "Hj"; tp_rec j; tp_pures j.
  by iApply "Hj".
tp_bind j (eqImpl _ _).
rewrite refines_right_bind.
iPoseProof (tp_eqImpl with "Hj") as ">Hj"=> //.
rewrite -refines_right_bind=> /=.
rewrite (_ : bool_decide (v = x) = bool_decide (x = v)); last first.
  by apply: bool_decide_ext; split; congruence.
case: (bool_decide (x = v)) => /=; tp_pures j; first by iApply "Hj".
tp_bind j (rem_list _ _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj".
rewrite -refines_right_bind=> /=.
tp_pures j; by iApply "Hj".
Qed.

End ListLemmasEq.

Section DoUntil.

Context `{!relocG Σ}.

Lemma rel_do_until (f f' : val) φ Ψ :
  □ (φ -∗ REL f' #() << f #() : (fun o1 o2 =>
    ⌜o1 = NONEV⌝ ∗ ⌜o2 = NONEV⌝ ∗ φ ∨
    ∃ (v v' : val), ⌜o1 = SOMEV v⌝ ∗ ⌜o2 = SOMEV v'⌝ ∗
    Ψ v v')) -∗
  φ -∗
  REL do_until f' << do_until f : Ψ.
Proof.
iIntros "#Hf Hφ". iLöb as "IH".
rel_rec_l; rel_rec_r.
rel_bind_l (f' _); rel_bind_r (f _).
iApply (refines_bind with "[Hφ] []").
by iApply "Hf".
iIntros (v v') "Hv" => /=.
iDestruct "Hv" as "[(-> & -> & Hφ)| (%v1 & %v2 & -> & -> & HΨ)]";
rel_pures_l; rel_pures_r; first by iApply "IH".
rel_values.
Qed.

Lemma rel_do_until' (f f' : val) Ψ :
  □ (REL f' #() << f #() : (fun o1 o2 =>
    ⌜o1 = NONEV⌝ ∗ ⌜o2 = NONEV⌝ ∨
    ∃ (v v' : val), ⌜o1 = SOMEV v⌝ ∗ ⌜o2 = SOMEV v'⌝ ∗
    Ψ v v')) -∗
  REL do_until f' << do_until f : Ψ.
Proof.
iIntros "#Hf".
iApply (rel_do_until _ _ True%I) => //.
iIntros "!> _".
iApply refines_wand => //.
iIntros (v v') "[(-> & ->)|(%v1 & %v2 & HΨ)]"; eauto.
Qed.

End DoUntil.

Section Ordered.

Context {A : Type}.
Context (R : relation A)
  `{!RelDecision R, !Transitive R, !Total R, !AntiSymm (=@{A}) R}.
Context `{!Repr A, !relocG Σ}.

Implicit Types (x y z : A) (l : list A).

Lemma tp_insert_sorted E j (f : val) x l :
  ↑specN ⊆ E →
  StronglySorted R l →
  (∀ j y z, refines_right j (f (repr y) (repr z)) ={E}=∗
    refines_right j #(bool_decide (R y z))) →
  refines_right j (insert_sorted f (repr x) (repr l)) ={E}=∗
    ∃ l', ⌜StronglySorted R l'⌝ ∗ ⌜l' ≡ₚ x :: l⌝ ∗ refines_right j (repr l').
Proof.
move=> HE.
rewrite repr_list_unseal => sorted_l tp_f.
elim: l sorted_l j => [|y l IH] sorted_l j /=; iIntros "Hj"; tp_rec j; tp_pures j.
  iModIntro. iExists [x]. iSplitR "Hj"; last iSplitR "Hj"; last by iApply "Hj".
    by iPureIntro; repeat constructor.
  by iPureIntro.
move: (sorted_l) => /StronglySorted_cons [Ry_l sorted_l'].
move/(_ sorted_l') in IH.
tp_bind j (f _ _).
rewrite refines_right_bind.
iPoseProof (tp_f with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
case: (bool_decide_reflect (R x y)) => [Rxy|nRxy]; tp_pures j.
  iModIntro. iExists (x :: y :: l). iSplitR "Hj"; last iSplitR "Hj"; last by iApply "Hj".
    iPureIntro. apply/StronglySorted_cons; split; last exact: sorted_l.
    constructor; first exact: Rxy.
    apply: (Forall_impl _ _ _ Ry_l) => z Ryz; exact: (transitivity Rxy Ryz).
  by iPureIntro.
tp_bind j (insert_sorted _ _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">(%l' & %ss' & %perm' & Hj)".
rewrite -refines_right_bind /=.
tp_pures j.
iModIntro. iExists (y :: l'). iSplitR "Hj"; last iSplitR "Hj"; last by iApply "Hj".
  iPureIntro. apply/StronglySorted_cons; split; last exact: ss'.
  apply/Forall_forall => z; rewrite perm' elem_of_cons => - [->|z_l].
    exact: (total_not _ _ nRxy).
  by move/Forall_forall: Ry_l; apply.
iPureIntro. by rewrite perm'; exact: Permutation_swap.
Qed.

Lemma tp_insertion_sort E j (f : val) l :
  ↑specN ⊆ E →
  (∀ j x y, refines_right j (f (repr x) (repr y)) ={E}=∗
    refines_right j #(bool_decide (R x y))) →
  refines_right j (insertion_sort f (repr l)) ={E}=∗
    refines_right j (repr (merge_sort R l)).
Proof.
move=> HE.
rewrite repr_list_unseal => tp_f; iIntros "Hj"; iStopProof.
elim: l j => [|y l IH] j; iIntros "Hj"; tp_rec j; tp_pures j.
  by iApply "Hj".
tp_bind j (insertion_sort _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj".
rewrite -refines_right_bind => /=.
rewrite -repr_list_unseal.
iPoseProof (tp_insert_sorted _ _ _ _ _ HE (merge_sort_sorted R l) tp_f with "Hj")
  as ">(%l' & %ss' & %perm' & Hj)".
have -> : merge_sort R (y :: l) = l'.
  apply: (StronglySorted_unique R); [exact: merge_sort_sorted|exact: ss'|].
  by rewrite merge_sort_Permutation perm' merge_sort_Permutation.
by iApply "Hj".
Qed.

End Ordered.

Section Lexicographic.

Context `{!EqDecision A, !Lexico A,
          !StrictOrder (@lexico A _), !TrichotomyT (@lexico A _),
          !Repr A, !relocG Σ}.

Implicit Types (x : A) (l : list A).

Lemma tp_leq_list E j (feq fle : val) l1 l2 :
  ↑specN ⊆ E →
  (∀ j x1 x2, refines_right j (feq (repr x1) (repr x2)) ={E}=∗
    refines_right j #(bool_decide (x1 = x2))) →
  (∀ j x1 x2, x1 ∈ l1 →
    refines_right j (fle (repr x1) (repr x2)) ={E}=∗
    refines_right j #(bool_decide (x1 = x2 ∨ lexico x1 x2))) →
  refines_right j (leq_list feq fle (repr l1) (repr l2)) ={E}=∗
    refines_right j #(bool_decide (l1 = l2 ∨ lexico l1 l2)).
Proof.
move=> HE feqP.
rewrite /= repr_list_unseal.
elim: l1 l2 j => [|x1 l1 IH] [|x2 l2] j fleP; iIntros "Hj";
  tp_rec j; tp_pures j; rewrite bool_decide_lexico_le; try by iApply "Hj".
tp_bind j (feq _ _).
rewrite refines_right_bind.
iPoseProof (feqP with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
case: (bool_decide_reflect (x1 = x2)) => [ex|ne]; tp_pures j.
- iApply (IH with "Hj") => j' x1' x2' x1'_in; apply: fleP.
  by apply: list_elem_of_further.
- by iApply (fleP _ _ _ (list_elem_of_here x1 l1) with "Hj").
Qed.

End Lexicographic.
