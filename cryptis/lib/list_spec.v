From reloc Require Import reloc.
From cryptis.lib Require Import repr list.

Section ListLemmas.

Context `{!Repr A, !Repr B, !relocG Σ}.

Implicit Types (x : A) (xs : list A).

Lemma rel_get_list_l K e (l: list A) (n: nat) Ψ :
  (REL fill K (repr (l !! n)%stdpp : expr) << e : Ψ) -∗
  REL fill K (repr l !! #n) << e : Ψ.
Proof.
iIntros "H".
by iApply refines_wp_l; wp_apply wp_get_list.
Qed.

Lemma rel_get_list_r K e (l: list A) (n: nat) Ψ :
  (REL e << fill K (repr (l !! n)%stdpp : expr) : Ψ) -∗
  REL e << fill K (repr l !! #n) : Ψ.
Proof.
rewrite /= repr_list_unseal.
elim: n l => [|n IH] [|x l] /=; iIntros "H";
rel_rec_r; rel_pures_r; eauto.
rewrite (_ : (S n - 1)%Z = n); try lia.
by iApply IH.
Qed.

Lemma rel_nil_l K e Ψ :
  (REL fill K (repr (@nil A) : expr) << e : Ψ) -∗
  REL fill K (Val []%V) << e : Ψ .
Proof. iIntros "?". by iApply refines_wp_l; wp_apply (@wp_nil A). Qed.

Lemma rel_nil_r K e Ψ :
  (REL e << fill K (repr (@nil A) : expr) : Ψ) -∗
  REL e << fill K (Val []%V) : Ψ .
Proof. by rewrite /NILV /= repr_list_unseal; iIntros "?"; rel_pures_r. Qed.

Lemma rel_cons_l K e x xs Ψ :
  (REL fill K (repr (x :: xs)%list : expr) << e : Ψ) -∗
  REL fill K (repr x :: repr xs) << e : Ψ.
Proof. iIntros "?". by iApply refines_wp_l; wp_apply wp_cons. Qed.

Lemma rel_cons_r K e x xs Ψ :
  (REL e << fill K (repr (x :: xs)%list : expr) : Ψ) -∗
  REL e << fill K (repr x :: repr xs) : Ψ.
Proof. by rewrite /= repr_list_unseal; iIntros "?"; rewrite /CONS; rel_pures_r. Qed.

Lemma rel_eq_list_l `{EqDecision A} K e (f : val) (l1 l2 : list A) Ψ :
  (∀ (x1 x2 : A) E Ψ,
      x1 ∈ l1 →
      Ψ #(bool_decide (x1 = x2)) -∗
      WP f (repr x1) (repr x2) @ E [{ Ψ }]) →
  (REL fill K (#(bool_decide (l1 = l2)) : expr) << e : Ψ) -∗
  REL fill K (eq_list f (repr l1) (repr l2)) << e : Ψ.
Proof.
iIntros (H) "?". iApply refines_wp_l.
iApply twp_wp; wp_apply twp_eq_list; eauto.
Qed.

#[local] Lemma tp_eq_list `{EqDecision A} E j (f : val) (l1 l2 : list A) :
  ↑specN ⊆ E →
  (∀ (x1 x2 : A) j',
      x1 ∈ l1 →
      refines_right j' (f (repr x1) (repr x2)) -∗
      |={E}=> refines_right j' #(bool_decide (x1 = x2))) →
  refines_right j (eq_list f (repr l1) (repr l2)) -∗
  |={E}=> refines_right j #(bool_decide (l1 = l2)).
Proof.
move=> HE Hf.
rewrite repr_list_unseal /=.
elim: l1 l2 => [|x1 l1 IH] [|x2 l2] /= in Hf *; iIntros "Hj";
  tp_rec j; tp_pures j; do 1?by iApply "Hj".
tp_bind j (f _ _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj"; try set_solver.
rewrite -refines_right_bind /=.
case: (bool_decide_reflect (x1 = x2)) => [->|n_x1x2]; tp_pures j; last first.
  rewrite bool_decide_decide decide_False //; congruence.
iPoseProof (IH with "Hj") as ">Hj"; first by move=> *; iApply Hf; set_solver.
case: (bool_decide_reflect (l1 = l2)) => [->|n_l1l2].
- by rewrite bool_decide_decide decide_True.
- by rewrite bool_decide_decide decide_False //; congruence.
Qed.

Lemma rel_eq_list_r `{EqDecision A} K e (f : val) (l1 l2 : list A) Ψ :
  (∀ (x1 x2 : A) E j,
      x1 ∈ l1 →
      refines_right j (f (repr x1) (repr x2)) -∗
      |={E}=> refines_right j #(bool_decide (x1 = x2))) →
  (REL e << fill K (#(bool_decide (l1 = l2)) : expr) : Ψ) -∗
  REL e << fill K (eq_list f (repr l1) (repr l2)) : Ψ.
Proof.
iIntros (?) "?". iApply refines_step_r.
iIntros (j) "Hj". iPoseProof (tp_eq_list with "Hj") as ">Hj"; eauto.
by iFrame.
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

#[warnings="-ambiguous-paths"]
Import ssrbool seq boot.eqtype.
Variable (A : eqType).
Context `{!Repr A, !relocG Σ}.

Lemma tp_mem_list E j (eqImpl : heap_lang.val) (v : A) (l : list A) :
  ↑specN ⊆ E →
  (∀ j (x y : A), refines_right j (eqImpl (repr x) (repr y)) ={E}=∗
    refines_right j #(eq_op x y)) →
  refines_right j (mem_list eqImpl (repr v) (repr l)) ={E}=∗
    refines_right j #(v \in l).
Proof.
move=> HE.
iIntros "%tp_eqImpl Hj".
tp_lam j; tp_pures j.
tp_bind j (find_list _ _).
rewrite refines_right_bind.
iPoseProof (tp_find_list with "Hj") as ">Hj"=> //.
  iIntros "%j' %x Hj'"; tp_pures j'.
  iPoseProof (tp_eqImpl with "Hj'") as ">Hj'"=> //.
rewrite -refines_right_bind => /=.
rewrite find_if_in.
case (List.find (eq_op v) l) => *; by tp_pures j.
Qed.

Lemma tp_rem_list E j (eqImpl : heap_lang.val) (v : A) (l : list A) :
  ↑specN ⊆ E →
  (∀ j (x y : A), refines_right j (eqImpl (repr x) (repr y)) ={E}=∗
    refines_right j #(eq_op x y)) →
  refines_right j (rem_list eqImpl (repr v) (repr l)) ={E}=∗
    refines_right j (repr (seq.rem v l)).
Proof.
move=> HE.
rewrite repr_list_unseal /=.
iIntros "%tp_eqImpl Hj".
iStopProof; elim: l j => [| h l' IH] j /=; iIntros "Hj"; tp_rec j; tp_pures j.
  by iApply "Hj".
tp_bind j (eqImpl _ _).
rewrite refines_right_bind.
iPoseProof (tp_eqImpl with "Hj") as ">Hj"=> //.
rewrite -refines_right_bind=> /=.
case: (h == v) => /=; tp_pures j; first by iApply "Hj".
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

#[warnings="-ambiguous-paths"]
Import ssrbool seq all_order path.
Variable (d : Order.disp_t) (A : orderType d).
Context `{!Repr A, !relocG Σ}.
Import Order Order.POrderTheory Order.TotalTheory.
Implicit Types (x y z : A) (s : seqlexi_with d A).

Lemma tp_insert_sorted E j (f : val) (x : A) (l : list A) :
  ↑specN ⊆ E →
  is_true (sorted le l) →
  (∀ j (y z : A),
      refines_right j (f (repr y) (repr z)) ={E}=∗
        refines_right j #(le y z)) →
  refines_right j (insert_sorted f (repr x) (repr l)) ={E}=∗
    refines_right j (repr (sort le (x :: l))).
Proof.
move=> HE.
rewrite repr_list_unseal => sorted_l Hf.
elim: l sorted_l j => //= [|y l IH] path_l j; iIntros "Hj";
tp_rec j => /=; tp_pures j => //;
move/(_ (path_sorted path_l)) in IH.
tp_bind j (f _ _).
rewrite refines_right_bind.
iPoseProof (Hf with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
have [le_xy|le_yx] := boolP (x <= y)%O; tp_pures j.
  by rewrite sort_le_id //= ?le_xy.
move: le_yx; rewrite -ltNge => /ltW le_yx.
tp_bind j (insert_sorted _ _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj".
rewrite -refines_right_bind /=.
tp_pures j.
suff -> : sort le [:: x, y & l] = y :: sort le (x :: l) by tp_pures j.
rewrite -[RHS]sort_le_id /=.
  apply/perm_sort_leP/perm_consP.
  exists 1, (l ++ [:: x])%SEQ.
  by rewrite /= perm_catC perm_sym /= perm_sort; split.
rewrite path_min_sorted ?sort_le_sorted // all_sort /= le_yx /=.
apply: order_path_min => //; apply: le_trans.
Qed.

Lemma tp_insertion_sort E j (f : val) (l : list A) :
  ↑specN ⊆ E →
  (∀ j (x y : A), refines_right j (f (repr x) (repr y)) ={E}=∗
    refines_right j #(le x y)) →
  refines_right j (insertion_sort f (repr l)) ={E}=∗
    refines_right j (repr (sort le l)).
Proof.
move=> HE.
rewrite repr_list_unseal => tp_f; iIntros "Hj"; iStopProof.
elim: l j => [| y l' IH] j; iIntros "Hj"; tp_rec j; tp_pures j.
  iApply "Hj".
tp_bind j (insertion_sort _ _).
rewrite refines_right_bind.
iPoseProof (IH with "Hj") as ">Hj".
rewrite -refines_right_bind => /=.
rewrite -repr_list_unseal.
iPoseProof (tp_insert_sorted with "Hj") as ">Hj" => //.
suff ->: sort <=%O (y :: sort <=%O l') = sort <=%O (y :: l') by [].
apply /perm_sort_leP; rewrite perm_cons.
apply /permPl /perm_sort.
Qed.

Lemma tp_leq_list E j (feq : val) (fle : val) s1 s2 :
  ↑specN ⊆ E →
  (∀ j x1 x2,
      refines_right j (feq (repr x1) (repr x2)) ={E}=∗
        refines_right j #(eqtype.eq_op x1 x2)) →
  (∀ j x1 x2,
      is_true (x1 \in s1) →
        refines_right j (fle (repr x1) (repr x2)) ={E}=∗
        refines_right j #(le x1 x2)) →
  refines_right j (leq_list feq fle (repr s1) (repr s2)) ={E}=∗
    refines_right j #(le s1 s2).
Proof.
move=> HE.
move=> feqP.
rewrite /= repr_list_unseal.
elim: s1 s2 => [|x1 s1 IH] [|x2 s2] fleP; iIntros "Hj";
  tp_rec j => /=; tp_pures j => //.
rewrite lexi_cons; tp_bind j (feq _ _).
rewrite refines_right_bind => /=.
iPoseProof (feqP with "Hj") as ">Hj".
case: (ltgtP x1 x2) => [l_x1x2|l_x2x1|<-] /=; tp_pures j.
all: simpl; set ctx := IfCtx _ _;
     rewrite -(refines_right_bind j [ctx] #_) => /=; tp_pures j.
- iPoseProof (fleP with "Hj") as ">Hj";
  rewrite ?inE ?eqtype.eqxx // ltW //.
- iPoseProof (fleP with "Hj") as ">Hj";
  rewrite ?inE ?eqtype.eqxx // leNgt l_x2x1 //.
- iPoseProof (IH with "Hj") as ">Hj"=> // j' x1' ? x1'_in;
  apply fleP; rewrite inE x1'_in orbT //.
Qed.

End Ordered.
