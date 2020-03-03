(** * Reduction of PCP to ZF-Deduction *)

From Undecidability.Reductions Require Export BPCP_to_ZF.
From Undecidability.FOLP Require Export FullND.





(** ** Definition of ZF theory *)

Notation "x ∈ y" := (Pred elem (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "x ≡ y" := (Pred equal (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
Notation "$ x" := (var_term x) (at level 1).

Notation "∅" := (Func eset Vector.nil).
Notation "'ω'" := (Func om Vector.nil).
Notation "{ x ; y }" := (Func pair (Vector.cons x (Vector.cons y Vector.nil))) (at level 10).
Notation "⋃ x" := (Func union (Vector.cons x Vector.nil)) (at level 15).
Notation "'PP' x" := (Func power (Vector.cons x Vector.nil)) (at level 15).

Notation "x ∪ y" := (⋃ {x; y}) (at level 16).
Notation "'σ' x" := (x ∪ {x; x}) (at level 15).

Definition ax_refl :=
  ∀ $0 ≡ $0.

Definition ax_sym :=
  ∀ ∀ $1 ≡ $0 --> $0 ≡ $1.

Definition ax_trans :=
  ∀ ∀ ∀ $2 ≡ $1 --> $1 ≡ $0 --> $2 ≡ $0.

Definition ax_eq_elem :=
  ∀ ∀ ∀ ∀ $3 ≡ $1 --> $2 ≡ $0 --> $3 ∈ $2 --> $1 ∈ $0.

Definition ZF phi :=
  phi = ax_ext
  \/ phi = ax_eset
  \/ phi = ax_pair
  \/ phi = ax_union
  \/ phi = ax_power
  \/ phi = ax_om1
  \/ phi = ax_om2
  \/ (exists psi, bounded 1 psi /\ phi = ax_sep psi)
  \/ (exists psi, bounded 2 psi /\ phi = ax_rep psi)
  \/ phi = ax_refl
  \/ phi = ax_sym
  \/ phi = ax_trans
  \/ phi = ax_eq_elem.





(** ** Theory manipulation *)

Instance ZF_funcs_dec :
  eq_dec Funcs.
Proof.
  intros f g. unfold dec. decide equality.
Qed.

Instance ZF_preds_dec :
  eq_dec Preds.
Proof.
  intros f g. unfold dec. decide equality.
Qed.

Lemma tsubs_refl T :
  T ⊑ T.
Proof.
  firstorder.
Qed.

Lemma tsubs_trans T1 T2 T3 :
  T1 ⊑ T2 -> T2 ⊑ T3 -> T1 ⊑ T3.
Proof.
  firstorder.
Qed.

Lemma tsubs_extend T phi :
  T ⊑ (T ⋄ phi).
Proof.
  firstorder.
Qed.

Ltac solve_tsub :=
  try apply tsubs_refl; eapply tsubs_trans; eauto; try eapply tsubs_extend.

Lemma prv_T_mp (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi --> psi) -> T ⊩ phi -> T ⊩ psi.
Proof.
  intros [A[A1 A2]] [B[B1 B2]]. use_theory (A++B).
  apply IE with phi; eauto using Weak.
Qed.

Lemma prv_T_ExI (p : peirce) (b : bottom) T phi t :
  T ⊩ phi[t..] -> T ⊩ ∃ phi.
Proof.
  intros [A[A1 A2]]. use_theory A.
  now apply ExI with t.
Qed.

Lemma prv_T_CI (p : peirce) (b : bottom) T phi psi :
  T ⊩ phi -> T ⊩ psi -> T ⊩ (phi ∧ psi).
Proof.
  intros [A[A1 A2]] [B[B1 B2]]. use_theory (A++B).
   apply CI; eauto using Weak.
Qed.

Lemma prv_T_DI1 (p : peirce) (b : bottom) T phi psi :
  T ⊩ phi -> T ⊩ (phi ∨ psi).
Proof.
  intros [A[H1 H2]]. use_theory A. now apply DI1.
Qed.

Lemma prv_T_DI2 (p : peirce) (b : bottom) T phi psi :
  T ⊩ psi -> T ⊩ (phi ∨ psi).
Proof.
  intros [A[H1 H2]]. use_theory A. now apply DI2.
Qed.

Lemma prv_T_CE1 (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ phi.
Proof.
  intros [A[H1 H2]]. use_theory A. eapply CE1; eauto.
Qed.

Lemma prv_T_CE2 (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ psi.
Proof.
  intros [A[H1 H2]]. use_theory A. eapply CE2; eauto.
Qed.

Lemma prv_T_CE (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi ∧ psi) -> T ⊩ phi /\ T ⊩ psi.
Proof.
  intros H. split.
  - now apply prv_T_CE1 in H.
  - now apply prv_T_CE2 in H.
Qed.

Lemma prv_T_AllE (p : peirce) (b : bottom) T phi t :
  (T ⊩ ∀ phi) -> T ⊩ phi[t..].
Proof.
  intros [A[H1 H2]]. use_theory A. now apply AllE.
Qed.

Lemma prv_T_DE (p : peirce) (b : bottom) T phi psi theta :
  T ⊩ (phi ∨ psi) -> (T ⋄ phi) ⊩ theta -> (T ⋄ psi) ⊩ theta -> T ⊩ theta.
Proof.
  intros [A[A1 A2]] [B[B1 B2]] [C[C1 C2]].
  exists (A ++ (rem B phi) ++ (rem C psi)). split.
  { intros xi. intros [H|[H|H] % in_app_iff] % in_app_iff; auto. 
    - apply in_rem_iff in H as [H1 H2]. apply B1 in H1 as [H1|H1]; tauto.
    - apply in_rem_iff in H as [H1 H2]. apply C1 in H1 as [H1|H1]; tauto. }  
  eapply DE. eapply Weak; try apply A2. auto.
  - apply (Weak B2). intros xi H. decide (xi = phi); auto; try now left.
    right. apply in_or_app. right. eauto using rem_neq.
  - apply (Weak C2). intros xi H. decide (xi = psi); auto; try now left.
    right. apply in_or_app. right. eauto using rem_neq.   
Qed.

Lemma prv_T_DS (p : peirce) (b : bottom) T phi :
  T ⊩ (phi ∨ phi) -> T ⊩ phi.
Proof.
  intros H. apply (prv_T_DE H); apply elem_prv; now right.
Qed.

Lemma prv_T1 (p : peirce) (b : bottom) T phi :
  T ⋄ phi ⊩ phi.
Proof.
  apply elem_prv. now right.
Qed.

Lemma prv_T2 (p : peirce) (b : bottom) T phi psi :
  (T ⋄ psi) ⋄ phi ⊩ psi.
Proof.
  apply elem_prv. left. now right.
Qed.

Lemma prv_T3 (p : peirce) (b : bottom) T phi psi theta :
  ((T ⋄ psi) ⋄ phi) ⋄ theta ⊩ psi.
Proof.
  apply elem_prv. left. left. now right.
Qed.

Lemma prv_T_imp (p : peirce) (b : bottom) T phi psi :
  T ⊩ (phi --> psi) -> T ⋄ phi ⊩ psi.
Proof.
  intros H. eapply prv_T_mp. 2: apply prv_T1.
  apply (Weak_T H). firstorder.
Qed.

Lemma prv_T_exf (p : peirce) T phi :
  T ⊩(p, expl) ⊥ -> T ⊩(p, expl) phi.
Proof.
  intros [A[H1 H2]]. use_theory A. now apply Exp.
Qed.

Lemma prv_T_ExE (p : peirce) (b : bottom) (T : theory) n phi psi :
  (forall theta, T theta -> unused n theta) -> unused n psi -> unused (S n) phi
  -> (T ⊩ ∃ phi) -> (T ⋄ phi[(var_term n)..]) ⊩ psi -> T ⊩ psi.
Proof.
  intros H1 H2 H3 [A[A1 A2]] [B[B1 B2]].
  assert (HT : (A ++ rem B phi[($ n)..]) ⊏ T).
  { intros theta [H|[H H'] % in_rem_iff] % in_app_iff; auto. now apply B1 in H as [H|H]. }
  exists (A ++ rem B (phi[($ n)..])). split; trivial. eapply ExE.
  - apply (Weak A2). auto.
  - apply nameless_equiv_ex with n; trivial.
    + firstorder.
    + apply (Weak B2). intros theta H.
      decide (theta = phi[($ n)..]); auto. now left.
Qed.

Lemma prv_T_AllI (p : peirce) (b : bottom) (T : theory) n phi :
  (forall theta, T theta -> unused n theta) -> unused (S n) phi
  -> T ⊩ phi[(var_term n)..] -> T ⊩ ∀ phi.
Proof.
  intros H1 H2 [A[A1 A2]]. use_theory A.
  apply AllI. apply nameless_equiv_all with n; firstorder.
Qed.

Lemma prv_T_imps (p : peirce) (b : bottom) T phi psi psi' :
  T ⊩ (phi --> psi) -> T ⊩ (psi --> psi') -> T ⊩ (phi --> psi').
Proof.
  intros H1 H2. apply prv_T_impl. eapply prv_T_mp.
  apply (Weak_T H2). apply tsubs_extend.
  now apply prv_T_imp.
Qed.

Lemma prv_clear1 (p : peirce) (b : bottom) T phi psi :
  T ⊩ phi -> (T ⋄ psi) ⊩ phi.
Proof.
  intros H. apply (Weak_T H). repeat solve_tsub.
Qed.

Lemma prv_clear2 (p : peirce) (b : bottom) T phi psi theta :
  (T ⋄ psi) ⊩ phi -> ((T ⋄ theta) ⋄ psi) ⊩ phi.
Proof.
  intros H. apply (Weak_T H).
  intros phi'. unfold extend, contains. tauto.
Qed.





(** ** Bounded terms and formulas *)

Lemma substt_bounded t sigma n :
  bounded_term n t -> (forall i, i < n -> sigma i = $i) -> subst_term sigma t = t.
Proof.
  induction 1; intros HS; cbn; try now apply HS.
  f_equal. erewrite <- vec_id. 2: reflexivity.
  apply vec_map_ext. intros x H'. now apply H0.
Qed.

Lemma substt_bounded0 t sigma :
  bounded_term 0 t -> subst_term sigma t = t.
Proof.
  intros H. apply (substt_bounded H). intros i. lia.
Qed.

Lemma subst_bounded phi sigma n :
  bounded n phi -> (forall i, i < n -> sigma i = $i) -> phi[sigma] = phi.
Proof.
  induction 1 in sigma |- *; intros HS; cbn; subst; try firstorder congruence.
  - f_equal. erewrite <- vec_id. 2: reflexivity.
    apply vec_map_ext. intros x H'. eapply substt_bounded; eauto.
  - f_equal. apply IHbounded. intros [|i] Hi; trivial.
    cbn. asimpl. rewrite HS; trivial. lia.
  - f_equal. apply IHbounded. intros [|i] Hi; trivial.
    cbn. asimpl. rewrite HS; trivial. lia.
Qed.

Lemma subst_bounded0 phi sigma :
  bounded 0 phi -> phi[sigma] = phi.
Proof.
  intros H. apply (subst_bounded H). intros i. lia.
Qed.

Ltac solve_bounds :=
  repeat constructor; try lia; try inversion X; intros;
  match goal with
  | H : vec_in ?x (Vector.cons ?y ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H
  | _ => idtac
  end.

Lemma bounded_term_up t n k :
  bounded_term n t -> k >= n -> bounded_term k t.
Proof.
  induction 1; cbn; intros Hk; constructor; firstorder lia.
Qed.

Lemma bounded_up phi n k :
  bounded n phi -> k >= n -> bounded k phi.
Proof.
  induction 1 in k |- *; cbn; intros Hk; constructor; try firstorder.
  eauto using bounded_term_up.
Qed.

Lemma vec_map_inv X Y (f : X -> Y) n (v : vector X n) y :
  vec_in y (Vector.map f v) -> sigT (fun x => prod (vec_in x v) (y = f x)).
Proof.
  revert y. apply vec_forall_map. intros x H. exists x. split; trivial.
Qed.

Lemma substt_bounded_up t n sigma k :
  bounded_term n t -> (forall i, i < n -> bounded_term k (sigma i)) -> bounded_term k (subst_term sigma t).
Proof.
  induction 1; intros HS; cbn; auto.
  constructor. intros t [t'[HT ->]] % vec_map_inv.
  apply H0; trivial.
Qed.

Lemma subst_bounded_up phi n sigma k :
  bounded n phi -> (forall i, i < n -> bounded_term k (sigma i)) -> bounded k (phi[sigma]).
Proof.
  induction 1 in k, sigma |- *; intros H1 ; cbn; solve_bounds; intuition.
  - apply vec_map_inv in X as [t'[HT ->]].
    eapply substt_bounded_up; eauto.
  - apply IHbounded; try lia.
    intros [|i]; cbn; asimpl.
    + intros _. constructor. lia.
    + intros Hi. eapply substt_bounded_up; try apply H1; try lia.
      intros [|j] Hj; asimpl; unfold unscoped.shift; constructor; lia.
  - apply IHbounded; try lia.
    intros [|i]; cbn; asimpl.
    + intros _. constructor. lia.
    + intros Hi. eapply substt_bounded_up; try apply H1; try lia.
      intros [|j] Hj; asimpl; unfold unscoped.shift; constructor; lia.    
Qed.

Lemma ZF_bounded phi :
  ZF phi -> bounded 0 phi.
Proof.
  intros [->|[->|[->|[->|[->|[->|[->|[[psi [H ->]]|[[psi [H ->]]|[->|[->|[->| ->]]]]]]]]]]]];
  repeat solve_bounds; eauto using bounded_up.
  - apply (subst_bounded_up H). intros [|[]]; solve_bounds.
  - apply (subst_bounded_up H). intros [|[]]; solve_bounds.
Qed.

Lemma ZF_all phi :
  ZF ⊩IE phi -> ZF ⊩IE ∀ phi.
Proof.
  intros [A[H1 H2]]. use_theory A. apply AllI.
  enough ([psi[form_shift] | psi ∈ A] = A) as -> by trivial.
  erewrite <- list_id. 2: reflexivity.
  apply map_ext_in. intros psi H % H1.
  apply subst_bounded0, ZF_bounded, H.
Qed.

Lemma find_unused_L A :
  sig (fun n => forall k, n <= k -> unused_L k A).
Proof.
  induction A.
  - exists 0. intros k _ phi [].
  - destruct IHA as [n HN], (find_unused a) as [m HM].
    destruct (le_lt_dec m n) as [H|H].
    + exists n. intros k H1 phi [->|H2]. apply HM. lia. apply HN; auto.
    + exists m. intros k H1 phi [->|H2]. apply HM. lia. apply HN; trivial. lia.
Qed.

Lemma bounded_unused_term t n k :
  bounded_term n t -> k >= n -> unused_term k t.
Proof.
  induction 1; intros Hk; constructor. lia. firstorder.
Qed.

Lemma bounded_unused phi n k :
  bounded n phi -> k >= n -> unused k phi.
Proof.
  induction 1 in k |- *; intros Hk; constructor; firstorder.
  eapply bounded_unused_term; eauto.
Qed.

Lemma ZF_unused phi n :
  ZF phi -> unused n phi.
Proof.
  intros H % ZF_bounded.
  apply (bounded_unused H). lia.
Qed.





(** ** Quantifier handling *)

Class bounded_theory (T : theory) :=
  {
    bound : nat;
    bound_spec : (forall phi k, T phi -> bound <= k -> unused k phi);
  }.

Instance bt_ZF : bounded_theory ZF :=
  { bound := 0 }.
Proof.
  intros phi k H _. now apply ZF_unused.
Qed.

Instance bt_extend T (HB : bounded_theory T) (phi : form) : bounded_theory (T ⋄ phi) :=
  { bound := (proj1_sig (find_unused phi) + bound) }.
Proof.
  destruct (find_unused phi) as [n H]; cbn.
  intros psi k [HT| ->] Hk.
  - apply bound_spec; trivial. lia.
  - apply H. lia.
Qed.

Section BT.

Context {T : theory} {HB : bounded_theory T} {p : peirce} {b : bottom}.

Lemma bt_all' phi :
  let k := bound + proj1_sig (find_unused phi) in
  T ⊩ subst_form ($k..) phi -> T ⊩ ∀ phi.
Proof.
  intros k H. apply prv_T_AllI with k.
  - intros psi HP. apply bound_spec; trivial. cbn. lia.
  - unfold k. destruct (find_unused phi) as [n Hn]; cbn. apply Hn. lia.
  - assumption.
Qed.

Lemma bt_all phi :
  (forall t, T ⊩ subst_form (t..) phi) -> T ⊩ ∀ phi.
Proof.
  intros H. eapply bt_all', H.
Qed.

Lemma bt_exists' phi psi :
  let k := bound + proj1_sig (find_unused phi) + proj1_sig (find_unused psi) in
  (T ⊩ ∃ phi) -> (T ⋄ (subst_form ($k..) phi)) ⊩ psi -> T ⊩ psi.
Proof.
  intros k H1 H2. apply prv_T_ExE in H2; trivial.
  - intros theta HP. apply bound_spec; trivial. cbn. lia.
  - unfold k. destruct (find_unused psi) as [n Hn]; cbn. apply Hn. lia.
  - unfold k. destruct (find_unused phi) as [n Hn]; cbn. apply Hn. lia.
Qed.

Lemma bt_exists phi psi :
  (T ⊩ ∃ phi) -> exists t, (T ⋄ (subst_form (t..) phi)) ⊩ psi -> T ⊩ psi.
Proof.
  intros H. eexists. now apply bt_exists'.
Qed.

End BT.

Ltac assert1 H :=
  match goal with  |- (?T ⋄ ?phi) ⊩IE _ => assert (H : (T ⋄ phi) ⊩IE phi) by apply prv_T1 end.

Ltac use_exists H t :=
  eapply (@bt_exists) in H as [t H]; eauto; apply H.





(** ** Encodings are closed *)

Fixpoint tnumeral n :=
  match n with 
  | O => ∅
  | S n => σ (tnumeral n)
  end.

Fixpoint enc_derivations B n :=
  match n with 
  | O => sing (opair ∅ (enc_stack B))
  | S n => enc_derivations B n ∪ sing (opair (tnumeral (S n)) (enc_stack (derivations B (S n))))
  end.

Lemma perst_bounded0 t sigma :
  bounded_term 0 t -> bounded_term 0 (subst_term sigma t).
Proof.
  intros H. now rewrite substt_bounded0.
Qed.

Lemma enc_bool_bounded0 b :
  bounded_term 0 (enc_bool b).
Proof.
  destruct b; repeat solve_bounds.
Qed.

Lemma prep_string_bounded s t n :
  bounded_term n t -> bounded_term n (prep_string s t).
Proof.
  induction s; cbn; repeat solve_bounds; eauto.
  all: eapply bounded_term_up; try apply enc_bool_bounded0; lia.
Qed.

Lemma enc_string_bounded0 s :
  bounded_term 0 (enc_string s).
Proof.
  apply prep_string_bounded. repeat solve_bounds.
Qed.

Hint Resolve enc_string_bounded0.

Lemma tnumeral_bounded0 n :
  bounded_term 0 (tnumeral n).
Proof.
  induction n; cbn; repeat solve_bounds; trivial.
Qed.

Hint Resolve tnumeral_bounded0.

Lemma enc_stack_bounded0 B :
  bounded_term 0 (enc_stack B).
Proof.
  induction B as [|[]IH]; cbn; repeat solve_bounds; eauto.
Qed.

Hint Resolve enc_stack_bounded0.

Lemma enc_derivations_bounded0 B n :
  bounded_term 0 (enc_derivations B n).
Proof.
  induction n; cbn; repeat solve_bounds; eauto.
Qed.

Hint Resolve enc_derivations_bounded0.





(** ** Simple derivations in ZF *)

Lemma ZF_eset x :
  ZF ⊩IE ¬ (x ∈ ∅).
Proof.
  change (ZF ⊩IE (¬ ($0 ∈ ∅))[x..]).
  apply prv_T_AllE. apply elem_prv.
  right. left. reflexivity.
Qed.

Lemma ZF_eset' T x :
  ZF ⊑ T -> T ⊩IE ¬ (x ∈ ∅).
Proof.
  intros H. eapply Weak_T; eauto. apply ZF_eset.
Qed.

Lemma ZF_numeral n :
  ZF ⊩IE tnumeral n ∈ ω.
Proof.
  induction n; cbn.
  - eapply prv_T_CE1. apply elem_prv.
    do 5 right. left. reflexivity.
  - eapply prv_T_mp; try apply IHn.
    change (ZF ⊩IE ($0 ∈ ω --> σ ($0) ∈ ω)[(tnumeral n)..]).
    apply prv_T_AllE. eapply prv_T_CE2. apply elem_prv.
    do 5 right. left. reflexivity.
Qed.

Lemma ZF_refl' (T : theory) x :
  ZF ⊑ T -> T ⊩IE x ≡ x.
Proof.
  intros H. change (T ⊩IE ($0 ≡ $0)[x..]).
  apply prv_T_AllE. apply elem_prv. firstorder.
Qed.

Lemma ZF_refl x :
  ZF ⊩IE x ≡ x.
Proof.
  now apply ZF_refl'.
Qed.

Lemma ZF_sym' T x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE y ≡ x.
Proof.
  intros H1 H2. eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_sym) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y) in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_trans' T x y z :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE y ≡ z -> T ⊩IE x ≡ z.
Proof.
  intros H1 H2 H3. eapply prv_T_mp; try apply H3.
  eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_trans) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y), (prv_T_AllE z) in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_eq_elem T x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE x ∈ y -> T ⊩IE x' ∈ y'.
Proof.
  intros H1 H2 H3 H4. eapply prv_T_mp; try apply H4.
  eapply prv_T_mp; try apply H3. eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_eq_elem) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y), (prv_T_AllE x'), (prv_T_AllE y') in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_ext' T x y :
  ZF ⊑ T -> T ⊩IE sub x y -> T ⊩IE sub y x -> T ⊩IE x ≡ y.
Proof.
  intros H1 H2 H3. eapply prv_T_mp; try apply H3.
  eapply prv_T_mp; try apply H2.
  assert (H : T ⊩IE ax_ext) by (apply elem_prv; firstorder).
  now apply (prv_T_AllE x), (prv_T_AllE y) in H; cbn in H; asimpl in H.
Qed.

Lemma ZF_pair_el' (T : theory) x y z :
  ZF ⊑ T -> T ⊩IE (z ≡ x ∨ z ≡ y) <-> T ⊩IE z ∈ {x; y}.
Proof.
  intros HT; split; intros H; eapply prv_T_mp; try apply H.
  all: assert (HP : T ⊩IE ax_pair) by (apply elem_prv; firstorder).
  all: apply (prv_T_AllE y), (prv_T_AllE x), (prv_T_AllE z) in HP; cbn in HP; asimpl in HP.
  - eapply prv_T_CE2, HP.
  - eapply prv_T_CE1, HP.
Qed.

Lemma ZF_pair_el x y z :
  ZF ⊩IE (z ≡ x ∨ z ≡ y) -> ZF ⊩IE z ∈ {x; y}.
Proof.
  now apply ZF_pair_el'.
Qed.

Lemma ZF_sub_pair' x y x' y' :
  ZF ⊩IE x ≡ x' --> y ≡ y'--> sub ({x; y}) ({x'; y'}).
Proof.
  repeat apply prv_T_impl. apply bt_all. intros z. cbn. asimpl.
  apply prv_T_impl. apply ZF_pair_el'. repeat solve_tsub. eapply prv_T_DE.
  - eapply ZF_pair_el'. repeat solve_tsub. apply prv_T1.
  - apply prv_T_DI1. eapply ZF_trans'. repeat solve_tsub.
    apply prv_T1. apply elem_prv. unfold extend, contains. tauto.
  - apply prv_T_DI2. eapply ZF_trans'. repeat solve_tsub.
    apply prv_T1. apply elem_prv. unfold extend, contains. tauto.
Qed.

Lemma ZF_eq_pair' x y x' y' :
  ZF ⊩IE x ≡ x' --> y ≡ y'--> {x; y} ≡ {x'; y'}.
Proof.
  repeat apply prv_T_impl. apply ZF_ext'; trivial. solve_tsub.
  all: eapply prv_T_mp. 1,3: eapply prv_T_mp. 1,3: eapply Weak_T.
  1,3: apply ZF_sub_pair'. 1,2: solve_tsub.
  apply prv_T2. apply ZF_sym'; try apply prv_T2. solve_tsub.
  apply prv_T1. apply ZF_sym'; try apply prv_T1. solve_tsub.
Qed.

Lemma ZF_eq_pair T x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE {x; y} ≡ {x'; y'}.
Proof.
  intros HT H1 H2. eapply prv_T_mp; try apply H2.
  eapply prv_T_mp; try apply H1. eapply Weak_T; eauto.
  apply ZF_eq_pair'.
Qed.

Lemma ZF_eq_opair T x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE opair x y ≡ opair x' y'.
Proof.
  intros HT H1 H2. repeat apply ZF_eq_pair; trivial.
Qed.

Lemma ZF_sing_el x :
  ZF ⊩IE x ∈ (sing x).
Proof.
  apply ZF_pair_el. apply prv_T_DI1. apply ZF_refl.
Qed.

Lemma ZF_sing_iff T x y :
  ZF ⊑ T -> T ⊩IE x ∈ sing y <-> T ⊩IE x ≡ y.
Proof.
  intros HT. unfold sing.
  rewrite <- ZF_pair_el'; trivial.
  split; intros H.
  - now apply prv_T_DS.
  - now apply prv_T_DI1.
Qed.

Lemma ZF_union_el' (T : theory) x y z :
  ZF ⊑ T -> T ⊩IE y ∈ x ∧ z ∈ y -> T ⊩IE z ∈ ⋃ x.
Proof.
  intros HT H.
  assert (HU : T ⊩IE ax_union) by (apply elem_prv; firstorder).
  apply (prv_T_AllE x), (prv_T_AllE z) in HU; cbn in HU; asimpl in HU.
  apply prv_T_CE2 in HU. eapply prv_T_mp; try apply HU.
  apply prv_T_ExI with y. cbn. asimpl. apply H.
Qed.

Lemma ZF_union_el x y z :
  ZF ⊩IE y ∈ x ∧ z ∈ y -> ZF ⊩IE z ∈ ⋃ x.
Proof.
  now apply ZF_union_el'.
Qed.

Lemma ZF_sub_union {T} {HB : bounded_theory T} x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE sub (⋃ x) (⋃ y).
Proof.
  intros HT H. apply bt_all. intros z. cbn. asimpl. 
  apply prv_T_impl. assert1 H'.
  assert (HU : T ⋄ (z ∈ ⋃ x) ⊩IE ax_union) by (apply elem_prv; firstorder).
  apply (prv_T_AllE x), (prv_T_AllE z) in HU; cbn in HU; asimpl in HU.
  apply prv_T_CE1 in HU. eapply (prv_T_mp HU) in H'.
  use_exists H' u. cbn. asimpl. clear H' HU.
  eapply ZF_union_el'. repeat solve_tsub. apply prv_T_CI.
  - eapply ZF_eq_elem. repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
    apply (Weak_T H). repeat solve_tsub. eapply prv_T_CE1, prv_T1.
  - eapply prv_T_CE2, prv_T1.
Qed.

Lemma ZF_eq_union {T} {HB : bounded_theory T} x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE ⋃ x ≡ ⋃ y.
Proof.
  intros HT H. apply ZF_ext'; try apply ZF_sub_union; trivial.
  now apply ZF_sym'.
Qed.

Lemma ZF_bunion_el' T x y z :
  ZF ⊑ T -> T ⊩IE (z ∈ x ∨ z ∈ y) -> T ⊩IE z ∈ x ∪ y.
Proof.
  intros HT H. apply (prv_T_DE H).
  - eapply ZF_union_el' with x. solve_tsub. apply prv_T_CI; try apply prv_T1.
    apply ZF_pair_el'. solve_tsub. apply prv_T_DI1. apply ZF_refl'. solve_tsub.
  - eapply ZF_union_el' with y. solve_tsub. apply prv_T_CI; try apply prv_T1.
    apply ZF_pair_el'. solve_tsub. apply prv_T_DI2. apply ZF_refl'. solve_tsub.
Qed.

Lemma ZF_bunion_el x y z :
  ZF ⊩IE (z ∈ x ∨ z ∈ y) -> ZF ⊩IE z ∈ x ∪ y.
Proof.
  now apply ZF_bunion_el'.
Qed.

Lemma ZF_bunion_inv' x y z :
   ZF ⊩IE z ∈ x ∪ y --> z ∈ x ∨ z ∈ y.
Proof.
  assert (TU : ZF ⊩IE ax_union) by (apply elem_prv; firstorder).
  pose (upair (x y : term) := {x; y}).
  eapply (prv_T_AllE (upair x y)), (prv_T_AllE z) in TU; fold subst_form in TU.
  apply prv_T_CE1 in TU; fold subst_form in TU. cbn in TU; asimpl in TU.
  apply (prv_T_imps TU). apply prv_T_impl.
  assert1 H. use_exists H u. cbn. asimpl. clear H. apply prv_clear2.
  eapply prv_T_DE. apply ZF_pair_el'. repeat solve_tsub.
  + eapply prv_T_CE1. apply prv_T1.
  + apply prv_T_DI1. eapply ZF_eq_elem. repeat solve_tsub.
    apply ZF_refl'. repeat solve_tsub. apply prv_T1.
    eapply prv_T_CE2. apply prv_T2.
  + apply prv_T_DI2. eapply ZF_eq_elem. repeat solve_tsub.
    apply ZF_refl'. repeat solve_tsub. apply prv_T1.
    eapply prv_T_CE2. apply prv_T2.
Qed.

Lemma ZF_bunion_inv T x y z :
   ZF ⊑ T -> T ⊩IE z ∈ x ∪ y -> T ⊩IE z ∈ x ∨ z ∈ y.
Proof.
  intros HT H. eapply prv_T_mp; try apply H.
  eapply Weak_T; try apply HT. apply ZF_bunion_inv'.
Qed.

Lemma ZF_eq_bunion {T} {HB : bounded_theory T} x y x' y' :
  ZF ⊑ T -> T ⊩IE x ≡ x' -> T ⊩IE y ≡ y' -> T ⊩IE x ∪ y ≡ x' ∪ y'.
Proof.
  intros HT H1 H2. now apply ZF_eq_union, ZF_eq_pair.
Qed.

Lemma ZF_sig_el T x :
   ZF ⊑ T -> T ⊩IE x ∈ σ x.
Proof.
  intros H. apply ZF_bunion_el'; trivial.
  apply prv_T_DI2. apply ZF_sing_iff; trivial.
  apply ZF_refl'. trivial.
Qed.

Lemma ZF_eq_sig {T} {HB : bounded_theory T} x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE σ x ≡ σ y.
Proof.
  intros HT H. now apply ZF_eq_bunion, ZF_eq_pair.
Qed.

Lemma sing_pair1 T x y z :
  ZF ⊑ T -> T ⊩IE sing x ≡ {y; z} -> T ⊩IE x ≡ y.
Proof.
  intros HT H. apply ZF_sym'; trivial.
  apply ZF_sing_iff; trivial. eapply ZF_eq_elem; trivial.
  apply ZF_refl'; trivial. apply ZF_sym'; eauto.
  apply ZF_pair_el'; trivial. apply prv_T_DI1. now apply ZF_refl'.
Qed.

Lemma sing_pair2 T x y z :
  ZF ⊑ T -> T ⊩IE sing x ≡ {y; z} -> T ⊩IE x ≡ z.
Proof.
  intros HT H. apply ZF_sym'; trivial.
  apply ZF_sing_iff; trivial. eapply ZF_eq_elem; trivial.
  apply ZF_refl'; trivial. apply ZF_sym'; eauto.
  apply ZF_pair_el'; trivial. apply prv_T_DI2. now apply ZF_refl'.
Qed.

Lemma opair_inj1 T x y x' y' :
  ZF ⊑ T -> T ⊩IE opair x y ≡ opair x' y' -> T ⊩IE x ≡ x'.
Proof.
  intros HT He. assert (H : T ⊩IE {x; x} ∈ opair x y).
  { apply ZF_pair_el'; trivial. apply prv_T_DI1. now apply ZF_refl'. }
  eapply ZF_eq_elem in H; try apply He; try apply ZF_refl'; trivial.
  apply ZF_pair_el' in H; trivial.
  apply (prv_T_DE H); eapply sing_pair1; try apply prv_T1; solve_tsub.
Qed.

Lemma opair_inj2 T x y x' y' :
  ZF ⊑ T -> T ⊩IE opair x y ≡ opair x' y' -> T ⊩IE y ≡ y'.
Proof.
  intros HT H. assert (H' : T ⊩IE y ≡ x' ∨ y ≡ y').
  - assert (H2 : T ⊩IE {x; y} ∈ opair x' y').
    { eapply ZF_eq_elem; trivial. apply ZF_refl'; trivial. apply H.
      apply ZF_pair_el'; trivial. apply prv_T_DI2. now apply ZF_refl'. }
    apply ZF_pair_el' in H2; trivial. apply (prv_T_DE H2).
    + apply prv_T_DI1. apply ZF_sym'. solve_tsub. eapply sing_pair2.
      solve_tsub. apply ZF_sym'; try apply prv_T1. solve_tsub.
    + apply ZF_pair_el'. solve_tsub. eapply ZF_eq_elem; try apply prv_T1. solve_tsub.
      apply ZF_refl'. solve_tsub. apply ZF_pair_el'. solve_tsub.
      apply prv_T_DI2. apply ZF_refl'. solve_tsub.
  - apply (prv_T_DE H'); try apply prv_T1.
    assert (H1 : T ⊩IE x ≡ x') by apply (opair_inj1 HT H).
    assert (H2 : T ⊩IE {x'; y'} ∈ opair x y).
    { eapply ZF_eq_elem; trivial. apply ZF_refl'; trivial. apply ZF_sym', H; trivial.
      apply ZF_pair_el'; trivial. apply prv_T_DI2. now apply ZF_refl'. }
    apply ZF_pair_el' in H2; trivial.
    eapply prv_T_DE; try eapply (Weak_T H2). repeat solve_tsub.
    + eapply ZF_trans'; try apply prv_T2. repeat solve_tsub.
      eapply ZF_trans'. repeat solve_tsub. apply ZF_sym'. repeat solve_tsub.
      apply (Weak_T H1). repeat solve_tsub. eapply sing_pair2. repeat solve_tsub.
      apply ZF_sym'; try apply prv_T1. repeat solve_tsub.
    + eapply ZF_trans'; try apply prv_T2. repeat solve_tsub.
      eapply sing_pair2. repeat solve_tsub. eapply ZF_trans'. repeat solve_tsub.
      2: apply ZF_sym'; try apply prv_T1. 2: repeat solve_tsub.
      eapply ZF_eq_pair; try apply ZF_sym'; try apply prv_T2.
      3: apply (Weak_T H1). all: repeat solve_tsub.
Qed.

Lemma ZF_bunion_el1 T x y z :
  ZF ⊑ T -> T ⊩IE z ∈ x -> T ⊩IE z ∈ x ∪ y.
Proof.
  intros HT H. now apply ZF_bunion_el', prv_T_DI1.
Qed.

Lemma ZF_bunion_el2 T x y z :
  ZF ⊑ T -> T ⊩IE z ∈ y -> T ⊩IE z ∈ x ∪ y.
Proof.
  intros HT H. now apply ZF_bunion_el', prv_T_DI2.
Qed.
 
Lemma bunion_eset x :
   ZF ⊩IE ∅ ∪ x ≡ x.
Proof.
  apply ZF_ext'; try apply ZF_all, prv_T_impl; cbn. solve_tsub. 
  - eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
    + apply prv_T_exf. eapply prv_T_mp; try apply prv_T1.
      eapply Weak_T; try apply ZF_eset. repeat solve_tsub.
    + apply prv_T1.
  - apply ZF_bunion_el2, prv_T1. repeat solve_tsub.
Qed.

Lemma bunion_swap x y z :
  ZF ⊩IE (x ∪ y) ∪ z ≡ (x ∪ z) ∪ y.
Proof.
  apply ZF_ext'; try apply ZF_all, prv_T_impl; cbn. solve_tsub.
  - eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
    + eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
      * apply ZF_bunion_el1, ZF_bunion_el1, prv_T1. all: repeat solve_tsub.
      * apply ZF_bunion_el2, prv_T1. repeat solve_tsub.
    + apply ZF_bunion_el1, ZF_bunion_el2, prv_T1. all: repeat solve_tsub.
  - eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
    + eapply prv_T_DE. eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
      * apply ZF_bunion_el1, ZF_bunion_el1, prv_T1. all: repeat solve_tsub.
      * apply ZF_bunion_el2, prv_T1. repeat solve_tsub.
    + apply ZF_bunion_el1, ZF_bunion_el2, prv_T1. all: repeat solve_tsub.
Qed.

Lemma bunion_use T x y z phi :
  ZF ⊑ T -> T ⋄ (x ∈ y) ⊩IE phi -> T ⋄ (x ≡ z) ⊩IE phi -> T ⊩IE x ∈ y ∪ sing z --> phi.
Proof.
  intros HT H1 H2. apply prv_T_impl. eapply prv_T_DE.
  - eapply ZF_bunion_inv. repeat solve_tsub. apply prv_T1.
  - apply (Weak_T H1). intros psi. unfold extend, contains. tauto.
  - eapply prv_T_remove.
    + rewrite <- ZF_sing_iff. apply prv_T1. repeat solve_tsub.
    + apply (Weak_T H2). intros psi. unfold extend, contains. tauto.
Qed.

Lemma ZF_numeral_trans T n x y :
  ZF ⊑ T -> T ⊩IE x ∈ tnumeral n --> y ∈ x --> y ∈ tnumeral n.
Proof.
  intros HT. induction n; cbn.
  - apply prv_T_impl, prv_T_exf.
    eapply prv_T_mp; try apply prv_T1.
    apply ZF_eset'. repeat solve_tsub.
  - apply bunion_use; trivial.
    + apply prv_T_imp in IHn. apply (prv_T_imps IHn).
      apply prv_T_impl. apply ZF_bunion_el1, prv_T1. repeat solve_tsub.
    + apply prv_T_impl. apply ZF_bunion_el'. repeat solve_tsub.
      apply prv_T_DI1. eapply ZF_eq_elem; try apply prv_T2; try apply prv_T1.
      repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
Qed.

Lemma ZF_numeral_wf T n :
  ZF ⊑ T -> T ⊩IE ¬ (tnumeral n ∈ tnumeral n).
Proof.
  intros HT. induction n; cbn.
  - now apply ZF_eset'.
  - apply bunion_use; trivial.
    + eapply prv_T_mp. apply (Weak_T IHn). repeat solve_tsub.
      eapply prv_T_mp. eapply prv_T_mp. apply ZF_numeral_trans. repeat solve_tsub.
      apply prv_T1. apply ZF_sig_el. repeat solve_tsub.
    + eapply prv_T_mp. apply (Weak_T IHn). repeat solve_tsub.
      eapply ZF_eq_elem. repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
      apply prv_T1. apply ZF_sig_el. repeat solve_tsub.
Qed.





(** ** Preservation proof *)

Lemma enc_derivations_base R n :
  ZF ⊩IE {{∅; ∅}; {∅; enc_stack R}} ∈ enc_derivations R n.
Proof.
  induction n; cbn.
  - apply ZF_sing_el.
  - apply ZF_bunion_el. now apply prv_T_DI1.
Qed.

Lemma enc_derivations_step B n :
  ZF ⊩IE opair (tnumeral n) (enc_stack (derivations B n)) ∈ enc_derivations B n.
Proof.
  destruct n; cbn.
  - apply ZF_sing_el.
  - apply ZF_bunion_el. apply prv_T_DI2. apply ZF_sing_el.
Qed.

Lemma enc_stack_spec R s t :
  s/t el R -> ZF ⊩IE opair (enc_string s) (enc_string t) ∈ enc_stack R.
Proof.
  induction R as [|[u v] R IH]; cbn; auto.
  intros [[=]| H]; subst.
  - apply ZF_bunion_el. apply prv_T_DI2. apply ZF_sing_el.
  - apply ZF_bunion_el. apply prv_T_DI1. now apply IH.
Qed.

Lemma ZF_derivations_bound T B k n x :
  ZF ⊑ T -> T ⊩IE opair k x ∈ enc_derivations B n -> T ⊩IE k ∈ σ (tnumeral n).
Proof.
  induction n in T |- *; cbn; intros HT H.
  - apply ZF_sing_iff in H; trivial. eapply ZF_eq_elem; trivial.
    apply ZF_sym'; trivial. eapply opair_inj1; trivial. apply H.
    apply ZF_refl'; trivial. eapply ZF_bunion_el'; trivial.
    apply prv_T_DI2. apply ZF_sing_iff; trivial. apply ZF_refl'; trivial.
  - apply ZF_bunion_inv in H; trivial. apply (prv_T_DE H).
    + apply ZF_bunion_el1. solve_tsub. apply IHn; try apply prv_T1. solve_tsub.
    + apply ZF_bunion_el2. solve_tsub. apply ZF_sing_iff. solve_tsub.
      eapply opair_inj1. solve_tsub. apply ZF_sing_iff; try apply prv_T1. solve_tsub.
Qed.

Lemma enc_derivations_functional B n :
  ZF ⊩IE opair $2 $1 ∈ enc_derivations B n --> opair $2 $0 ∈ enc_derivations B n --> $ 1 ≡ $ 0.
Proof.
  induction n; cbn -[derivations].
  - repeat apply prv_T_impl. eapply opair_inj2. repeat solve_tsub. eapply ZF_trans'. repeat solve_tsub.
    + apply ZF_sing_iff; try apply prv_T2. repeat solve_tsub.
    + apply ZF_sym'. repeat solve_tsub. apply ZF_sing_iff; try apply prv_T1. repeat solve_tsub.
  - apply bunion_use; try apply bunion_use. 1,2,5: repeat solve_tsub.
    + repeat apply prv_T_imp. now apply (Weak_T IHn).
    + apply prv_T_exf. eapply prv_T_mp. apply (@ZF_numeral_wf _ (S n)). solve_tsub.
      eapply ZF_derivations_bound. solve_tsub. eapply ZF_eq_elem; try apply prv_T2. solve_tsub.
      2: apply ZF_refl'. 2: solve_tsub. apply ZF_eq_opair. solve_tsub.
      eapply opair_inj1; try apply prv_T1. solve_tsub. apply ZF_refl'. solve_tsub.
    + apply prv_T_exf. eapply prv_T_mp. apply (@ZF_numeral_wf _ (S n)). solve_tsub.
      eapply ZF_derivations_bound. solve_tsub. eapply ZF_eq_elem; try apply prv_T1. solve_tsub.
      2: apply ZF_refl'. 2: solve_tsub. apply ZF_eq_opair. solve_tsub.
      eapply opair_inj1; try apply prv_T2. solve_tsub. apply ZF_refl'. solve_tsub.
    + eapply opair_inj2. solve_tsub. eapply ZF_trans'; try apply prv_T2. solve_tsub.
      apply ZF_sym'; try apply prv_T1. solve_tsub.
Qed.

Lemma prep_string_subst sigma s x :
  subst_term sigma (prep_string s x) = prep_string s (subst_term sigma x).
Proof.
  induction s; cbn; trivial. rewrite IHs.
  rewrite substt_bounded0; eauto.
  apply enc_bool_bounded0.
Qed.

Lemma is_rep_subst s t x y sigma :
  subst_form sigma (is_rep (comb_rel s t) x y) =
  is_rep (comb_rel s t) (subst_term sigma x) (subst_term sigma y).
Proof.
  unfold is_rep. cbn -[comb_rel]. asimpl. repeat f_equal.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
  - unfold comb_rel. cbn. rewrite !prep_string_subst. reflexivity.
Qed.

Lemma combinations_subst B x y sigma :
  subst_form sigma (combinations B x y) = combinations B (subst_term sigma x) (subst_term sigma y).
Proof.
  induction B as [|[s t] B IH] in sigma, x, y |- *.
  - cbn. reflexivity.
  - cbn -[is_rep]. rewrite IH, is_rep_subst. cbn -[is_rep]. now asimpl.
Qed.

Lemma enc_derivations_eq T B n x :
  ZF ⊑ T -> T ⊩IE opair (tnumeral n) x ∈ enc_derivations B n -> T ⊩IE x ≡ enc_stack (derivations B n).
Proof.
  intros HT H. destruct n; cbn in *.
  - eapply opair_inj2; trivial. eapply ZF_sing_iff; eauto.
  - apply ZF_bunion_inv in H; trivial. apply (prv_T_DE H).
    + apply prv_T_exf. eapply prv_T_mp. apply (ZF_numeral_wf (S n)). solve_tsub.
      eapply ZF_derivations_bound. solve_tsub. apply prv_T1.
    + eapply opair_inj2. solve_tsub. apply ZF_sing_iff. solve_tsub. apply prv_T1.
Qed.

Lemma enc_stack_app {T} {HB : bounded_theory T} B C :
  ZF ⊑ T -> T ⊩IE (enc_stack B) ∪ (enc_stack C) ≡ enc_stack (B ++ C).
Proof.
  intros HT. induction B as [|[s t] B IH]; cbn.
  - eapply Weak_T; try apply bunion_eset. assumption.
  - eapply ZF_trans'; trivial. eapply Weak_T; try apply bunion_swap; trivial.
    eapply ZF_eq_bunion; trivial. apply ZF_refl'; trivial.
Qed.

Lemma prep_string_app s t x :
  prep_string (s ++ t) x = prep_string s (prep_string t x).
Proof.
  induction s; cbn; congruence.
Qed.

Lemma ZF_eq_prep T s x y :
  ZF ⊑ T -> T ⊩IE x ≡ y -> T ⊩IE prep_string s x ≡ prep_string s y.
Proof.
  intros HT H. induction s; cbn; try tauto.
  apply ZF_eq_opair; trivial. now apply ZF_refl'.
Qed.

Lemma append_all_el T B s t x y :
  ZF ⊑ T -> T ⊩IE opair x y ∈ enc_stack B
  -> T ⊩IE opair (prep_string s x) (prep_string t y) ∈ enc_stack (append_all B (s/t)).
Proof.
  intros HT H. induction B as [|[u v] B IH] in T, HT, H |- *; cbn in *.
  - apply prv_T_exf. eapply prv_T_mp. 2: apply H. now apply ZF_eset'.
  - eapply (ZF_bunion_el' HT). eapply prv_T_DE. apply (ZF_bunion_inv HT H).
    + apply prv_T_DI1. apply IH; try apply prv_T1. solve_tsub.
    + assert1 H'. apply ZF_sing_iff in H'; try now solve_tsub.
      apply prv_T_DI2. apply ZF_sing_iff. solve_tsub.
      rewrite !prep_string_app. apply ZF_eq_opair. solve_tsub.
      * apply ZF_eq_prep. solve_tsub. eapply opair_inj1; eauto. solve_tsub.
      * apply ZF_eq_prep. solve_tsub. eapply opair_inj2; eauto. solve_tsub.
Qed.

Lemma is_rep_eq {T} {HB : bounded_theory T} B s t x y :
  ZF ⊑ T -> T ⊩IE x ≡ enc_stack B -> T ⊩IE is_rep (comb_rel s t) x y
  -> T ⊩IE y ≡ enc_stack (append_all B (s / t)).
Proof.
  intros HT H1 H2. apply ZF_ext'; trivial.
  - apply bt_all. intros a. cbn.
    eapply prv_T_AllE in H2. cbn -[comb_rel] in H2.
    eapply prv_T_CE1 in H2. eapply prv_T_imps. apply H2.
    apply prv_T_impl. assert1 H. use_exists H b. apply prv_clear2. clear H.
    cbn -[comb_rel]. asimpl. assert1 H. apply prv_T_CE in H as [H H'].
    unfold comb_rel at 2 in H'. cbn -[comb_rel] in H'. asimpl in H'.
    rewrite !prep_string_subst in H'. cbn -[comb_rel] in H'. 
    use_exists H' c. clear H'.
    cbn -[comb_rel]. asimpl. rewrite !prep_string_subst. cbn -[comb_rel].
    assert1 H'. use_exists H' d. clear H'.
    cbn -[comb_rel]. asimpl. rewrite !prep_string_subst. cbn -[comb_rel]. asimpl.
    eapply ZF_eq_elem. repeat solve_tsub. apply ZF_sym'. repeat solve_tsub.
    eapply prv_T_CE2. apply prv_T1. apply ZF_refl'. repeat solve_tsub.
    apply append_all_el. repeat solve_tsub.
    eapply ZF_eq_elem. repeat solve_tsub. eapply prv_T_CE1. apply prv_T1.
    eapply (Weak_T H1). repeat solve_tsub. eapply (Weak_T H). repeat solve_tsub.
  - apply bt_all. intros a. cbn. asimpl.
    apply (@prv_T_AllE _ _ _ _ a) in H2. cbn -[comb_rel] in H2. asimpl in H2.
    eapply prv_T_CE2 in H2. eapply prv_T_imps. 2: apply H2. clear H2. apply prv_T_impl.
    induction B as [|[u v] B IH] in T, x, HT, H1, HB |- *; cbn -[comb_rel] in *.
    + apply prv_T_exf. eapply prv_T_mp; try apply prv_T1. apply ZF_eset'. repeat solve_tsub.
    + apply prv_T_imp. apply bunion_use; trivial.
      * specialize (IH T HB (enc_stack B) HT).
        assert (H : T ⊩IE enc_stack B ≡ enc_stack B) by now apply ZF_refl'.
        apply IH in H. use_exists H z. clear H. apply prv_T_ExI with z.
        cbn -[comb_rel]. asimpl. assert1 H. apply prv_T_CE in H as [H H'].
        apply prv_T_CI; trivial. eapply ZF_eq_elem. repeat solve_tsub.
        apply ZF_refl'. repeat solve_tsub. apply ZF_sym'. repeat solve_tsub.
        apply (Weak_T H1). repeat solve_tsub. apply ZF_bunion_el1; trivial. repeat solve_tsub.
      * apply prv_T_ExI with (opair (enc_string u) (enc_string v)).
        cbn -[comb_rel]. asimpl. apply prv_T_CI.
        -- eapply ZF_eq_elem. repeat solve_tsub. apply ZF_refl'. repeat solve_tsub.
           apply ZF_sym'. repeat solve_tsub. apply (Weak_T H1). repeat solve_tsub.
           apply ZF_bunion_el2. repeat solve_tsub. eapply Weak_T. apply ZF_sing_el.
           repeat solve_tsub.
        -- cbn. apply prv_T_ExI with (enc_string v).
           cbn. apply prv_T_ExI with (enc_string u).
           cbn. asimpl. rewrite !prep_string_subst, !prep_string_app; cbn.
           apply prv_T_CI; try apply prv_T1. apply ZF_refl'. repeat solve_tsub.
Qed.

Lemma combinations_eq {T} {HB : bounded_theory T} B C x y :
  ZF ⊑ T -> T ⊩IE x ≡ enc_stack C -> T ⊩IE combinations B x y -> T ⊩IE y ≡ enc_stack (derivation_step B C).
Proof.
  induction B as [|[s t] B IH] in y, T, HB |-*; cbn; intros HT H1 H2; trivial.
  use_exists H2 u. clear H2. cbn -[is_rep]. asimpl. assert1 H. use_exists H v. clear H. apply prv_clear2.
  cbn -[is_rep]. asimpl. rewrite !combinations_subst, !is_rep_subst. cbn -[is_rep]. asimpl.
  eapply ZF_trans'. solve_tsub. eapply prv_T_CE1. apply prv_T1.
  eapply ZF_trans'. solve_tsub. 2: apply enc_stack_app; eauto. 2: solve_tsub.
  apply ZF_eq_bunion; eauto. solve_tsub.
  - eapply is_rep_eq; eauto. solve_tsub. apply prv_clear1. eauto.
    eapply prv_T_CE2. eapply prv_T_CE2. apply prv_T1.
  - apply IH; eauto. solve_tsub.
    + now apply prv_clear1.
    + eapply prv_T_CE1. eapply prv_T_CE2. apply prv_T1.
Qed.

Lemma combinations_step B n (i x y : term) :
  ZF ⊩IE i ∈ tnumeral n --> opair i x ∈ enc_derivations B n
     --> combinations B x y --> opair (σ i) y ∈ enc_derivations B n.
Proof.
  induction n; cbn.
  - apply prv_T_impl. apply prv_T_exf.
    apply prv_T_imp. apply ZF_eset.
  - apply bunion_use; try apply bunion_use.
    apply tsubs_refl. 1, 4: apply tsubs_extend.
    + apply prv_T_impl. apply ZF_bunion_el'. repeat solve_tsub.
      apply prv_T_DI1. eapply prv_T_mp. eapply prv_T_mp. eapply prv_T_mp.
      * eapply Weak_T. apply IHn. repeat solve_tsub.
      * apply prv_T3.
      * apply prv_T2.
      * apply prv_T1.
    + apply prv_T_exf. eapply prv_T_mp. apply (ZF_numeral_wf (S n)). solve_tsub.
      eapply ZF_eq_elem. solve_tsub. eapply opair_inj1. solve_tsub. apply prv_T1.
      apply ZF_refl'. solve_tsub. cbn. apply ZF_bunion_el'. solve_tsub.
      apply prv_T_DI1. apply prv_T2.
    + apply prv_T_impl. apply ZF_bunion_el'. repeat solve_tsub.
      apply prv_T_DI2. apply ZF_sing_iff. repeat solve_tsub.
      apply ZF_eq_opair. repeat solve_tsub.
      * apply ZF_eq_sig; eauto. repeat solve_tsub. apply prv_T3.
      * eapply combinations_eq; eauto; try apply prv_T1. repeat solve_tsub.
        apply enc_derivations_eq. repeat solve_tsub.
        eapply ZF_eq_elem; try apply prv_T2; try apply ZF_refl'. 1, 3: repeat solve_tsub.
        eapply ZF_eq_opair; try apply prv_T3; try apply ZF_refl'. all: repeat solve_tsub.
    + apply prv_T_exf. eapply prv_T_mp. apply (ZF_numeral_wf n). solve_tsub.
      eapply ZF_eq_elem. solve_tsub. apply ZF_refl'. solve_tsub.
      eapply ZF_trans'. solve_tsub. apply ZF_sym'. solve_tsub.
      eapply opair_inj1. solve_tsub. apply prv_T1. apply prv_T2.
      apply ZF_sig_el. solve_tsub.
Qed.

Theorem BPCP_slv B :
  BPCP' B -> ZF ⊩IE solvable B.
Proof.
  intros [s H]. destruct (derivable_derivations H) as [n Hn].
  apply prv_T_ExI with (tnumeral n);
  apply prv_T_ExI with (enc_derivations B n);
  apply prv_T_ExI with (opair (enc_string s) (enc_string s));
  apply prv_T_ExI with (enc_string s);
  apply prv_T_ExI with (enc_stack (derivations B n)); fold subst_form.
  cbn; rewrite !substt_bounded0; repeat apply perst_bounded0; eauto.
  repeat apply prv_T_CI.
  - apply ZF_numeral.
  - repeat apply ZF_all. asimpl. unfold unscoped.shift.
    apply enc_derivations_functional.
  - apply enc_derivations_base.
  - repeat apply ZF_all. rewrite !combinations_subst. cbn. asimpl.
    rewrite !combinations_subst. cbn. unfold unscoped.shift.
    apply combinations_step.
  - apply enc_derivations_step.
  - now apply enc_stack_spec.
  - apply ZF_refl.
Qed.

Print Assumptions BPCP_slv.





(** Reflection proof *)

Section Soundness.

  Context {p : peirce} {b : bottom}.

  Hint Unfold valid_L.

  Lemma Soundness C A phi :
    A ⊢ phi -> (p = class -> con_subs classical C) -> valid_L C A phi.
  Proof.
    induction 1; intros Hclass D I HC rho HA; (eauto || (comp; eauto)).
    - intros Hphi. capply IHprv. intros ? []; subst. assumption. now apply HA.
    - intros d. capply IHprv. intros psi [psi'[<- H' % HA]] % in_map_iff.
      eapply sat_comp. now comp.
    - eapply sat_comp, sat_ext. 2: apply (IHprv Hclass D I HC rho HA (eval rho t)).
      now intros []; asimpl.
    - exists (eval rho t). cbn. specialize (IHprv Hclass D I HC rho HA).
      apply sat_comp in IHprv. comp. apply IHprv.
    - edestruct IHprv1 as [d HD]; eauto.
      assert (H' : forall psi, phi = psi \/ psi el [theta[form_shift] | theta ∈ A] -> (d.:rho) ⊨ psi).
      + intros P [<-|[psi'[<- H' % HA]] % in_map_iff]; trivial. apply sat_comp. apply H'.
      + specialize (IHprv2 Hclass D I HC (d.:rho) H'). apply sat_comp in IHprv2. apply IHprv2.
    - firstorder.
    - firstorder.
    - firstorder.
    - edestruct IHprv1; eauto.
      + apply IHprv2; trivial. intros xi [<-|HX]; auto.
      + apply IHprv3; trivial. intros xi [<-|HX]; auto.
    - apply (Hclass eq_refl D I HC).
  Qed.

  Lemma StrongSoundness C T phi :
    T ⊩ phi -> (p = class -> con_subs classical C) -> valid_T C T phi.
  Proof.
    intros (A & HA1 & HA2) Hclass D I HC rho HT. eapply Soundness in HA2; eauto.
  Qed.

End Soundness.

Lemma StrongSoundnessIE T phi :
  T ⊩IE phi -> valid_T (fun _ _ => True) T phi.
Proof.
  intros H. eapply StrongSoundness. apply H. discriminate.
Qed.

Theorem BPCP_slv' B :
  (exists M : ZF_Model, extensional M /\ standard M) -> ZF ⊩IE solvable B -> BPCP' B.
Proof.
  intros HE H % StrongSoundnessIE. eapply PCP_ZF; trivial. intros M HM rho. apply (H M); trivial.
  intros phi [->|[->|[->|[->|[->|[->|[->|[[psi [H' ->]]|[[psi [H' ->]]|[->|[->|[->| ->]]]]]]]]]]]]; try apply M; trivial.
  - intros x. cbn. apply HM. reflexivity.
  - intros x y Hx % HM. cbn in *. apply HM. congruence.
  - intros x y z Hx % HM Hy % HM. cbn in *. apply HM. congruence.
  - intros x y x' y' Hx % HM Hy % HM. cbn in *. congruence.
Qed.





(** ** Main results *)

Theorem PCP_ZFD B :
  (exists M : ZF_Model, extensional M /\ standard M) -> BPCP' B <-> ZF ⊩IE solvable B.
Proof.
  intros H. split.
  - apply BPCP_slv.
  - now apply BPCP_slv'.
Qed.

Print Assumptions PCP_ZFD.

From Undecidability.FOLP Require Import ZF_model.

Corollary PCP_ZFD' B :
  inhabited extensional_normaliser -> BPCP' B <-> ZF ⊩IE solvable B.
Proof.
  intros H % extnorm_stanmod. now apply PCP_ZFD.
Qed.





(** ** Incompleteness *)

Section Completeness.

  Context {bt : bottom} {pe : peirce}.
  Variable T : theory.

  Variable f : nat -> option form.
  Hypothesis HF : forall phi, tprv T phi <-> (exists n, f n = Some phi).

  Definition tprv_decide' (phi : form) (n : nat) : option bool.
  Proof.
    destruct (f n) as [psi|] eqn : Hn.
    - decide (psi = phi). exact (Some true).
      decide (psi = ¬ phi). exact (Some false).
      exact None.
    - exact None.
  Defined.

  Definition complete :=
    forall phi, T ⊩ phi \/ T ⊩ ¬ phi.

  Hypothesis HT : complete.

  Lemma neg_neq phi :
    ¬ phi <> phi.
  Proof.
    induction phi; cbn; congruence.
  Qed.

  Lemma complete_total phi :
    exists n b, tprv_decide' phi n = Some b.
  Proof.
    destruct (HT phi) as [HP|HP].
    - apply HF in HP as [n HN]. exists n, true.
      unfold tprv_decide'. rewrite HN.
      decide _; tauto.
    - apply HF in HP as [n HN]. exists n, false.
      unfold tprv_decide'. rewrite HN.
      decide _. now apply neg_neq in e. decide _; tauto.
  Qed.

  Lemma exist_bool_dec (P : bool -> Prop) :
    (forall b, dec (P b)) -> dec (exists b, P b).
  Proof.
    intros d.
    destruct (d true). left. now exists true.
    destruct (d false). left. now exists false.
    right. intros [[] H]; tauto.
  Qed.

  Lemma exist_bool_reify (P : bool -> Prop) :
    (forall b, dec (P b)) -> (exists b, P b) -> sig (fun b => P b).
  Proof.
    intros d H.
    destruct (d true). now exists true.
    destruct (d false). now exists false.
    exfalso. destruct H as [[] H]; tauto.                        
  Qed.

  Require Import Coq.Logic.ConstructiveEpsilon.

  Lemma complete_total'' phi :
    sig (fun n => exists b, tprv_decide' phi n = Some b).
  Proof.
    apply constructive_indefinite_ground_description_nat.
    - intros n. apply exist_bool_dec. intros b.
      unfold dec. repeat decide equality.
    - apply complete_total.
  Qed.

  Lemma complete_total' phi :
    sigT (fun n => sig (fun b => tprv_decide' phi n = Some b)).
  Proof.
    destruct (complete_total'' phi) as [n H].
    exists n. apply exist_bool_reify; trivial.
    intros b. unfold dec. repeat decide equality.
  Qed.

  Definition tprv_decide phi : bool :=
    let (_, H) := complete_total' phi in let (b, _) := H in b.

  Definition consistent :=
    forall phi, ~ (T ⊩ phi /\ T ⊩ ¬ phi).

  Hypothesis HC : consistent.

  Theorem complete_dec :
    decidable (tprv T).
  Proof.
    exists tprv_decide. intros phi. unfold tprv_decide.
    destruct complete_total' as [n[b H]].
    unfold tprv_decide' in H. destruct (f n) as [psi|] eqn : Hn.
    - decide (psi = phi); subst. split; try congruence. intros _. apply HF. now exists n.
      decide (psi = ¬ phi); subst; try congruence. split; try congruence.
      intros H'. exfalso. apply (@HC phi). split; trivial.
      apply HF. now exists n.
    - congruence.
  Qed.

End Completeness.


