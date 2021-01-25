(* * Reduction to semantic ZF entailment *)

Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski_facts.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Reductions.PCPb_to_ZF.
Require Import Lia.

From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

Require Import Morphisms.



(* ** Internal axioms *)

Section ZF.

  Context { V : Type }.
  Context { M : interp V }.

  Hypothesis M_ZF : forall rho, rho ⊫ ZFeq'.

  Definition set_equiv x y :=
    x ≡ y.

  Notation "x ≡' y" := (set_equiv x y) (at level 35).

  Definition set_elem x y :=
    x ∈ y.

  Notation "x ∈' y" := (set_elem x y) (at level 35).
  Notation "x ⊆' y" := (forall z, z ∈' x -> z ∈' y) (at level 35).

  Instance set_equiv_equiv :
    Equivalence set_equiv.
  Proof.
    split.
    - apply (@M_ZF (fun _ => ∅) ax_refl). cbn; tauto.
    - apply (@M_ZF (fun _ => ∅) ax_sym). cbn; tauto.
    - apply (@M_ZF (fun _ => ∅) ax_trans). cbn; tauto.
  Qed.

  Instance set_equiv_elem :
    Proper (set_equiv ==> set_equiv ==> iff) set_elem.
  Proof.
    intros x x' Hx y y' Hy. split.
    - apply (@M_ZF (fun _ => ∅) ax_eq_elem); cbn; tauto.
    - symmetry in Hx, Hy. apply (@M_ZF (fun _ => ∅) ax_eq_elem); cbn; tauto.
  Qed.

  Lemma set_equiv_refl' x :
    x ≡' x.
  Proof.
    apply set_equiv_equiv.
  Qed.

  Lemma set_equiv_refl x :
    x ≡ x.
  Proof.
    apply set_equiv_equiv.
  Qed.
  
  Hint Resolve set_equiv_refl set_equiv_refl' : core.
  
  Lemma M_ext x y :
    x ⊆' y -> y ⊆' x -> x ≡' y.
  Proof.
    apply (@M_ZF (fun _ => ∅) ax_ext). cbn; tauto.
  Qed.

  Lemma M_eset x :
    ~ x ∈' ∅.
  Proof.
    refine (@M_ZF (fun _ => ∅) ax_eset _ x). cbn; tauto.
  Qed.

  Lemma M_pair x y z :
    x ∈' {y; z} <-> x ≡' y \/ x ≡' z.
  Proof.
    apply (@M_ZF (fun _ => ∅) ax_pair). cbn; tauto.
  Qed.

  Lemma M_union x y :
    x ∈' ⋃ y <-> exists z, z ∈' y /\ x ∈' z.
  Proof.
    apply (@M_ZF (fun _ => ∅) ax_union). cbn; tauto.
  Qed.

  (*
  Lemma M_power x y :
    x ∈ PP y <-> x ⊆ y.
  Proof.
    apply (@M_ZF (fun _ => ∅) ax_power). cbn; tauto.
  Qed.

  Definition M_inductive x :=
    ∅ ∈ x /\ forall y, y ∈ x -> σ y ∈ x.

  Lemma M_om1 :
    M_inductive ω.
  Proof.
    apply (@M_ZF (fun _ => ∅) ax_om1). cbn; tauto.
  Qed.

  Lemma M_om2 x :
    M_inductive x -> ω ⊆ x.
  Proof.
    apply (@M_ZF (fun _ => ∅) ax_om2). cbn; tauto.
  Qed.

  Definition agrees_fun phi (P : V -> Prop) :=
    forall x rho, P x <-> (x.:rho) ⊨ phi.

  Definition def_pred (P : V -> Prop) :=
    exists phi rho, forall d, P d <-> (d.:rho) ⊨ phi.

  Lemma M_sep P x :
    (forall phi rho, rho ⊨ ax_sep phi) -> def_pred P -> exists y, forall z, z ∈ y <-> z ∈ x /\ P z.
  Proof.
    cbn. intros H [phi [rho Hp]].
    destruct (H phi rho x) as [y H']; clear H.
    exists y. intros z. specialize (H' z). setoid_rewrite sat_comp in H'.
    rewrite (sat_ext _ _ (xi:=z.:rho)) in H'; try now intros [].
    firstorder.
  Qed.

  Definition M_is_rep R x y :=
    forall v, v ∈ y <-> exists u, u ∈ x /\ R u v.

  Lemma is_rep_unique R x y y' :
    M_is_rep R x y -> M_is_rep R x y' -> y = y'.
  Proof.
    intros H1 H2. apply M_ext; intros v.
    - intros H % H1. now apply H2.
    - intros H % H2. now apply H1.
  Qed.

  Definition functional (R : V -> V -> Prop) :=
    forall x y y', R x y -> R x y' -> y = y'.

  Definition def_rel (R : V -> V -> Prop) :=
    exists phi rho, forall x y, R x y <-> (x.:y.:rho) ⊨ phi.

  Lemma M_rep R x :
    (forall phi rho, rho ⊨ ax_rep phi) -> def_rel R -> functional R -> exists y, M_is_rep R x y.
  Proof.
    intros H1 [phi [rho Hp]]. intros H2.
    cbn in H1. specialize (H1 phi rho). destruct H1 with x as [y Hy].
    - intros a b b'. setoid_rewrite sat_comp.
      erewrite sat_ext. rewrite <- (Hp a b). 2: now intros [|[]].
      erewrite sat_ext. rewrite <- (Hp a b'). 2: now intros [|[]].
      rewrite VIEQ. apply H2.
    - exists y. intros v. split.
      + intros [u[U1 U2]] % Hy. exists u. split; trivial.
        setoid_rewrite sat_comp in U2. rewrite sat_ext in U2. rewrite (Hp u v). apply U2. now intros [|[]]; cbn.
      + intros [u[U1 U2]]. apply Hy. exists u. split; trivial.
        setoid_rewrite sat_comp. rewrite sat_ext. rewrite <- (Hp u v). apply U2. now intros [|[]]; cbn.
  Qed.



  (* ** Basic ZF *)

  Definition M_sing x :=
    {x; x}.

  Definition M_opair x y := ({{x; x}; {x; y}}).
  *)

  Definition M_binunion x y :=
    ⋃ {x; y}.

  Notation "x ∪' y" := (M_binunion x y) (at level 32).

  Lemma binunion_el x y z :
    x ∈' y ∪ z <-> x ∈' y \/ x ∈' z.
  Proof.
    split.
    - intros [u [H1 H2]] % M_union.
      apply M_pair in H1 as [<-| <-]; auto.
    - intros [H|H].
      + apply M_union. exists y. rewrite M_pair. auto.
      + apply M_union. exists z. rewrite M_pair. auto.
  Qed.

  Instance equiv_bunion :
    Proper (set_equiv ==> set_equiv ==> set_equiv) M_binunion.
  Proof.
  Admitted.

  Lemma sing_el x y :
    x ∈' M_sing y <-> x ≡' y.
  Proof.
    split.
    - now intros [H|H] % M_pair.
    - intros ->. apply M_pair. now left.
  Qed.

  Lemma M_pair1 x y :
    x ∈' {x; y}.
  Proof.
    apply M_pair. now left.
  Qed.

  Lemma M_pair2 x y :
    y ∈' {x; y}.
  Proof.
    apply M_pair. now right.
  Qed.

  Lemma sing_pair x y z :
    {x; x} ≡' {y; z} -> x ≡' y /\ x ≡' z.
  Proof.
    intros He. split.
    - assert (H : y ∈' {y; z}) by apply M_pair1.
      rewrite <- He in H. apply M_pair in H. intuition.
    - assert (H : z ∈' {y; z}) by apply M_pair2.
      rewrite <- He in H. apply M_pair in H. intuition.
  Qed.

  Lemma opair_inj1 x x' y y' :
    M_opair x y ≡' M_opair x' y' -> x ≡' x'.
  Proof.
    intros He. assert (H : {x; x} ∈' M_opair x y) by apply M_pair1.
    rewrite He in H. apply M_pair in H as [H|H]; apply (sing_pair H).
  Qed.

  Instance set_equiv_pair :
    Proper (set_equiv ==> set_equiv ==> set_equiv) M_opair.
  Proof.
  Admitted.

  Lemma opair_inj2 x x' y y' :
    M_opair x y ≡' M_opair x' y' -> y ≡' y'.
  Proof.
    intros He. assert (y ≡' x' \/ y ≡' y') as [Hy | Hy]; trivial.
    - assert (H : {x; y} ∈' M_opair x y) by apply M_pair2.
      rewrite He in H. apply M_pair in H as [H|H].
      + symmetry in H. apply sing_pair in H. intuition.
      + assert (H' : y ∈' {x; y}) by apply M_pair2.
        rewrite H in H'. now apply M_pair in H'.
    - assert (Hx : x ≡' x') by now apply opair_inj1 in He.
      rewrite Hx, Hy in He. rewrite Hy.
      assert (H : {x'; y'} ∈' M_opair x' y') by apply M_pair2.
      rewrite <- He in H. apply M_pair in H as [H|H]; symmetry in H; now apply sing_pair in H.
  Qed.

  Lemma opair_inj x x' y y' :
    M_opair x y ≡' M_opair x' y' -> x ≡' x' /\ y ≡' y'.
  Proof.
    intros H. split.
    - eapply opair_inj1; eassumption.
    - eapply opair_inj2; eassumption.
  Qed.

  Lemma sigma_el x y :
    x ∈' σ y <-> x ∈' y \/ x ≡' y.
  Proof.
    split.
    - intros [H|H] % binunion_el; auto.
      apply sing_el in H. now right.
    - intros [H| ->]; apply binunion_el; auto.
      right. now apply sing_el.
  Qed.

  (*Lemma sigma_eq x :
    x ∈ σ x.
  Proof.
    apply sigma_el. now right.
  Qed.

  Lemma sigma_sub x :
    x ⊆ σ x.
  Proof.
    intros y H. apply sigma_el. now left.
  Qed.*)

  Lemma binunion_eset x :
    x ≡' ∅ ∪ x.
  Proof.
    apply M_ext.
    - intros y H. apply binunion_el. now right.
    - intros y [H|H] % binunion_el.
      + now apply M_eset in H.
      + assumption.
  Qed.

  Lemma pair_com x y :
    {x; y} ≡' {y; x}.
  Proof.
    apply M_ext; intros z; rewrite !M_pair; tauto.
  Qed.

  Definition union x :=
    ⋃ x.

  Instance equiv_union :
    Proper (set_equiv ==> set_equiv) union.
  Proof.
  Admitted.

  Lemma binunion_com x y :
    x ∪' y ≡' y ∪' x.
  Proof.
    apply equiv_union, pair_com.
  Qed.

  Lemma binunionl a x y :
    a ∈' x -> a ∈' x ∪' y.
  Proof.
    intros H. apply binunion_el. now left.
  Qed.

  Lemma binunionr a x y :
    a ∈' y -> a ∈' x ∪' y.
  Proof.
    intros H. apply binunion_el. now right.
  Qed.

  Hint Resolve binunionl binunionr : core.

  Lemma binunion_assoc x y z :
    (x ∪' y) ∪' z ≡' x ∪' (y ∪' z).
  Proof.
    apply M_ext; intros a [H|H] % binunion_el; eauto.
    - apply binunion_el in H as [H|H]; eauto.
    - apply binunion_el in H as [H|H]; eauto.
  Qed.

  
  
  (* ** Numerals *)

  (*Fixpoint numeral n :=
    match n with 
    | O => ∅
    | S n => σ (numeral n)
    end.

  Lemma numeral_omega n :
    numeral n ∈ ω.
  Proof.
    induction n; cbn; now apply M_om1.
  Qed.

  Definition trans x :=
    forall y, y ∈ x -> y ⊆ x.

  Lemma numeral_trans n :
    trans (numeral n).
  Proof.
    induction n; cbn.
    - intros x H. now apply M_eset in H.
    - intros x [H| ->] % sigma_el; try apply sigma_sub.
      apply IHn in H. intuition eauto using sigma_sub.
  Qed.

  Lemma numeral_wf n :
    ~ numeral n ∈ numeral n.
  Proof.
    induction n.
    - apply M_eset.
    - intros [H|H] % sigma_el; fold numeral in *.
      + apply IHn. eapply numeral_trans; eauto. apply sigma_eq.
      + assert (numeral n ∈ numeral (S n)) by apply sigma_eq.
        now rewrite H in H0.
  Qed.*)

  Lemma numeral_lt k l :
    k < l -> numeral k ∈ numeral l.
  Proof.
    induction 1; cbn; apply sigma_el; auto.
  Qed.

  (*Lemma numeral_inj k l :
    numeral k = numeral l -> k = l.
  Proof.
    intros Hk. assert (k = l \/ k < l \/ l < k) as [H|[H|H]] by lia; trivial.
    all: apply numeral_lt in H; rewrite Hk in H; now apply numeral_wf in H.
  Qed.



  (* ** Encodings *)

  (* Encodings of booleans, strings, cards, and stacks *)

  Definition M_enc_bool (x : bool) :=
    if x then {∅; ∅} else ∅.

  Fixpoint M_prep_string (s : string bool) x :=
    match s with
    | nil => x
    | b::s => M_opair (M_enc_bool b) (M_prep_string s x)
    end.

  Definition M_enc_string (s : string bool) :=
    M_prep_string s ∅.

  Definition M_enc_card s t :=
    M_opair (M_enc_string s) (M_enc_string t).

  Fixpoint M_enc_stack (B : BSRS) :=
    match B with
    | nil => ∅
    | (s,t)::B => M_enc_stack B ∪ M_sing (M_enc_card s t)
    end.*)

  (* Injectivity of encodings *)

  Lemma enc_bool_inj b c :
    M_enc_bool b ≡' M_enc_bool c -> b = c.
  Proof.
    destruct b, c; trivial; cbn.
    - intros H. contradiction (@M_eset ∅).
      rewrite <- H at 2. apply M_pair; auto.
    - intros H. contradiction (@M_eset ∅).
      rewrite H at 2. apply M_pair; auto.
  Qed.

  Lemma enc_string_inj s t :
    M_enc_string s ≡' M_enc_string t -> s = t.
  Proof.
    induction s in t|-*; destruct t as [|b t]; cbn; trivial.
    - intros H. contradiction (M_eset (x:=M_sing (M_enc_bool b))).
      rewrite H. apply M_pair. now left.
    - intros H. contradiction (M_eset (x:=M_sing (M_enc_bool a))).
      rewrite <- H. apply M_pair. now left.
    - intros [H1 H2] % opair_inj. apply IHs in H2 as ->.
      apply enc_bool_inj in H1 as ->. reflexivity.
  Qed.

  (*
  (* Agreement to syntactical encodings under evaluation *)

  Lemma eval_opair rho x y :
    eval rho (opair x y) = M_opair (eval rho x) (eval rho y).
  Proof.
    reflexivity.
  Qed.

  Lemma eval_enc_bool rho b :
    eval rho (enc_bool b) = M_enc_bool b.
  Proof.
    destruct b; reflexivity.
  Qed.

  Lemma eval_prep_string rho s x :
    eval rho (prep_string s x) = M_prep_string s (eval rho x).
  Proof.
    induction s; trivial. cbn [prep_string].
    now rewrite eval_opair, IHs, eval_enc_bool.
  Qed.

  Lemma eval_enc_string rho s :
    eval rho (enc_string s) = M_enc_string s.
  Proof.
    unfold enc_string. now rewrite eval_prep_string.
  Qed.
  
  Lemma eval_enc_stack rho B :
    eval rho (enc_stack B) = M_enc_stack B.
  Proof.
    induction B; cbn; trivial. destruct a. unfold M_enc_card.
    now rewrite <- IHB, <- !eval_enc_string with (rho:=rho), <- eval_opair.
  Qed. *)

  (* Auxiliary lemmas for stack encodings *)

  Lemma M_enc_stack_app A B :
    M_enc_stack (A ++ B) ≡' M_enc_stack A ∪' M_enc_stack B.
  Proof.
    induction A as [|[s t] A IH]; cbn.
    - apply binunion_eset.
    - change (M_enc_stack (A ++ B) ∪' M_sing (M_enc_card s t)
                          ≡' (M_enc_stack A ∪' M_sing (M_enc_card s t)) ∪' M_enc_stack B).
      rewrite IH. rewrite !binunion_assoc.
      now rewrite (binunion_com (M_enc_stack B) (M_sing (M_enc_card s t))).
  Qed.

  Lemma enc_stack_el' x A :
    x ∈ M_enc_stack A -> exists s t, (s, t) el A /\ x ≡' M_enc_card s t.
  Proof.
    induction A as [|[s t] A IH]; cbn.
    - now intros H % M_eset.
    - intros [H|H] % binunion_el.
      + destruct (IH H) as (u&v&H1&H2). exists u, v. intuition.
      + apply sing_el in H. exists s, t. intuition.
  Qed.

  Lemma enc_stack_el B s t :
    (s, t) el B -> M_enc_card s t ∈ M_enc_stack B.
  Proof.
    induction B as [|[u b] B IH]; cbn; auto.
    intros [H|H]; apply binunion_el.
    - right. apply sing_el. injection H. now intros -> ->.
    - left. apply IH, H.
  Qed.

  (*
  Lemma M_prep_enc s s' :
    M_prep_string s (M_enc_string s') = M_enc_string (s ++ s').
  Proof.
    induction s; cbn; trivial.
    now rewrite IHs.
  Qed.



  (* ** Preservation direction *)

  (*
     We encode the k-step solutions of a PCP instance B as a set-theoretic function M_enc_derivations.
     This function satisfies the conditions expressed in the reduction formula and
     contains a solution whenever B is solvable.
   *)
     
  Definition append_all A (c : card bool) :=
    map (fun p => (fst c ++ fst p, snd c ++ snd p)) A.

  Definition derivation_step B C :=
    flat_map (append_all C) B.

  Fixpoint derivations B n :=
    match n with
    | O => B
    | S n => derivation_step B (derivations B n)
    end.

  Lemma derivable_derivations B s t :
    derivable B s t -> exists n, s/t el derivations B n.
  Proof.
    induction 1.
    - exists 0. apply H.
    - destruct IHderivable as [n Hn]. exists (S n).
      apply in_flat_map. exists (x, y). split; trivial.
      apply in_map_iff. exists (u,v). cbn. split; trivial.
  Qed.

  Fixpoint M_enc_derivations B n :=
    match n with 
    | O => M_sing (M_opair ∅ (M_enc_stack B))
    | S n => M_enc_derivations B n ∪
            M_sing (M_opair (numeral (S n)) (M_enc_stack (derivations B (S n))))
    end.

  Lemma enc_derivations_base B n :
    M_opair ∅ (M_enc_stack B) ∈ M_enc_derivations B n.
  Proof.
    induction n; cbn.
    - now apply sing_el.
    - apply binunion_el. now left.
  Qed.

  Lemma enc_derivations_bound B n k x :
    M_opair k x ∈ M_enc_derivations B n -> k ∈ σ (numeral n).
  Proof.
    induction n; cbn.
    - intros H % sing_el. apply opair_inj in H as [-> _].
      apply sigma_el. now right.
    - intros [H|H] % binunion_el.
      + apply sigma_el. left. apply IHn, H.
      + apply sing_el in H. apply opair_inj in H as [-> _]. apply sigma_eq.
  Qed. 

  Lemma enc_derivations_fun B n :
    forall k x y, M_opair k x ∈ M_enc_derivations B n -> M_opair k y ∈ M_enc_derivations B n -> x = y.
  Proof.
    induction n; cbn -[derivations]; intros k x y.
    - intros H1 % sing_el H2 % sing_el.
      rewrite <- H2 in H1. now apply opair_inj in H1.
    - intros [H1|H1 % sing_el] % binunion_el [H2|H2 % sing_el] % binunion_el.
      + now apply (IHn k x y).
      + exfalso. apply enc_derivations_bound in H1.
        destruct (opair_inj H2) as [-> _]. now apply (@numeral_wf (S n)).
      + exfalso. apply enc_derivations_bound in H2.
        destruct (opair_inj H1) as [-> _]. now apply (@numeral_wf (S n)).
      + rewrite <- H2 in H1. now apply opair_inj in H1.
  Qed.

  Lemma enc_derivations_el B n k x :
    M_opair k x ∈ M_enc_derivations B n -> exists l, k = numeral l /\ x = M_enc_stack (derivations B l).
  Proof.
    induction n; cbn.
    - intros H % sing_el. exists 0. apply (opair_inj H).
    - intros [H|H] % binunion_el.
      + apply IHn, H.
      + apply sing_el in H. exists (S n). apply (opair_inj H).
  Qed. 

  Lemma enc_derivations_step B n l :
    numeral l ∈ numeral n
    -> M_opair (σ (numeral l)) (M_enc_stack (derivations B (S l))) ∈ M_enc_derivations B n.
  Proof.
    induction n; cbn -[derivations].
    - now intros H % M_eset.
    - intros [H|H % sing_el] % binunion_el; apply binunion_el.
      + left. apply IHn, H.
      + right. apply numeral_inj in H as ->. now apply sing_el.
  Qed.

  Lemma enc_stack_combinations B rho C x X Y :
    rho ⊨ combinations B X Y -> eval rho X = M_enc_stack C -> eval rho Y = x -> x = M_enc_stack (derivation_step B C).
  Proof.
    induction B as [|[s t] B IH] in rho,C,x,X,Y |-*.
    - cbn. rewrite VIEQ. now intros -> _ <-.
    - intros [x1[x2[[H1 H2]H3]]] R1 R2; fold sat in *.
      assert (x = x2 ∪ x1) as ->. { rewrite <- R2. cbn in H1. rewrite !eval_comp in H1. apply VIEQ, H1. } clear H1.
      cbn. fold (derivation_step B C). rewrite M_enc_stack_app.
      enough (x1 = M_enc_stack (derivation_step B C)) as E1.
      + enough (x2 = M_enc_stack (append_all C (s / t))) as E2 by now rewrite E1, E2.
        apply M_ext; intros u Hu.
        * apply H3 in Hu as [v [Hv[a [b Ha]]]].
          cbn in Hv. erewrite !eval_comp, eval_ext, R1 in Hv; trivial.
          apply enc_stack_el' in Hv as (s'&t'&H&H').
          enough (u = M_enc_card (s++s') (t++t')) as ->.
          { apply enc_stack_el. apply in_map_iff. now exists (s'/t'). }
          cbn in Ha. rewrite !VIEQ in Ha. destruct Ha as [D1 D2].
          rewrite D1 in H'. unfold M_enc_card in H'. apply opair_inj in H' as [-> ->].
          rewrite D2; unfold M_enc_card, M_opair; repeat f_equal.
          all: rewrite eval_prep_string; cbn. all: apply M_prep_enc.
        * apply enc_stack_el' in Hu as (s'&t'&H&->).
          unfold append_all in H. eapply in_map_iff in H as [[a b][H H']].
          cbn in H. apply H3. exists (M_enc_card a b). split.
          { cbn. erewrite !eval_comp, eval_ext, R1; trivial. now apply enc_stack_el. }
          exists (M_enc_string b), (M_enc_string a). split.
          -- cbn. apply VIEQ. reflexivity.
          -- cbn. apply VIEQ. rewrite !eval_prep_string. cbn.
             rewrite !M_prep_enc. injection H. intros -> ->. reflexivity.
      + eapply IH; eauto. unfold shift. now erewrite !eval_comp, eval_ext, R1.
  Qed.

  Lemma enc_derivations_solutions B n rho a b :
    (a .: b .: M_enc_derivations B n .: numeral n .: rho) ⊨ solutions B $2 $3.
  Proof.
    cbn. split.
    - rewrite eval_enc_stack. apply enc_derivations_base.
    - intros k x x' H1 H2 H3.
      destruct (enc_derivations_el H2) as [l[-> ->]].
      specialize (enc_derivations_step B H1).
      replace (M_enc_stack (derivations B (S l))) with x'; trivial.
      apply (enc_stack_combinations H3); trivial.
  Qed.

  Lemma derivations_enc_derivations B n :
    M_opair (numeral n) (M_enc_stack (derivations B n)) ∈ M_enc_derivations B n.
  Proof.
    induction n; cbn -[derivations].
    - now apply sing_el.
    - apply binunion_el. right.
      now apply sing_el.
  Qed.

  Lemma derivations_el B n s t :
     s / t el derivations B n -> M_enc_card s t ∈ M_enc_stack (derivations B n).
  Proof.
    apply enc_stack_el.
  Qed.

  Theorem PCP_ZF1 B s :
    derivable B s s -> forall rho, rho ⊨ solvable B.
  Proof.
    intros H rho. destruct (derivable_derivations H) as [n Hn]. unfold solvable.
    exists (numeral n), (M_enc_derivations B n), (M_enc_string s), (M_enc_stack (derivations B n)).
    split; [split; [split; [split |] |] |].
    - apply numeral_omega.
    - unfold function'. intros k x y H1 H2. apply VIEQ. apply (enc_derivations_fun H1 H2).
    - apply enc_derivations_solutions.
    - cbn. apply derivations_enc_derivations.
    - now apply enc_stack_el.
  Qed.
  *)


  (* ** Reflection direction *)

  (*
    Conversely, we show how to reconstruct a solution of a PCP instance B from a model
    (1) satisfying the reduction formula defined above and
    (2) containing only the standard natural numers.
    The latter seems necessary to exclude non-standard solutions the model might contain.
   *)
  
  Definition M_comb_rel s t :=
    fun u v => exists u1 u2, u ≡' M_opair u1 u2 /\ v ≡' M_opair (M_prep_string s u1) (M_prep_string t u2).

  Fixpoint M_combinations B x y :=
    match B with
    | nil => y = ∅
    | (s,t)::B => exists y1 y2, y ≡' y2 ∪ y1 /\ M_combinations B x y1 /\ M_is_rep (M_comb_rel s t) x y2
    end.

  Lemma M_combinations_spec B rho x y a b :
    M_combinations B x y -> eval rho a = x -> eval rho b = y -> rho ⊨ combinations B a b.
  Proof.
    induction B in y,a,b,rho|-*; cbn.
    - now intros -> _ ->.
    - destruct a0 as [s t]. intros (y1&y2&H1&H2&H3) Ha Hb. exists y1, y2. repeat split.
      + cbn. erewrite !eval_comp. unfold funcomp. cbn.
        change (eval rho b ≡' y2 ∪ y1). now rewrite Hb, H1.
      + eapply (IHB _ y1); trivial. erewrite !eval_comp. unfold funcomp. cbn.
        change (eval (fun x => rho x) a) with (eval rho a). now rewrite Ha.
      + intros (u & Hu & c & d' & H) % H3. exists u. split.
        * cbn. erewrite !eval_comp. erewrite eval_ext, Ha; trivial.
        * exists d', c. cbn. rewrite !eval_prep_string. apply H.
      + intros (u & Hu & c & d' & H). apply H3. exists u. split.
        * cbn in Hu. erewrite !eval_comp in Hu. rewrite <- Ha. apply Hu.
        * exists d', c. cbn in H. rewrite !eval_prep_string in H. apply H.
  Qed.

  Definition M_solutions B f n :=
    M_opair ∅ (M_enc_stack B) ∈ f /\ forall k x y, k ∈ n -> M_opair k x ∈ f -> M_combinations B x y -> M_opair (σ k) y ∈' f.

  Instance equiv_prep :
    Proper (eq ==> set_equiv ==> set_equiv) M_prep_string.
  Proof.
  Admitted.

  Lemma comb_rel_rep C s t :
    M_is_rep (M_comb_rel s t) (M_enc_stack C) (M_enc_stack (append_all C (s, t))).
  Proof.
    intros y. split.
    - intros (u&v&H&H') % enc_stack_el'.
      unfold append_all in H. apply in_map_iff in H as [[a b][H1 H2]]. cbn in H1.
      exists (M_enc_card a b). split; try now apply enc_stack_el.
      exists (M_enc_string a), (M_enc_string b). split; trivial.
      assert (u = s++a) as -> by congruence. assert (v = t++b) as -> by congruence.
      now rewrite !M_prep_enc.
    - intros (u&H&a&b&H3&H4). apply enc_stack_el' in H as [u'[v[H1 H2]]]. rewrite H3 in H2.
      apply opair_inj in H2 as [H2 H2']. change (y ∈' M_enc_stack (append_all C (s, t))).
      rewrite H4, H2, H2', !M_prep_enc. apply enc_stack_el.
      apply in_map_iff. now exists (u', v).
  Qed.

  Lemma M_combinations_step B C :
    M_combinations B (M_enc_stack C) (M_enc_stack (derivation_step B C)).
  Proof.
    induction B as [|[s t] B IH]; cbn; trivial.
    exists (M_enc_stack (derivation_step B C)), (M_enc_stack (append_all C (s, t))).
    rewrite M_enc_stack_app. split; trivial. split; trivial.
    apply comb_rel_rep.
  Qed.

  Lemma solutions_derivations B f n k :
    M_solutions B f (numeral n) -> k <= n -> M_opair (numeral k) (M_enc_stack (derivations B k)) ∈ f.
  Proof.
    intros H Hk; induction k; cbn.
    - apply H.
    - assert (Hk' : k <= n) by lia. specialize (IHk Hk').
      destruct H as [_ H]. eapply H in IHk; eauto.
      + now apply numeral_lt.
      + apply M_combinations_step.
  Qed.

  Definition M_function f :=
    forall x y y', M_opair x y ∈ f -> M_opair x y' ∈ f -> y ≡' y'.

  Instance equiv_solutions :
    Proper (eq ==> eq ==> set_equiv ==> iff) M_solutions.
  Proof.
  Admitted.

  Lemma M_solutions_el B f k X p :
    standard M -> k ∈ ω -> M_function f -> M_solutions B f k -> M_opair k X ∈' f
    -> p ∈' X -> exists u v, p ≡' M_enc_card u v /\ derivable B u v.
  Proof.
    intros HS HO Hf Hk HX Hp. destruct (HS k HO) as [n Hn].
    change (k ≡' numeral n) in Hn. rewrite Hn in Hk. rewrite Hn in HX.
    pose proof (H := solutions_derivations Hk (le_n n)).
    rewrite (Hf _ _ _ HX H) in Hp. apply enc_stack_el' in Hp as (s&t&H'&Hp).
    exists s, t. split; trivial. eapply derivations_derivable; eauto.
  Qed.

  Theorem PCP_ZF2 B rho :
    standard M -> rho ⊨ solvable B -> exists s, derivable B s s.
  Proof.
    intros VIN (n & f & s & X & [[[[H1 H2] H3] H4] H5]).
    assert (H1' : n ∈ ω) by apply H1. clear H1.
    assert (H4' : M_opair n X ∈ f) by apply H4. clear H4.
    assert (H5' : M_opair s s ∈ X) by apply H5. clear H5.
    assert (H2' : M_function f).
    { intros x y y' H H'. eapply H2. apply H. apply H'. } clear H2.
    assert (H3' : M_opair ∅ (M_enc_stack B) ∈ f).
    { erewrite <- eval_enc_stack. apply H3. } destruct H3 as [_ H3].
    assert (H3'' : forall k x y, k ∈ n -> M_opair k x ∈ f -> M_combinations B x y -> M_opair (σ k) y ∈ f).
    { intros k x y Hn Hk Hy. apply (H3 k x y); auto. fold sat. eapply M_combinations_spec; eauto. } clear H3.
    destruct (@M_solutions_el B f n X (M_opair s s)) as (u&v&H1&H2); trivial.
    now split. exists u. apply opair_inj in H1 as [H H1]. rewrite H1 in H.
    apply enc_string_inj in H as ->. apply H2.
  Qed.
  
End ZF.



(* ** Reduction Theorem *)

Theorem PCP_ZFeq' B :
  (exists V (M : interp V), standard M /\ forall rho, rho ⊫ ZFeq')
  -> entailment_ZFeq' (solvable B) -> PCPb B.
Proof.
  intros (M & H1 & H2 & H3) H. rewrite PCPb_iff_dPCPb.
  specialize (H M H1 (fun _ => @i_func _ _ _ _ eset Vector.nil) H3).
  apply PCP_ZF2 in H as [s Hs]; trivial. now exists s.
Qed.