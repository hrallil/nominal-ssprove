Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude Group Misc.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.


Module PKScheme.

Record pk_scheme :=
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip : code fset0 [interface] Cip

  ; keygen :
      code fset0 [interface] (Sec × Pub)

  ; enc : ∀ (pk : Pub) (m : Mes),
      code fset0 [interface] Cip

  ; dec : ∀ (sk : Sec) (c : Cip),
      code fset0 [interface] Mes
  }.

Notation " 'sec p " := (Sec p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'sec p " := (Sec p)
  (at level 3) : package_scope.

Notation " 'pub p " := (Pub p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'pub p " := (Pub p)
  (at level 3) : package_scope.

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Notation " 'cip p " := (Cip p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'cip p " := (Cip p)
  (at level 3) : package_scope.


Definition ENCDEC := 0%N.

Definition I_CORR (P : pk_scheme) :=
  [interface #val #[ ENCDEC ] : 'mes P → 'mes P ].

Definition CORR0 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    #def #[ ENCDEC ] (m : 'mes P) : ('mes P) {
      '(sk, pk) ← P.(keygen) ;;
      c ← P.(enc) pk m ;;
      m' ← P.(dec) sk c ;;
      ret m'
    }
  ].

Definition CORR1 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    #def #[ ENCDEC ] (m : 'mes P) : ('mes P) {
      ret m
    }
  ].

Definition CORR P b := if b then CORR0 P else CORR1 P.

Definition flag_loc : Location := ('option 'unit; 0%N).
Definition mpk_loc (P : pk_scheme) : Location := ('option ('pub P); 1%N).
Definition GET := 0%N.
Definition QUERY := 1%N.

Lemma r_refl {A : choiceType} : ∀ c : raw_code A,
  ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c ≈ c ⦃ λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ ∧ s₀ = s₁ ⦄.
Proof.
  intros c.
  eapply rpost_weaken_rule.
  1: apply rreflexivity_rule.
  intros [? ?] [? ?] ?.
  injection H => ? ?. 
  by subst.
Qed.


Definition init_loc (P : pk_scheme) : Location := ('option ('pub P); 1%N).

Definition init P : raw_code ('pub P) :=
  locked (mpk ← get init_loc P ;;
  match mpk with
  | None => 
    '(_, pk) ← P.(keygen) ;;
    #put init_loc P := Some pk ;;
    ret pk
  | Some pk =>
    ret pk
  end).

#[export] Instance init_valid {P} {L : {fset Location}} {I : Interface}
  : init_loc P \in L → ValidCode L I (init P).
Proof.
  intros H.
  rewrite /init -lock.
  ssprove_valid.
Qed.

Notation rem_init P (* {P} : 'pub P → precond *)
  := (λ pk, rem_rhs (init_loc P) (Some pk)).

Lemma r_init {B : choiceType} {P} {f0 f1}
  : ∀ (pre : precond) (post : postcond B B),
  (∀ pk : 'pub P, put_pre_cond (init_loc P) (Some pk) pre) →
  Syncs (init_loc P) pre →
  (∀ pk : 'pub P,
    ⊢ ⦃ λ '(h₀, h₁), (pre ⋊ rem_init P pk) (h₀, h₁) ⦄ f0 pk ≈ f1 pk ⦃ post ⦄
  ) → ⊢ ⦃ λ '(h₀, h₁), pre (h₀, h₁) ⦄
    x ← init P ;; f0 x ≈ x ← init P ;; f1 x
    ⦃ post ⦄.
Proof.
  intros pre post E H H'.
  rewrite /init -lock.
  simpl.
  apply r_get_vs_get_remember_rhs => pk.
  1: apply H.
  destruct pk.
  1: apply H'.
  ssprove_code_simpl.
  apply r_forget_rhs.
  eapply rsame_head_alt.
  1: apply prog_valid.
  1,2: intros l ? => //.
  intros [_ pk].
  eapply r_put_vs_put.
  eapply rpre_weaken_rule.
  1: apply H'.
  intros s0 s1 [s1' [[s0' [H1 H2]] H3]].
  subst.
  split.
  1: apply E, H1.
  1: unfold put_pre_cond in E.
  rewrite //=.
  by get_heap_simpl.
Qed.

Lemma r_init_remember_rhs {B : choiceType} {P} {c f1}
  : ∀ (pre : precond) (post : postcond B B) pk,
  Remembers_rhs (init_loc P) (Some pk) pre →
    ⊢ ⦃ λ '(h₀, h₁), pre (h₀, h₁) ⦄ c ≈ f1 pk ⦃ post ⦄
  → ⊢ ⦃ λ '(h₀, h₁), pre (h₀, h₁) ⦄ c ≈ x ← init P ;; f1 x ⦃ post ⦄.
Proof.
  intros pre post pk H H'.
  rewrite /init -lock //=.
  eapply rpre_weaken_rule.
  1: apply (r_get_remind_rhs (init_loc P) (Some pk)).
  3: intros s0 s1 H''; exact H''.
  1: exact H.

  eapply rpre_weaken_rule.
  1: apply H'.
  intros s0 s1 H''; exact H''.
Qed.

Lemma r_init_remember_lhs {B : choiceType} {P} {c f1}
  : ∀ (pre : precond) (post : postcond B B) pk,
  Remembers_lhs (init_loc P) (Some pk) pre →
    ⊢ ⦃ λ '(h₀, h₁), pre (h₀, h₁) ⦄ f1 pk ≈ c ⦃ post ⦄
  → ⊢ ⦃ λ '(h₀, h₁), pre (h₀, h₁) ⦄ x ← init P ;; f1 x ≈ c ⦃ post ⦄.
Proof.
  intros pre post pk H H'.
  rewrite /init -lock //=.
  eapply rpre_weaken_rule.
  1: apply (r_get_remind_lhs (init_loc P) (Some pk)).
  3: intros s0 s1 H''; exact H''.
  1: exact H.

  eapply rpre_weaken_rule.
  1: apply H'.
  intros s0 s1 H''; exact H''.
Qed.

Lemma r_put_init_swap {P} : ∀ (l : Location)
  (v : l), init_loc P != l →
  ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
    x ← init P ;;
    a ← cmd cmd_put l v ;;
    ret (x, a)
  ≈
    a ← cmd cmd_put l v ;;
    x ← init P ;;
    ret (x, a)
 ⦃ eq ⦄.
Proof.
  intros l v H.
  rewrite /init -lock.
  ssprove_code_simpl; simpl.
  ssprove_swap_rhs 0%N.
  1: move: H => /negP H; by apply H.
  ssprove_sync_eq => pk.
  destruct pk.
  1: {
    simpl.
    eapply rpost_weaken_rule.
    1: apply r_refl.
    by intros [a0 h0] [a1 h1] [-> ->].
  }
  ssprove_swap_rhs 0%N.
  1: apply r_swap_scheme_cmd, prog_valid.
  ssprove_code_simpl; simpl.
  apply rsame_head => skpk.
  destruct skpk as [_ pk].
  ssprove_swap_rhs 0%N.
  1: move: H => /negP H; by apply H.
  eapply rpost_weaken_rule.
  1: apply r_refl.
  by intros [a0 h0] [a1 h1] [-> ->].
Qed.


Definition I_PK_OTSR (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P → 'cip P
  ].

Definition PK_OTSR (P : pk_scheme) b :
  game (I_PK_OTSR P) :=
  [module fset [:: mpk_loc P ; flag_loc ] ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      pk ← init P ;;
      ret pk
    } ;
    #def #[ QUERY ] (m : 'mes P) : ('cip P) {
      pk ← init P ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      if b then
        P.(enc) pk m
      else
        P.(sample_Cip)
    }
  ].

(*
Definition PK_OTSR1 (P : pk_scheme) :
  game (I_PK_OTSR P) :=
  [module PK_OTSR_loc P ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      getNone (mpk_loc P) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] (m : 'mes P) : ('cip P) {
      pk ← getSome (mpk_loc P) ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      P.(sample_Cip)
    }
  ].
  
Definition PK_OTSR P b := if b then PK_OTSR0 P else PK_OTSR1 P.
 *)


Definition I_PK_OTS (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P × 'mes P → 'cip P
  ].

Definition PK_OTS (P : pk_scheme) b :
  game (I_PK_OTS P) :=
  [module fset [:: mpk_loc P ; flag_loc ] ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      pk ← init P ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, m') : 'mes P × 'mes P) : ('cip P) {
      pk ← init P ;; 
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      P.(enc) pk (if b then m else m')
    }
  ].

(*
Definition PK_OTS1 (P : pk_scheme) :
  game (I_PK_OTS P) :=
  [module PK_OTS_loc P ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      getNone (mpk_loc P) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(_, m) : 'mes P × 'mes P) : ('cip P) {
      pk ← getSome (mpk_loc P) ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      P.(enc) pk m
    }
  ].
  
Definition PK_OTS P b := if b then PK_OTS0 P else PK_OTS1 P.

 *)

Definition CHOOSE (P : pk_scheme) b :
  module (I_PK_OTSR P) (I_PK_OTS P) :=
  [module no_locs ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      #import {sig #[ GET ] : 'unit → 'pub P } as GET ;;
      pk ← GET tt ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, m') : 'mes P × 'mes P) : ('cip P) {
      #import {sig #[ QUERY ] : 'mes P → 'cip P } as QUERY ;;
      c ← QUERY (if b then m else m') ;;
      ret c
    }
  ].

Lemma pk_ots_choose {P} {b} : PK_OTS P b ≈₀ (CHOOSE P b ∘ PK_OTSR P true)%share.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel mm'.
  1,2: simplify_linking.
  1,2: ssprove_code_simpl; simpl.
  1,2: rewrite cast_fun_K.
  + rewrite bind_assoc.
    apply rsame_head => pk.
    by apply r_ret.
  + move: mm' => //= [m m'].
    ssprove_code_simpl; simpl.
    apply rsame_head => pk.
    ssprove_code_simpl_more.
    ssprove_sync_eq => flag.
    ssprove_sync_eq => H'.
    ssprove_sync_eq.
    rewrite bind_ret.
    apply r_refl.
Qed.

Lemma choose_perf {P} : (CHOOSE P true ∘ PK_OTSR P false)%share ≈₀ (CHOOSE P false ∘ PK_OTSR P false)%share.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel mm'.
  + apply r_refl.
  + ssprove_code_simpl; simpl.
    apply r_refl.
Qed.

Lemma Adv_PK_OTS {P} (A : adversary (I_PK_OTS P)) :
  AdvFor (PK_OTS P) A
  <= AdvFor (PK_OTSR P) (A ∘ CHOOSE P true)
  +  AdvFor (PK_OTSR P) (A ∘ CHOOSE P false).
Proof.
  rewrite /AdvFor //=.
  rewrite (Adv_perf_l pk_ots_choose).
  rewrite (Adv_perf_r pk_ots_choose).
  nssprove_adv_trans (CHOOSE P true ∘ PK_OTSR P false)%share.
  rewrite (Adv_perf_l choose_perf).
  nssprove_separate.
  apply Num.Theory.lerD.
  2: rewrite Adv_sym.
  1,2: rewrite Adv_sep_link Order.le_refl //.
Qed.



Definition I_PK_CPA (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P × 'mes P → 'cip P
  ].

Definition count_loc : Location := ('nat; 20%N).

Definition PK_CPA (P : pk_scheme) (n : nat) b :
  game (I_PK_CPA P) :=
  [module fset [:: mpk_loc P ; count_loc ] ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      pk ← init P ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, m') : 'mes P × 'mes P) : ('cip P) {
      pk ← init P ;;
      count ← get count_loc ;; 
      #assert (count < n)%N ;;
      #put count_loc := count.+1 ;;
      P.(enc) pk (if b then m else m')
    }
  ].

Definition SLIDE (P : pk_scheme) (i n : nat) :
  module (I_PK_OTS P) (I_PK_CPA P) :=
  [module fset [:: count_loc ] ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      #import {sig #[ GET ] : 'unit → 'pub P } as GET ;;
      pk ← GET tt ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, m') : 'mes P × 'mes P) : ('cip P) {
      #import {sig #[ GET ] : 'unit → 'pub P } as GET ;;
      #import {sig #[ QUERY ] : 'mes P × 'mes P → 'cip P } as QUERY ;;
      pk ← GET tt ;;
      count ← get count_loc ;;
      #assert (count < n)%N ;;
      #put count_loc := count.+1 ;;
      if (count < i)%N then
        c ← P.(enc) pk m' ;;
        ret c
      else if (i < count)%N then
        c ← P.(enc) pk m ;;
        ret c
      else 
        c ← QUERY (m, m') ;;
        ret c
    }
  ].

Definition R (i : 'nat) (c : 'nat) (f : 'option 'unit)
  := ((c > i)%N = isSome f).

Notation inv i := (
  heap_ignore (fset [:: flag_loc ])
  ⋊ couple_rhs count_loc flag_loc (R i)
).

Lemma put_pre_cond_inv {P n} : ∀ pk : 'pub P,
  put_pre_cond (init_loc P) (Some pk) (λ '(s₀, s₁), inv n (s₀, s₁)).
Proof.
  intros pk h0 h1 [H0 H1].
  repeat split.
  1: apply put_pre_cond_heap_ignore, H0.
  1: apply put_pre_cond_couple_rhs; [ fset_solve | fset_solve | done ].
Qed.

Lemma pk_cpa_slide {P n b} :
  PK_CPA P n b ≈₀ (SLIDE P (if b then 0 else n) n ∘ PK_OTS P true)%share.
Proof.
  apply (eq_rel_perf_ind _ _ (inv (if b then 0 else n))).
  1: simpl; ssprove_invariant.
  1: fset_solve.
  1: rewrite /R ltn0 //.
  simplify_eq_rel mm'.
  - simplify_linking.
    rewrite cast_fun_K bind_assoc.
    apply r_init.
    2: apply Syncs_conj, Syncs_heap_ignore; fset_solve.
    1: apply put_pre_cond_inv.
    move=> pk //=.
    apply r_ret => s0 s1 [[H0 H1] H2].
    by repeat split.
  - ssprove_code_simpl; simpl.
    rewrite 2!cast_fun_K bind_ret.
    move: mm' => //= [m m']. 

    apply r_init.
    2: apply Syncs_conj, Syncs_heap_ignore; fset_solve.
    1: apply put_pre_cond_inv.
    intros pk.
    apply r_get_vs_get_remember_rhs.
    1: intros ? ? ? => //; apply H; fset_solve.
    intros i.
    ssprove_sync => H.
    (* eapply r_put_vs_put. *)

    destruct b.
    + destruct i eqn:E.
      2: {
        rewrite //= bind_ret.
        eapply r_put_vs_put.
        ssprove_restore_mem.
        2: eapply r_reflexivity_alt; [ apply prog_valid  | | ]; done.
        ssprove_invariant.

        move=> h0 h1 //= [[H0 H1] H2].
        rewrite /R /couple_rhs in H0 |- *.
        get_heap_simpl.
        rewrite -H0 H2 //.
      }

      ssprove_code_simpl; simpl.
      ssprove_swap_rhs 0%N.
      1: apply r_put_init_swap; fset_solve.
      apply (r_init_remember_rhs _ _ pk).
      1: exact _.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => f.
      eapply (r_rem_couple_rhs count_loc flag_loc).
      1,2,3: exact _.
      intros H'.
      rewrite /R //= ltn0 in H'.
      apply r_put_vs_put.
      destruct f; [ done | simpl ].
      apply r_put_rhs.
      rewrite bind_ret.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid  | | ]; done.
      ssprove_invariant.
      rewrite /R //.

    + rewrite H.
      apply r_put_vs_put.
      rewrite bind_ret.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid  | | ]; done.
      ssprove_invariant.

      move=> h0 h1 //= [[H0 H1] H2].
      rewrite /R /couple_rhs in H0 |- *.
      get_heap_simpl.
      rewrite -H0 H2.
      rewrite ltnNge H ltnNge (ltnW H) //.
Qed.


Lemma slide_succ {P} {n} {i} : (SLIDE P i n ∘ PK_OTS P false)%share ≈₀ (SLIDE P i.+1 n ∘ PK_OTS P true)%share.
Proof.
  apply (eq_rel_perf_ind _ _ (inv i.+1 ⋊ couple_lhs count_loc flag_loc (R i))).
  1: simpl; ssprove_invariant.
  1: fset_solve.
  1,2: rewrite /R ltn0 //.
  simplify_eq_rel mm'.
  - simplify_linking.
    rewrite cast_fun_K bind_assoc.
    apply r_init.
    2: apply Syncs_conj, Syncs_conj, Syncs_heap_ignore; fset_solve.
    1: intros pk; apply put_pre_cond_conj.
    1: apply put_pre_cond_inv.
    1: apply put_pre_cond_couple_lhs; fset_solve.
    move=> pk //=.
    apply r_ret => s0 s1 [[[H0 H1] H2] H3].
    by repeat split.
  - ssprove_code_simpl; simpl.
    rewrite 3!cast_fun_K bind_ret.
    move: mm' => //= [m m']. 

    apply r_init.
    2: apply Syncs_conj, Syncs_conj , Syncs_heap_ignore; fset_solve.
    1: intros pk; apply put_pre_cond_conj.
    1: apply put_pre_cond_inv.
    1: apply put_pre_cond_couple_lhs; fset_solve.
    intros pk.
    apply r_get_vs_get_remember.
    1: intros ? ? ? => //; apply H; fset_solve.
    intros j.
    ssprove_sync => H.
    destruct (j < i)%N eqn:E1.
    { rewrite ltnS (ltnW E1) bind_ret.
      apply r_put_vs_put.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid | |]; done.
      ssprove_invariant.

      + move=> h0 h1 //= [[[H0 _] _] H2].
        rewrite /R /couple_rhs in H0 |- *.
        get_heap_simpl.
        rewrite -H0 H2 //.
        rewrite ltnS ltnNge (ltnW E1) ltnNge .
        apply leqW, leqW in E1.
        rewrite -ltnS E1 //.
      + move=> h0 h1 //= [[[H0 _] H2] _].
        rewrite /R /couple_lhs in H0 |- *.
        get_heap_simpl.
        rewrite -H0 H2 //.
        rewrite ltnNge E1 ltnNge (ltnW E1) //.
    }
    destruct (j == i)%B eqn:E2.
    { move: E2 => /eqP ->.
      rewrite ltnn ltnS leqnn.
      ssprove_code_simpl.
      ssprove_swap_lhs 0%N.
      1: apply r_put_init_swap; fset_solve.
      apply (r_init_remember_lhs _ _ pk).
      1: apply Remembers_lhs_from_tracked_rhs.
      1: exact _.
      1: do 5 apply Syncs_conj; apply Syncs_heap_ignore; fset_solve.
      ssprove_swap_lhs 0%N.
      apply r_get_remember_lhs => f.
      eapply (r_rem_couple_lhs count_loc flag_loc).
      1,2,3: exact _.
      rewrite /R ltnn.
      destruct f; [ done | move=> _ //= ].
      apply r_put_vs_put.
      apply r_put_lhs.
      rewrite bind_ret.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid | |]; done.
      ssprove_invariant.

      + move=> h0 h1 //= [[[[H0 H1] H2] H3] H4].
        rewrite /R /couple_rhs in H0 |- *.
        get_heap_simpl.
        rewrite -H0 H3 //.
        unfold "-"%Nrec.
        rewrite PeanoNat.Nat.sub_succ.
        rewrite PeanoNat.Nat.sub_succ_l //.
        rewrite PeanoNat.Nat.sub_diag.
        rewrite PeanoNat.Nat.sub_succ_l.
        1: rewrite PeanoNat.Nat.sub_succ_l //.
        apply PeanoNat.Nat.le_succ_diag_r.
      + unfold "-"%Nrec.
        rewrite PeanoNat.Nat.sub_succ.
        rewrite PeanoNat.Nat.sub_diag //.
    }
    destruct (j == i.+1)%B eqn:E3.
    { move: E3 => /eqP ->.
      rewrite ltnn ltnS leqnn.
      ssprove_code_simpl.
      ssprove_swap_rhs 0%N.
      1: apply r_put_init_swap; fset_solve.
      eapply (r_init_remember_rhs _ _ pk).
      1: exact _.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => f.
      eapply (r_rem_couple_rhs count_loc flag_loc).
      1,2,3: exact _.
      rewrite /R ltnn.
      destruct f; [ done | move=> _ //= ].
      apply r_put_vs_put.
      apply r_put_rhs.
      rewrite bind_ret.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid | |]; done.
      ssprove_invariant.
      + unfold "-"%Nrec.
        rewrite 2!PeanoNat.Nat.sub_succ.
        rewrite PeanoNat.Nat.sub_diag //.
      + move=> h0 h1 //= [[[[H0 H1] H2] H3] H4].
        rewrite /R /couple_lhs in H0 |- *.
        get_heap_simpl.
        rewrite -H0 H2 //.
        unfold "-"%Nrec.
        rewrite 2!PeanoNat.Nat.sub_succ //.
        rewrite PeanoNat.Nat.sub_succ_r //.
        rewrite PeanoNat.Nat.sub_diag //.
    }
    destruct (j > i.+1)%N eqn:E4.
    { replace (i < j)%N with true.
      2: rewrite ltnW //.
      replace (j < i.+1)%N with false.
      2: rewrite ltnNge ltnW //.
      apply r_put_vs_put.
      rewrite bind_ret.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid | |]; done.
      ssprove_invariant.
      + move=> h0 h1 //= [[[H0 H1] H2] H3].
        rewrite /R /couple_rhs in H0 |- *.
        get_heap_simpl.
        rewrite -H0 H3 //.
        rewrite E4.
        apply ltnW in E4.
        rewrite ltnS E4 //.
      + move=> h0 h1 //= [[[H0 H1] H2] H3].
        rewrite /R /couple_lhs in H0 |- *.
        get_heap_simpl.
        rewrite -H0 H2 //.
        unfold "-"%Nrec.
        apply ltnW in E4.
        rewrite ltnNge E1 E4 //.
    }

    exfalso.
    rewrite 2!ltn_neqAle in E1,E4.
    rewrite 2!Bool.andb_false_iff in E1,E4.
    destruct E1.
    + rewrite E2 // in H0.
    + destruct E4.
      * rewrite eq_sym in E3.
        rewrite E3 // in H1.
      * rewrite ltnNge in H1.
        rewrite H0 // in H1.
Qed.

Lemma adv_cpa_ots {P} {n} :
  ∀ A : adversary (I_PK_CPA P),
  AdvFor (PK_CPA P n) A <=
    \sum_(i <- iota 0 n) AdvFor (PK_OTS P) (A ∘ SLIDE P i n).
Proof.
  intros A.
  rewrite /AdvFor //=.
  rewrite (Adv_perf_l pk_cpa_slide).
  rewrite (Adv_perf_r pk_cpa_slide).
  elim: {+ 2 4}n.
  { rewrite Adv_same big_nil //. }
  intros i IH.
  rewrite -{2}addn1 iotaD big_cat big_seq1 //=.
  nssprove_adv_trans (SLIDE P i n ∘ PK_OTS P true)%share.
  apply Num.Theory.lerD.
  1: apply IH.
  rewrite -(Adv_perf_r slide_succ).
  nssprove_separate.
  rewrite Adv_sep_link //.
Qed.

Local Obligation Tactic := notac.

Program Definition A_SLIDE {P} {A : adversary (I_PK_CPA P)} {i} {n}
  : adversary (I_PK_OTS P) :=
  {module (A ∘ SLIDE P i n)%sep }.
Obligation 1.
  intros.
  apply trimmed_link.
  apply module_trimmed.
Qed.

Lemma AdvForE {P A} : AdvFor P A = Adv (P true) (P false) A.
Proof. done. Qed.

Lemma adv_cpa_otsr {P} {n} :
  ∀ A : adversary (I_PK_CPA P),
  AdvFor (PK_CPA P n) A <=
    \sum_(i <- iota 0 n)
      ( AdvFor (PK_OTSR P) (A ∘ SLIDE P i n ∘ CHOOSE P true)
      + AdvFor (PK_OTSR P) (A ∘ SLIDE P i n ∘ CHOOSE P false)).
Proof.
  intros A.
  eapply Order.le_trans.
  1: apply adv_cpa_ots.
  elim: {+ 1 3}n.
  { rewrite 2!big_nil //. } 
  intros j IH.
  rewrite -addn1 iotaD 2!big_cat 2!big_seq1 //=.
  apply Num.Theory.lerD.
  + apply IH.
  + rewrite add0n.
    unfold AdvFor.
    rewrite 2!(sep_link_assoc A).
    epose proof (Adv_PK_OTS (@A_SLIDE P A j n)).
    unfold AdvFor in H.
    apply H.
Qed.

Theorem adv_cpa_otsr_p {P} {n} {p} :
  ∀ A : adversary (I_PK_CPA P),
  (∀ i b, AdvFor (PK_OTSR P) (A ∘ SLIDE P i n ∘ CHOOSE P b) <= p) →
  AdvFor (PK_CPA P n) A <= p *+ 2 *+ n.
Proof.
  intros A H.
  eapply Order.le_trans.
  1: apply adv_cpa_otsr.
  eapply Order.le_trans.
  + apply Num.Theory.ler_sum => i _.
    apply Num.Theory.lerD; apply H.
  + rewrite big_const_seq.
    rewrite count_predT size_iota.
    rewrite GRing.iter_addr_0.
    rewrite -GRing.mulr2n //.
Qed.

End PKScheme.
