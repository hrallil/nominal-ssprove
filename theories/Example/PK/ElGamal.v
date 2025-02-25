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

From NominalSSP Require Import Prelude Group.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.

From NominalSSP Require Import DDH Misc Scheme.


Module ElGamal (GP : GroupParam).

Module DDH' := DDH GP.
Import PKScheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

Definition elgamal : pk_scheme := {|
    Sec := 'fin #|exp|
  ; Pub := 'fin #|el|
  ; Mes := 'fin #|el|
  ; Cip := 'fin #|el| × 'fin #|el|
  ; sample_Cip :=
    {code
      c₁ ← sample uniform #|el| ;;
      c₂ ← sample uniform #|el| ;;
      ret (c₁, c₂)
    }
  ; keygen :=
    {code
      sk ← sample uniform #|exp| ;;
      ret (sk, op_exp op_g sk)
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp| ;;
      ret (op_exp op_g r, op_mul m (op_exp pk r))
    }
  ; dec := λ sk c,
    {code
      ret (op_mul (snd c) (op_expn (fst c) sk))
    }
  |}.


Theorem correct_elgamal : CORR0 elgamal ≈₀ CORR1 elgamal.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros sk.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros r.
  apply r_ret => s0 s1.
  split; subst; [| done ].
  unfold op_mul, op_exp, op_g, op_expn.
  rewrite !otf_fto expgAC -mulgA mulgV mulg1 fto_otf //.
Qed.


(*
Definition stop_loc : Location := ('option 'unit; 4%N).

Definition RED_loc :=
  fset [:: stop_loc ].
 *)

(*
Definition init' : raw_code ('pub elgamal) := locked (
  #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
  mpk ← get PKScheme.init_loc elgamal ;;
  match mpk with
  | None => 
    pk ← GETA tt ;;
    #put PKScheme.init_loc elgamal := Some pk ;;
    ret pk
  | Some pk =>
    ret pk
  end).
 *)

Notation init' := (
  mpk ← get PKScheme.init_loc elgamal ;;
  match mpk with
  | None => 
    #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
    pk ← GETA tt ;;
    #put PKScheme.init_loc elgamal := Some pk ;;
    ret pk
  | Some pk =>
    ret pk
  end).

(*
#[export] Instance init'_valid {L : {fset Location}} {I : Interface}
  : PKScheme.init_loc elgamal \in L → ValidCode L (I_DDH) init'.
Proof.
  intros H.
  rewrite /init' -lock.
  ssprove_valid.
Qed.
 *)


Definition RED :
  module I_DDH (I_PK_OTSR elgamal) :=
  [module fset [:: flag_loc; PKScheme.init_loc elgamal ] ;
    #def #[ GET ] (_ : 'unit) : 'el {
      pk ← init' ;;
      @ret 'el pk
    } ;
    #def #[ QUERY ] (m : 'el) : 'el × 'el {
      #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;
      _ ← init' ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      '(r, sh) ← GETBC tt ;;
      @ret ('el × 'el) (r, op_mul m sh)
    }
  ].

#[export] Instance valid_RED_DDH0
  : ValidPackage (loc (RED ∘ DDH true)%share)
      Game_import (I_PK_OTSR elgamal) (RED ∘ DDH true)%share.
Proof.
  eapply valid_package_inject_locations.
  2: nssprove_valid.
  apply fsubsetxx.
Qed.

#[export] Instance valid_RED_DDH1
  : ValidPackage (loc (RED ∘ DDH false)%share)
      Game_import (I_PK_OTSR elgamal) (RED ∘ DDH false)%share.
Proof.
  eapply valid_package_inject_locations.
  2: nssprove_valid.
  apply fsubsetxx.
Qed.

(*
Definition Rel0
  (flag : flag_loc) (mpk : mpk_loc elgamal)
  (init : init_loc) (mga : mga_loc) : Prop
  := (isSome mpk == isSome init)%B &&
      if flag then init && ~~ mga else
        (if init then (mpk == mga)%B else ~~ mpk).
 *)

(*
Notation inv0 := (
  heap_ignore (PK_OTSR_loc elgamal :|: (RED_loc :|: DDH0_loc))
  ⋊ quad flag_loc (mpk_loc elgamal) stop_loc mga_loc Rel0
).

Lemma inv0_Invariant :
  Invariant (PK_OTSR_loc elgamal) (RED_loc :|: DDH0_loc) inv0.
Proof.
  ssprove_invariant; [ apply fsubsetxx | done ].
Qed.
 *)

Notation inv0 := (
  heap_ignore (fset [:: mga_loc ])
  ⋊ triple_rhs flag_loc (PKScheme.init_loc elgamal) mga_loc
      (λ f pk ga, ~~ f → pk = ga)
).

Lemma pk_ots_ddh_perf {b} : PK_OTSR elgamal b ≈₀ (RED ∘ DDH b)%share.
Proof.
  apply (eq_rel_perf_ind _ _ inv0).
  1: ssprove_invariant.
  1-4: simpl.
  1: fset_solve.
  1: right; left; fset_solve.
  1: left; fset_solve.
  1: right; right; fset_solve.
  1: done.

  simplify_eq_rel m.
  - rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= pk.
    destruct pk.
    1: {
      rewrite code_link_bind //=.
      apply r_ret.
      intros s0 s1 H.
      split; [ done | apply H ].
    }
    ssprove_code_simpl; simpl.
    ssprove_sync => a.
    apply r_put_rhs.
    apply r_put_vs_put.
    ssprove_restore_mem.
    2: by apply r_ret.
    ssprove_invariant.
    intros h0 h1 H f.
    by get_heap_simpl.

  - rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= pk.
    destruct pk as [pk|].
    1,2: ssprove_code_simpl; simpl.
    + apply r_get_vs_get_remember.
      1: ssprove_invariant.
      intros f.
      ssprove_sync => H.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => ga.
      eapply (r_rem_triple_rhs flag_loc (PKScheme.init_loc elgamal) mga_loc).
      1-4: exact _.
      move: H => /eqP H //= H'.
      rewrite H //= in H'.
      rewrite -H' //= => {H'} {ga}.
      apply r_put_vs_put.
      apply r_put_rhs.
      ssprove_restore_mem.
      1: {
        ssprove_invariant.
        intros h0 h1 [[[[[H0 H1] H2] H3] H4] H5].
        rewrite //= /triple_rhs.
        by get_heap_simpl.
      }
      destruct b; simpl.
      * ssprove_sync => b.
        by apply r_ret.
      * eapply rsymmetry.
        eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
        eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
        by eapply r_ret.
    + apply r_forget_rhs, r_forget_lhs.
      ssprove_sync => a.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      apply r_get_vs_get_remember.
      1: ssprove_invariant.
      move=> //= pk.
      ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N ].
      ssprove_contract_put_get_rhs.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      ssprove_sync => /eqP -> {pk}.
      ssprove_code_simpl; simpl.
      ssprove_swap_rhs 2%N.
      ssprove_swap_rhs 1%N.
      ssprove_contract_put_rhs.
      apply r_put_rhs.
      do 2 apply r_put_vs_put.
      ssprove_restore_mem.
      1: by ssprove_invariant.
      destruct b; simpl.
      * ssprove_sync => b.
        by apply r_ret.
      * eapply rsymmetry.
        eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
        eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
        by eapply r_ret.
Qed.


Lemma elgamal_ots
  : ∀ A : adversary (I_PK_OTSR elgamal),
  AdvFor (PK_OTSR elgamal) A = AdvFor DDH (A ∘ RED).
Proof.
  intros A.
  unfold AdvFor.
  rewrite (Adv_perf_l pk_ots_ddh_perf).
  rewrite (Adv_perf_r pk_ots_ddh_perf).
  rewrite -Adv_sep_link.
  nssprove_separate.
Qed.

Local Obligation Tactic := notac.

Program Definition A' (A : adversary (I_PK_CPA elgamal)) n i b
  : adversary (I_PK_OTSR elgamal) :=
  {module (A ∘ SLIDE elgamal i n ∘ CHOOSE elgamal b)%sep }.
Obligation 1.
  intros.
  apply trimmed_link.
  apply module_trimmed.
Qed.

Theorem elgamal_cpa_p {n} {p}
  : ∀ A : adversary (I_PK_CPA elgamal),
  (∀ i b, AdvFor DDH (A ∘ SLIDE elgamal i n ∘ CHOOSE elgamal b ∘ RED) <= p) →
  AdvFor (PK_CPA elgamal n) A <= p *+ 2 *+ n.
Proof.
  intros A H.
  apply adv_cpa_otsr_p => i b.
  eapply le_trans.
  2: apply (H i b).
  pose proof (elgamal_ots (A' A n i b)) as H'. 
  unfold AdvFor.
  apply eq_ler.
  rewrite 2!(sep_link_assoc _ _ RED).
  apply H'.
Qed.


(*
Axiom negl : nat → Prop.
Axiom poly : raw_module → Axioms.R → Prop.
Axiom poly_sep_link : ∀ {M M'} {B : Axioms.R}, poly M B → poly M' B → poly (M ∘ M')%sep B.
Axiom adv_ddh : ∀ (A : raw_module) B, poly A B → AdvFor DDH A <= negl n.

Corollary elgamal_asym {n} {B : Axioms.R} :
  ∀ A : adversary (I_PK_CPA elgamal),
  poly A B → AdvFor (PK_CPA elgamal n) A <= (B *+ 2 *+ n)%R.
Proof.
  intros A H.
  eapply le_trans.
  1: apply elgamal_cpa.
  eapply le_trans.
  + apply ler_sum.
    intros i _.
    apply Num.Theory.lerD.
    1,2: apply adv_ddh.
    1,2: apply poly_sep_link.
    1,3: apply H.
    1,2: admit.
  +
    rewrite big_const_seq.
    rewrite count_predT size_iota.
    rewrite GRing.iter_addr_0.
    rewrite -GRing.mulr2n //.
Qed.
*)

End ElGamal.


