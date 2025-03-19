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

From NominalSSP Require Import DDH CKAScheme.

Module CKA (GP : GroupParam).

Module DDH' := DDH GP.
Import CKAscheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

Definition cka : cka_scheme := {|
    Mes := 'fin #|el|
  ; Key := 'fin #|el|
  ; StateS := 'fin #|el|
  ; StateR := 'fin #|exp|
  
  ; sampleKey :=
    {code 
      x ← sample uniform #|exp| ;;
      ret (op_exp op_g x)
    }
  
  ; keygen := 
    {code 
      x ← sample uniform #|exp| ;;
      ret (op_exp op_g x, x)
    } 
  ; ckaS := λ γ,
    {code
      x ← sample uniform #|exp| ;;
      let h := γ in 
      ret (x, op_exp op_g x, op_exp h x)
    }
  ; ckaR := λ γ m,
    {code
      let x := γ in
      let h := m in
      ret (h, op_exp h x)
    }
  |}.


Theorem correct_cka_simple : CORR0_simple cka ≈₀ CORR1_simple cka.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros x.
  unfold op_exp, op_g.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros x'.
  rewrite !otf_fto expgAC.
  rewrite eq_refl.
  simpl.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros x''.
  rewrite !otf_fto expgAC.
  rewrite eq_refl.
  simpl.
  apply r_ret => s0 s1.
  split.
    - reflexivity.
    - apply H.
Qed.



Theorem correct_cka : CORR0 cka ≈₀ CORR1 cka.
Proof.
  (*Fix heap_ignore, shouldnt be here*)
  apply (eq_rel_perf_ind _ _ (heap_ignore (fset [::]))).
  1: ssprove_invariant; fset_solve.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  induction m.
  - simpl.
    intros x.
    apply r_ret => s0 s1.
    split.
      + reflexivity.
      + apply H.
  - simpl.
    intros x.
    apply r_const_sample_L.
    1: apply LosslessOp_uniform.
    intros x'.
    unfold op_exp, op_g in *.
    rewrite !otf_fto expgAC in IHm |- *.
    rewrite eq_refl.
    simpl.
    apply IHm.
Qed.

Theorem perf_correct_cka : 
  perfect (I_CORR cka) (CORR0 cka) (CORR1 cka).
Proof.
  eapply prove_perfect.
  apply correct_cka.
Qed.

Notation init' := (
  epoch ← get epoch_loc ;;
  match epoch with
  | 0%N =>
    '(pk, x) ← cka.(keygen) ;;
    #put (send_loc cka) := pk ;;
    #put (rcv_loc cka) := x ;;

    @ret 'unit Datatypes.tt
  | _.+1 =>
    @ret 'unit Datatypes.tt
end). 

Definition RED t :
  module I_DDH (I_CKA_PCS cka) :=
  [module fset [:: epoch_loc ; send_loc cka ; rcv_loc cka] ;
    #def #[ EPOCH ] (_ : 'unit) : ('mes cka × 'key cka) {
      _ ← init' ;;

      epoch ← get epoch_loc ;;
      let epoch_inc := epoch.+1 in
      #put epoch_loc := epoch_inc ;;

      (* Send *)
      if epoch_inc.+1 == t then
        #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
        m ← GETA tt ;;
        stateR ← get rcv_loc cka ;;

        (* Receive *)
        stateR ← get rcv_loc cka ;;
        '(stateS', k) ← cka.(ckaR) stateR m ;;

        #put (send_loc cka) := stateS' ;;

        @ret ('mes cka × 'key cka) (m, k)
        
      else if epoch_inc == t then 
        #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;
        '(m, k) ← GETBC tt ;; 
         
        (* Receive *)
        stateR ← get rcv_loc cka ;;
        '(stateS', k') ← cka.(ckaR) stateR m ;;

        #put (send_loc cka) := stateS' ;;

        @ret ('mes cka × 'key cka) (m, k)

        (* for the case of t+1, 
           we see that the behavior is captured by the default case *)
      else
        stateS ← get send_loc cka ;;
        '(stateR', m, k) ← cka.(ckaS) stateS ;;

        (* Receive *)
        stateR ← get rcv_loc cka ;;
        '(stateS', k) ← cka.(ckaR) stateR m ;;

        #put (rcv_loc cka) := stateR' ;;
        #put (send_loc cka) := stateS' ;;

        @ret ('mes cka × 'key cka) (m, k)
    }
  ].
  
Notation inv0 t_max := (
  heap_ignore (fset[::mga_loc])
  ⋊ triple_rhs (epoch_loc) (send_loc cka) mga_loc
      (λ t r a, t.+1  = t_max → Some r = a)
).
  

Theorem cka_pcs_ddh_perf b t : (t > 1)%N →
  perfect (I_CKA_PCS cka)(CKA_PCS cka b t)(RED t ∘ DDH b).

Proof.
  nssprove_share. 
  intros.
  eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv0 t)).
  1:ssprove_invariant.
  1-4: simpl.
  - fset_solve.
  - left; fset_solve.
  - left; fset_solve.
  - right. right. 
    fset_solve.
  - intros. 
    rewrite get_empty_heap//= in H0.
    rewrite H0 ltnn // in H.
  - simplify_eq_rel x.
    rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= epoch.
    destruct epoch.
    1: {
      ssprove_code_simpl.
      simpl.
      ssprove_sync.
      intros x_init.
      ssprove_swap_lhs 1%N.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      eapply r_get_remind_lhs.
      1: exact _.
      eapply r_get_remind_rhs.
      1: exact _.
      ssprove_swap_lhs 2%N.
      ssprove_swap_lhs 1%N.
      ssprove_contract_put_get_lhs.
      ssprove_swap_lhs 3%N.
      ssprove_swap_lhs 2%N.
      ssprove_swap_lhs 0%N.
      ssprove_swap_lhs 1%N.
      ssprove_contract_put_get_lhs.
      ssprove_swap_lhs 1%N.
      ssprove_swap_lhs 0%N.
      (*      
      eapply r_put_lhs.
      eapply r_put_lhs.
      eapply r_put_lhs.
      eapply r_put_rhs.
      eapply r_put_rhs.
      eapply r_put_rhs.*)
      destruct ((t == 1%N)%B && ~~b) eqn:E1.
      1: {
        ssprove_swap_rhs 1%N.
        ssprove_swap_rhs 0%N.
        destruct ((2%N == t)%B) eqn:E2.
        1: {
          ssprove_swap_rhs 4%N.
          ssprove_swap_rhs 3%N.
          ssprove_swap_rhs 1%N.
          ssprove_swap_rhs 0%N.
          ssprove_swap_rhs 2%N.  
          ssprove_swap_rhs 1%N. 
          ssprove_contract_put_get_rhs.
          ssprove_swap_rhs 4%N.
          ssprove_swap_rhs 3%N.
          ssprove_swap_rhs 2%N.
          ssprove_swap_rhs 1%N.
          ssprove_contract_put_get_rhs.
          ssprove_swap_rhs 0%N.
          apply r_put_vs_put.
          apply r_put_vs_put.
          apply r_put_vs_put.
          ssprove_sync => a.
          ssprove_swap_rhs 0%N.
          ssprove_swap_lhs 0%N.
          apply r_put_vs_put.
          apply r_put_rhs.
          apply r_put_lhs.
          apply r_const_sample_L.
          1: apply LosslessOp_uniform.
          intros x0.
          ssprove_restore_mem.
          1: {
            ssprove_invariant.
            -
            intros h0 h1 [[H0 H1] H2].
            admit.
            - intros t1. reflexivity.
          }
        }
        
        1: {
          eapply r_get_remind_rhs.
          1: exact _.
          ssprove_restore_mem.
          1: {
            ssprove_invariant.
            admit.
          }
        }
      }

      admit.
      apply r_ret.
      intros s0 s1 H.
      split; [ done | apply H ].
    }
    admit.
    ssprove_sync.
    ssprove_sync.
    ssprove_sync.
  
Qed.
