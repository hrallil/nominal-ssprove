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
      x ← sample uniform #|el|;;
      ret x
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
  simplify_eq_rel n.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  induction n.
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
    rewrite !otf_fto expgAC in IHn |- *.
    rewrite eq_refl.
    simpl.
    apply IHn.
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
  
Definition triple_lrr (l₀ l₁ l₂ : Location) (R : l₀ → l₁ → l₂ → Prop)
  : precond := λ '(h₀, h₁),
    R (get_heap h₀ l₀) (get_heap h₁ l₁) (get_heap h₁ l₂).


Class Triple_lrr (l l' l'' : Location) R pre :=
  is_triple_lrr : ∀ s₀ s₁,
    pre (s₀, s₁) → R (get_heap s₀ l) (get_heap s₁ l') (get_heap s₁ l'').

Lemma Remembers_triple_lrr {l l' l''} {a a' a''} {R} {pre} :
  Remembers_lhs l a pre →
  Remembers_rhs l' a' pre →
  Remembers_rhs l'' a'' pre →
  Triple_lrr l l' l'' R pre →
  ∀ s, pre s →
  R a a' a''.
Proof.
  intros H H' H'' Hi [s0 s1] Hp.
  rewrite -(H _ _ Hp) -(H' _ _ Hp) -(H'' _ _ Hp).
  auto.
Qed.

Lemma triple_lrr_conj_left {l l' l'' R} {pre spre : precond} :
  Triple_lrr l l' l'' R spre → Triple_lrr l l' l'' R (pre ⋊ spre).
Proof. intros C s0 s1 [H0 H1]. by apply C. Qed.

Lemma triple_lrr_conj_right {l l' l'' R} {pre spre : precond} :
  Triple_lrr l l' l'' R pre → Triple_lrr l l' l'' R (pre ⋊ spre).
Proof. intros C s0 s1 [H0 H1]. by apply C. Qed.
  
Notation inv0 t_max := (
  heap_ignore (fset[::mga_loc; rcv_loc cka])
  ⋊ triple_rhs (epoch_loc) (send_loc cka) mga_loc
      (λ t s a, t.+1  = t_max → Some s = a)
  ⋊ triple_lrr (rcv_loc cka) (rcv_loc cka) epoch_loc
      (λ rl rr t, ¬(t.+1  = t_max) → rl = rr)
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
  - eapply Build_SemiInvariant.
    + intros s0 s1 l v.
      move=> /negP H5 /negP H6.   
      intros Q.
      unfold triple_lrr.
      do 4 try rewrite get_set_heap_neq //.
      1-3: apply /eqP; move=> h'; subst.
      1-3: apply H6; simpl; fset_solve.
    + simpl. 
      rewrite get_empty_heap//=.
      (* intros h'.
      destruct h'.
      * subst.
        done.
      * subst.
        done. *)
  - simplify_eq_rel x.
    rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= epoch.
    destruct epoch; ssprove_code_simpl; simpl.
    (* Init epoch *)
    1: {
      ssprove_sync => x_init.
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
      ssprove_swap_seq_lhs [:: 3%N; 2%N; 0%N; 1%N].
      ssprove_contract_put_get_lhs.      
      ssprove_swap_seq_lhs [:: 1%N; 0%N].
      (* Cannot have t*==1 as we cannot challenge there *)
      replace (t == 1%N)%B with false.
      - replace (1%N == t)%B with false.
        + simpl.
          (* init epoch ∧ t=t*-1 (meaning ) *)
          destruct ((2%N == t)%B) eqn:E2.
          * ssprove_swap_seq_rhs [:: 2%N; 1%N; 0%N].
            ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
            ssprove_sync => a.
            ssprove_swap_rhs 0%N.
            ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_lhs 0%N.
            ssprove_swap_lhs 1%N.
            ssprove_swap_lhs 2%N.
            ssprove_swap_lhs 1%N.
            ssprove_contract_put_lhs.
            apply r_put_vs_put.
            ssprove_swap_lhs 1%N.
            ssprove_contract_put_lhs.
            ssprove_swap_rhs 2%N.
            ssprove_swap_rhs 1%N.
            ssprove_contract_put_rhs.
            apply r_put_vs_put.
            apply r_put_vs_put.
            apply r_put_rhs.
            ssprove_restore_mem.
            2: by apply r_ret.
            ssprove_invariant.
            -- done.
            -- intros h0 h1 [[H0 H1] H2] H3.
               get_heap_simpl.
               destruct H3.
               get_heap_simpl.
               move: E2 => /eqP.
               done.
            (* init epoch ∧ else case *)
          * ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N; 0%N].
            ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
            ssprove_sync => a.
            ssprove_swap_seq_rhs [:: 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_rhs 0%N.
            ssprove_swap_seq_rhs [:: 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_seq_rhs [:: 2%N; 1%N].
            ssprove_contract_put_rhs.
            ssprove_swap_rhs 0%N.
            ssprove_swap_seq_rhs [:: 2%N; 1%N].
            ssprove_contract_put_rhs.
            ssprove_swap_lhs 0%N.
            ssprove_swap_seq_lhs [:: 2%N; 1%N].
            ssprove_contract_put_lhs.
            ssprove_swap_seq_lhs [:: 1%N; 0%N; 2%N; 1%N].
            ssprove_contract_put_lhs.
            apply r_put_vs_put.
            apply r_put_vs_put.
            apply r_put_vs_put.
            ssprove_restore_mem.
            -- ssprove_invariant.
              ++  intros h0 h1 [[H0 H1] H2] H3.
                  move: H3. 
                  get_heap_simpl.
                  move: E2 => /eqP.
                  done.
              ++  intros h0 h1 [[H0 H1] H2] H3.
                  get_heap_simpl.
                  done.
            -- apply r_ret. done.
        +  symmetry. apply /eqP. intro h. subst. done.  
      -  symmetry. apply /eqP. intro h. subst. done.
      }

     (* None init epoch *)
     eapply r_get_remind_lhs.
     1: exact _.
     eapply r_get_remind_rhs.
     1: exact _.
     
     (* Not init epoch ∧ t = t*-1 *)
     destruct (epoch.+3 == t)%B.
     + ssprove_swap_seq_lhs [:: 1%N; 0%N].
       ssprove_swap_rhs 0%N.
       ssprove_sync => a.
       ssprove_swap_seq_rhs [:: 1%N; 0%N; 2%N; 1%N].
       ssprove_swap_seq_lhs [:: 0%N; 1%N].
       eapply r_get_remember_lhs => __.
       apply r_forget_lhs.
       eapply r_get_remember_rhs => ___.
       apply r_forget_rhs.
       eapply r_get_remember_lhs => rcv_l.
       eapply r_get_remember_rhs => rcv_r.
       apply r_put_vs_put.
       ssprove_swap_lhs 0%N.
       ssprove_swap_rhs 0%N.
       apply r_put_vs_put.
       apply r_put_rhs.
       apply r_put_lhs.
       (* Random saple of key *)
       destruct ((epoch.+2 == t) && ~~ b)%B.
       *  apply r_const_sample_L.
          1: apply LosslessOp_uniform.
          intros x1.
          admit. (* Now we need to show DDH indistinguishability *)
      (* Normal execution *)
      * apply r_ret.
        admit.        (* rpre_learn to show that rcv_l and rcv_r are the same *)
        (*eapply r_get_remember_rhs => rcv_r.
        eapply r_get_remember_lhs => rcv_l. *)
     (* Not init epoch ∧  *)
     + ssprove_swap_lhs 0%N.
       eapply r_get_remember_lhs => __.
       apply r_forget_lhs.
       apply r_put_vs_put.
       destruct (epoch.+2 == t)%B; destruct (b); simpl.
       - admit.
       - admit.
       - admit.
       - admit.
       
       

      
Qed.


 (*
     ssprove_code_simpl.
     simpl.
      destruct ((t == 1%N)%B && ~~b) eqn:E1.
      2: {
         destruct ((2%N == t)%B) eqn:E2.
         1:{
           ssprove_swap_seq_rhs [:: 0%N; 4%N; 3%N; 2%N; 1%N ].
           ssprove_contract_put_get_rhs.
           ssprove_swap_seq_rhs [:: 4%N; 3%N; 2%N; 1%N ].
           ssprove_contract_put_get_rhs.
           ssprove_swap_lhs 0%N.
           apply r_put_vs_put.
           ssprove_swap_lhs 0%N.
           apply r_put_vs_put.
           apply r_put_vs_put.
           ssprove_sync => a.
           apply r_put_vs_put.
           apply r_put_vs_put.
           ssprove_restore_mem.
           - ssprove_invariant.
            + intros h0 h1 [[H0 H1] H2] H3.
              admit. (* Memory rcv_loc is not updated on the RED side *)
            + done.  
            + intros h0 h1 [[H0 H1] H2] H3.
              admit. (* Memory  mga_loc and rcv_loc only set on one side each *)
           - apply r_ret. done. 
         }
         destruct ((1%N == t)%B) eqn:E3.
           1: {
              destruct ((b)%B ) eqn:E7.
              - admit. (* Were missing g^a *)
              - admit. (* Were missing g^a *)
           }
           ssprove_swap_seq_rhs [:: 2%N; 1%N ].
           ssprove_contract_put_get_rhs.
           ssprove_swap_seq_rhs [:: 0%N; 3%N; 2%N; 1%N ].
           ssprove_contract_put_get_rhs.
           ssprove_swap_lhs 0%N.
           apply r_put_vs_put.
           ssprove_swap_lhs 0%N.
           apply r_put_vs_put.
           apply r_put_vs_put.
           ssprove_sync => a.
           apply r_put_vs_put.
           apply r_put_vs_put.
           ssprove_restore_mem.
           - ssprove_invariant.
              +  intros h0 h1 [[H0 H1] H2] H3.
                 rewrite //= /triple_rhs.
                 admit. (* Memory one extra mga_loc *)
              +  intros h0 h1 [[H0 H1] H2] H3.
                 admit. (* Memory: some implication *)
           - apply r_ret. done. 
        }
        ssprove_swap_seq_rhs [:: 1%N; 0%N].
        destruct ((2%N == t)%B) eqn:E2.
        1: {
          ssprove_swap_seq_rhs [:: 4%N; 3%N; 1%N; 0%N; 2%N; 1%N].
          ssprove_contract_put_get_rhs.
          ssprove_swap_seq_rhs [:: 4%N; 3%N; 2%N; 1%N].
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
            - intros h0 h1 [[H0 H1] H2] H3.
              admit. (* Memory mga_loc and rcv_loc not matching *)
            - intros t1. reflexivity.
          }
        }
        destruct ((1%N == t)%B) eqn:E3.
        (* Case: random sample vs DDH reduction getBC ( t == t* )*)  
        1: { 
            destruct ((b)%B ) eqn:E7.
            - ssprove_swap_seq_lhs [:: 1%N; 0%N].
              ssprove_swap_rhs 0%N.
              admit. (* mga_loc is not sat in this case *)
            - admit. (* mga_loc is not sat in this case *)
        }
        (* random sample <=> else case *)
        ssprove_swap_seq_rhs [:: 0%N; 2%N; 1%N].
        ssprove_contract_put_get_rhs. 
        ssprove_swap_seq_rhs [:: 2%N; 1%N; 0%N].
        ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
        ssprove_sync => x_gen.
        ssprove_swap_seq_rhs [:: 1%N; 0%N; 2%N; 1%N].
        ssprove_contract_put_get_rhs.
        ssprove_swap_rhs 1%N.
        ssprove_swap_rhs 0%N.
        apply r_put_vs_put.
        apply r_put_vs_put.
        apply r_put_vs_put.
        apply r_put_vs_put.
        apply r_put_vs_put.
        ssprove_restore_mem.
        - intros h0 h1 [[[[H0 H1] H2] H3] H4].
          rewrite //= /triple_rhs.
          admit. (* Theyre literally equal *)
        - apply r_const_sample_L.
          1: apply LosslessOp_uniform.
          intros x_init'.
          apply r_const_sample_L.
          1: apply LosslessOp_uniform.
          intros x_gen'.
          admit. (* sampling issue. weve sampled x_init and x_gen at another time *)
    }
    simpl.
    eapply r_get_remind_lhs.
      1: exact _.
    eapply r_get_remind_rhs.
      1: exact _.
    ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
    ssprove_code_simpl.
    simpl.
    destruct ((epoch.+3%N == t)%B) eqn:E4.
    + ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
      ssprove_swap_rhs 0%N.
      ssprove_sync => x_gen.
      ssprove_swap_seq_rhs [:: 1%N; 0%N].
      destruct ((t == epoch.+2)%B  && ~~ b) eqn:E5.
      * ssprove_sync => _.
        admit. (* seems like were trying to compare g^x1 with g^x2 *)
      * admit. (* seems like were trying to compare g^x1 with g^x2 *)
    + destruct ((t == epoch.+2)%B  && ~~ b) eqn:E5.
      * destruct ((epoch.+2 == t)%B) eqn:E6.
        -- simpl.
           destruct ((b)%B ) eqn:E7.
          ++ admit.
          ++ admit.
        -- admit.
      *  destruct ((epoch.+2 == t)%B) eqn:E6.
        -- destruct ((b)%B ) eqn:E7.
          ++ admit.
          ++ admit.
        -- admit.
Qed.*)
