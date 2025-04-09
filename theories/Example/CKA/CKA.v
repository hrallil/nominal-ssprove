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
Require Import Lia.

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
    x ← sample uniform #|exp| ;;

    #put (send_loc cka) := op_exp op_g x ;;
    #put (rcv_loc cka) := x ;;

    @ret 'unit Datatypes.tt
  | _.+1 =>
    @ret 'unit Datatypes.tt
end). 

Definition RED t :
  module I_DDH (I_CKA_PCS cka) :=
  [module fset [:: epoch_loc ; send_loc cka ; rcv_loc cka] ;
    #def #[ EPOCH ] (_ : 'unit) : (('mes cka × 'key cka) × 'option('stateR cka)) {
      _ ← init' ;;

      epoch ← get epoch_loc ;;
      let epoch_inc := epoch.+1 in
      #put epoch_loc := epoch_inc ;;

      (* Send *)
      if epoch_inc.+1 == t then
        #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
        m ← GETA tt ;;
        (* Only place where we need the receive lock, for the invariant *)
        stateR ← get rcv_loc cka ;;

        #put (send_loc cka) := m ;;

        @ret (('mes cka × 'key cka) × 'option('stateR cka))
          ((m, op_exp m stateR), None)
        
      else if epoch_inc == t then 
        #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;
        '(m, k) ← GETBC tt ;; 
       
        #put (send_loc cka) := m ;;

        @ret (('mes cka × 'key cka) × 'option('stateR cka))
          ((m, k), None)
        (* for the case of t+1, 
           we see that the behavior is captured by the default case *)
      else
        stateS ← get send_loc cka ;;
        
        x ← sample uniform #|exp| ;;
        (* Receive *)
        (* stateR ← get rcv_loc cka ;; *)
        (* '(stateS', k) ← cka.(ckaR) stateR m ;; *)

        #put (rcv_loc cka) := x ;;
        #put (send_loc cka) := op_exp op_g x ;;

        @ret (('mes cka × 'key cka) × 'option('stateR cka))
          ((op_exp op_g x, op_exp stateS x), Some(x))
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
  
  
  (* 
  ⋊ triple_rhs (epoch_loc) (send_loc cka) mga_loc
      (λ t s a, t.+1  = t_max → Some s = a)
      *)
Notation inv0 t_max := (
  heap_ignore (fset[::mga_loc; rcv_loc cka])
  ⋊ triple_lrr (rcv_loc cka) (mga_loc) epoch_loc
      (λ rl mga t, t.+1 = t_max → Some(op_exp op_g rl) = mga) (*Some(op_exp op_g rl) = mga*)
  ⋊ triple_lrr (rcv_loc cka) (rcv_loc cka) epoch_loc
      (λ rl rr t, t.+2 = t_max → rl = rr) (* before t-1 case *)
 ⋊ triple_lrr (rcv_loc cka) (send_loc cka) epoch_loc
      (λ rl sr t, t != 0 → op_exp op_g rl = sr)
 (*⋊ triple_lrr (rcv_loc cka) (rcv_loc cka) epoch_loc
      (λ rl rr t, t.+1 = t_max → rr = Some(None)) *)
).

Theorem not_or : forall A B:Prop, ~ A /\ ~ B -> ~ (A \/ B).
tauto. Qed.

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
      subst.
      intro t1.
      by subst.
      (* intros h'.
      destruct h'.
      * subst.
        done.
      * subst.
        done. *)
  -  eapply Build_SemiInvariant.
    + intros s0 s1 l v.
      move=> /negP H5 /negP H6.   
      intros Q.
      unfold triple_lrr.
      do 4 try rewrite get_set_heap_neq //.
      1-3: apply /eqP; move=> h'; subst.
      1-3: apply H6; simpl; fset_solve.
    + simpl. 
      rewrite get_empty_heap//=.
   -  eapply Build_SemiInvariant.
    + intros s0 s1 l v.
      move=> /negP H5 /negP H6.   
      intros Q.
      unfold triple_lrr.
      do 4 try rewrite get_set_heap_neq //.
      1-3: apply /eqP; move=> h'; subst.
      1-3: apply H6; simpl; fset_solve.
    + simpl. 
      rewrite get_empty_heap//=.
  - simplify_eq_rel x.
    rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= epoch.
    destruct epoch; ssprove_code_simpl; simpl.
    (* ========== Init epoch ========== *)
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
          (* init epoch ∧ t=t*-1 (meaning the epoch before the challenge) *)
          (* So when the challenge is on the 2nd epoch *)
          destruct ((2%N == t)%B) eqn:E2.
          * ssprove_swap_seq_rhs [:: 2%N; 1%N; 0%N].
            ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
            ssprove_sync => a.
            ssprove_swap_rhs 0%N.
            ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_seq_rhs [:: 0%N; 3%N; 2%N; 1%N].
            ssprove_contract_put_rhs.
            ssprove_swap_lhs 0%N.
            ssprove_swap_lhs 1%N.
            ssprove_swap_lhs 2%N.
            ssprove_swap_lhs 1%N.
            ssprove_contract_put_lhs.
            ssprove_swap_rhs 0%N.
            apply r_put_vs_put.
            ssprove_swap_lhs 1%N.
            ssprove_contract_put_lhs.
            apply r_put_vs_put.
            apply r_put_vs_put.
            apply r_put_rhs.
            ssprove_restore_mem.
            2: {
              apply r_ret. unfold op_exp. unfold op_exp, op_g in *.
              rewrite !otf_fto expgAC. done.
            }
            ssprove_invariant.
            -- intros h0 h1 [[H0 H1] H2] H3. 
               get_heap_simpl.
               done.
            -- intros h0 h1 [[H0 H1] H2] H3.
               get_heap_simpl.
               move: H3.
               get_heap_simpl.
               move: E2 => /eqP.
               lia.
            -- intros h0 h1 [[H0 H1] H2] H3.
               get_heap_simpl.
               done.
            (* init epoch ∧ else case *)
          * ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N; 0%N].
            ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
            ssprove_sync => a.
            ssprove_swap_seq_rhs [:: 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_rhs 0%N.
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
              ++  intros h0 h1 [[H0 H1] H2] H3.
                  get_heap_simpl.
                  done.
            -- apply r_ret. unfold op_exp. unfold op_exp, op_g in *.
            rewrite !otf_fto expgAC.
            done.
        +  symmetry. apply /eqP. intro h. subst. done.  
      -  symmetry. apply /eqP. intro h. subst. done.
      }

     (* ========== None init epoch ========== *)
     eapply r_get_remind_lhs.
     1: exact _.
     eapply r_get_remind_rhs.
     1: exact _.
     
     (* Not init epoch ∧ t = t*-1 *)
     destruct (epoch.+3 == t)%B eqn:E1.
     + ssprove_swap_seq_lhs [:: 1%N; 0%N].
       ssprove_swap_rhs 0%N.
       ssprove_sync => a.
       ssprove_swap_seq_rhs [:: 1%N; 0%N; 2%N; 1%N].
       ssprove_swap_seq_lhs [:: 0%N; 1%N].
       eapply r_get_remember_lhs => __.
       apply r_forget_lhs.
       eapply r_get_remember_lhs => rcv_l.
       eapply r_get_remember_rhs => rcv_r.
       eapply rpre_learn.
       { intros h0 h1 [[[[[[I0 I1] I2] I3] I4] I5] I6]. 
          unfold triple_lrr in I1. 
          rewrite I4 I5 I6 in I1.
          apply I1.
          move: E1 => /eqP E1.
          subst.
          lia.
          (* question intros [H1 | H2]; inversion H1 || inversion H2; lia. *)
          
       }
       intros rcv_fact. 
       ssprove_swap_rhs 0%N.
       apply r_put_vs_put.
       ssprove_swap_lhs 0%N.
       apply r_put_vs_put.
       apply r_put_rhs.
       apply r_put_lhs.
       replace (epoch.+2 == t)%B with false.
       * simpl.
         rewrite rcv_fact.
         ssprove_restore_mem.
         -- ssprove_invariant.
            ++ intros h0 h1 [[[[H0 H5] H4] H1] H2] H3.
               get_heap_simpl.
               done.
            ++ intros h0 h1 [[[[H0 H5] H4] H1] H2] H3.
               move: H3.
               get_heap_simpl.
               move: E1 => /eqP //.
               lia.
            ++ intros h0 h1 [[[[H0 H5] H4] H1] H2] H3.
               get_heap_simpl.
               done.
         -- apply r_ret. done.
       * move: E1 => /eqP E1. subst. simpl. symmetry. apply /eqP. done.

     (* Not init epoch ∧ challenging epoch (t==t* ) *)
     + ssprove_swap_lhs 0%N.
       eapply r_get_remember_lhs => __.
       apply r_forget_lhs.
       destruct (epoch.+2 == t)%B eqn:E3; destruct (b) eqn:E4; simpl.
       (* Not init epoch ∧ challenging epoch (t = t_max) ∧  cka-norm/RED-norm *)
       * ssprove_swap_lhs 1%N.
         ssprove_swap_lhs 0%N.
         ssprove_swap_rhs 0%N.
         apply r_get_remember_lhs => rcv_l.
         apply r_get_remember_rhs => mga.
         eapply rpre_learn.
         { intros h0 h1 [[[[[[[I0 I7] I1] I2] I3] I4] I5] I6]. 
          unfold triple_lrr in I7. 
          rewrite I4 I5 I6 in I7.
          apply I7.
          apply /eqP. apply E3.
         }
       intros mga_fact.
       subst.
       simpl.
       ssprove_swap_lhs 0%N.
       ssprove_swap_seq_rhs [:: 1%N; 0%N].
       ssprove_sync => a0.
       apply r_put_vs_put.
       apply r_put_vs_put.
       apply r_put_vs_put.
       ssprove_restore_mem.
         -- ssprove_invariant.
            ++ intros h0 h1 [[[[H0 H2] H3] H4] H5] H6.
               move: H6.
               get_heap_simpl.
               move: E1 => /eqP //.
            ++ intros h0 h1 [[[[H0 H2] H3] H4] H5] H6.
               move: H6.
               get_heap_simpl.
               move: E3 => /eqP //.
               lia.
            ++ intros h0 h1 [[[[H0 H2] H3] H4] H5] H6.
               get_heap_simpl.
               done.
         -- apply r_ret.
            unfold op_exp, op_g in *.
            rewrite !otf_fto expgAC.
            done.
            
       (* Not init epoch ∧ challenging epoch (t==t* ) ∧ cka-sample/RED-sampl *)
       * ssprove_swap_lhs 1%N.
         ssprove_swap_lhs 0%N.
         ssprove_swap_rhs 0%N.
         apply r_get_remember_lhs => rcv_l.
         apply r_get_remember_rhs => mga.
         eapply rpre_learn.
         { intros h0 h1 [[[[[[[I0 I7] I1] I2] I3] I4] I5] I6]. 
          unfold triple_lrr in I7. 
          rewrite I4 I5 I6 in I7.
          apply I7.
          apply /eqP. apply E3.
         }
         intros mga_fact.
         subst. 
         simpl.
         ssprove_swap_seq_lhs [:: 0%N; 3%N; 2%N; 1%N].
         ssprove_swap_seq_rhs [:: 1%N; 0%N; 2%N; 1%N].
         ssprove_sync => x1.
         eapply rsymmetry.
         eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
         eapply rsymmetry.
         apply r_put_vs_put.
         apply r_put_vs_put.
         apply r_put_vs_put.
         ssprove_restore_mem.
         -- ssprove_invariant.
            ++  intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
                get_heap_simpl.
                move: H5.
                get_heap_simpl.
                move: E3 => /eqP.
                lia.
            ++ intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
               move: H5.
               get_heap_simpl.
               move: E3 => /eqP.
               lia.
            ++ intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
               get_heap_simpl.
               done.
               (*right.
               move: E3 => /eqP.
               done.*)
         -- apply r_ret. done.
       
       (* non-init ∧ challenging epoch ∧ cka-norm/RED-sample *)
       * ssprove_swap_seq_rhs [:: 0%N].
         ssprove_swap_seq_lhs [:: 0%N; 1%N; 2%N; 3%N].
         eapply r_get_remember_rhs => send_x0.
         ssprove_swap_seq_rhs [:: 0%N].
         ssprove_sync => a.
         eapply r_get_remember_lhs => rcv_l.
         eapply rpre_learn.
         { intros h0 h1 [[[[[I0 I2] I3] I4] I5] I6]. 
           unfold triple_lrr in I2. 
           rewrite I4 I5 I6 in I2.
           apply I2.
           done.
         }
         intros send_fact.
         ssprove_swap_seq_rhs [:: 0%N].
         ssprove_swap_seq_rhs [:: 1%N].
         apply r_put_vs_put.
         apply r_put_vs_put.
         apply r_put_vs_put.
         ssprove_restore_mem.
         -- ssprove_invariant.
            ++ intros h0 h1 [[[H0 H2] H3] H4] H5.
                move: H5.
                get_heap_simpl.
                move: E1 => /eqP //.
            ++  intros h0 h1 [[[H0 H2] H3] H4] H5.
                get_heap_simpl.
                done.
            ++  intros h0 h1 [[[H0 H2] H3] H4] H5.
                get_heap_simpl.
                done.
         -- ssprove_invariant.
            apply r_ret.
            unfold op_exp, op_g in *.
            rewrite !otf_fto expgAC.
            rewrite -send_fact.
            rewrite 2!otf_fto.
            done.
        
       * ssprove_swap_seq_rhs [:: 0%N; 1%N; 2%N; 3%N].
         ssprove_swap_seq_lhs [:: 0%N; 1%N; 2%N; 3%N].
         eapply r_get_remember_rhs => send.
         ssprove_sync => a.
         eapply r_get_remember_lhs => rcv_l.
         eapply rpre_learn.
         { intros h0 h1 [[[[[[I0 I1] I2] I3] I4] I5] I6]. 
           unfold triple_lrr in I2. 
           rewrite I4 I5 I6 in I2.
           apply I2.
           done.
         }
         intros send_fact.
         apply r_put_vs_put.
         apply r_put_vs_put.
         apply r_put_vs_put.
         ssprove_restore_mem.
         -- ssprove_invariant.
            ++ intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
                move: H5.
                get_heap_simpl.
                move: E1 => /eqP //.
            ++  intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
                get_heap_simpl.
                done.
            ++  intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
                get_heap_simpl.
                done.
         -- ssprove_invariant.
            apply r_ret.
            rewrite -send_fact.
            unfold op_exp, op_g in *.
            rewrite !otf_fto expgAC.
            done.
Qed.

End CKA.
