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
Import CKAScheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

Definition cka_ddh : cka_scheme := {|
    Mes := 'fin #|el|
  ; Key := 'fin #|el|
  ; StateS := 'fin #|el|
  ; StateR := 'fin #|exp|

  ; sampleKey :=
    {code 
      x ← sample uniform #|el|;;
      ret x
    }

  ; sampleX := 
    {code 
      x ← sample uniform #|exp| ;;
      ret (x)
    }

  ; keygen := 
    {code 
      x ← sample uniform #|exp| ;;
      ret (op_exp op_g x, x)
    }

  ; ckaS := λ γ x,
    {code
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

Theorem correct_cka_simple : CORR0_simple cka_ddh ≈₀ CORR1_simple cka_ddh.
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


Theorem correct_cka : CORR0 cka_ddh ≈₀ CORR1 cka_ddh.
Proof.
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
  perfect (I_CORR cka_ddh) (CORR0 cka_ddh) (CORR1 cka_ddh).
Proof.
  eapply prove_perfect.
  apply correct_cka.
Qed.

Notation init' := (
  epoch ← get epoch_loc ;;
  match epoch with
  | 0%N =>
    x ← sample uniform #|exp| ;;

    #put (send_loc cka_ddh) := op_exp op_g x ;;
    #put (rcv_loc cka_ddh) := x ;;

    @ret 'unit Datatypes.tt
  | _.+1 =>
    @ret 'unit Datatypes.tt
end).

Definition CKA_SECURITY_RED t :
  module I_DDH (I_CKA_SECURITY cka_ddh) :=
  [module fset [:: epoch_loc ; send_loc cka_ddh ; rcv_loc cka_ddh] ;
    #def #[ EPOCH ] (r : ('stateR cka_ddh)) : (
      ('mes cka_ddh × 'key cka_ddh) × 'option('stateR cka_ddh)
    ) {
      _ ← init' ;;

      epoch ← get epoch_loc ;;
      let epoch_inc := epoch.+1 in
      #put epoch_loc := epoch_inc ;;

      (* Pre-challenge epoch (t - 1) *)
      if epoch_inc.+1 == t then
        #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
        m ← GETA tt ;;

        stateR ← get rcv_loc cka_ddh ;;
        #put (send_loc cka_ddh) := m ;;

        @ret (('mes cka_ddh × 'key cka_ddh) × 'option('stateR cka_ddh))
          ((m, op_exp m stateR), None)
      
      (* Challenge epoch (t) *)
      else if epoch_inc == t then 
        #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;
        '(m, k) ← GETBC tt ;; 
        #put (send_loc cka_ddh) := m ;;

        @ret (('mes cka_ddh × 'key cka_ddh) × 'option('stateR cka_ddh))
          ((m, k), None)
      
      (* This captures t + 1 and other cases *)
      else
        stateS ← get send_loc cka_ddh ;;

        #put (rcv_loc cka_ddh) := r ;;
        #put (send_loc cka_ddh) := op_exp op_g r ;;

        @ret (('mes cka_ddh × 'key cka_ddh) × 'option('stateR cka_ddh))
          ((op_exp op_g r, op_exp stateS r), Some(r))
    }
  ].

(* To be able to argue for left and right locations *)
Definition triple_lrr (l₀ l₁ l₂ : Location) (R : l₀ → l₁ → l₂ → Prop)
  : precond := λ '(h₀, h₁),
    R (get_heap h₀ l₀) (get_heap h₁ l₁) (get_heap h₁ l₂).

(* To be able to argue for left locations *)
Definition triple_lhs (l₀ l₁ l₂ : Location) (R : l₀ → l₁ → l₂ → Prop)
  : precond := λ '(h₀, h₁),
    R (get_heap h₀ l₀) (get_heap h₀ l₁) (get_heap h₀ l₂).

Notation inv0 t_max := (
 heap_ignore (fset[:: mga_loc; rcv_loc cka_ddh])
 (* Connect g^a to our case on t - 1 epoch *)
  ⋊ triple_lrr (rcv_loc cka_ddh) (mga_loc) epoch_loc
      (λ rl mga t, t.+1 = t_max → Some(op_exp op_g rl) = mga)

 (* We only care about
    the receive lock when we enter t - 1 case *)
  ⋊ triple_lrr (rcv_loc cka_ddh) (rcv_loc cka_ddh) epoch_loc
      (λ rl rr t, t.+2 = t_max → rl = rr)
 
 (* Left side receive location is always
    the exponent to the right send location *)
  ⋊ triple_lrr (rcv_loc cka_ddh) (send_loc cka_ddh) epoch_loc
      (λ rl sr t, t != 0 → op_exp op_g rl = sr)
      
 (* Left side receive location is always
    the exponent to the left send location *)
  ⋊ triple_lhs (rcv_loc cka_ddh) (send_loc cka_ddh) epoch_loc
      (λ rl sr t, t != 0 → op_exp op_g rl = sr)
).

Ltac swap_exp :=
  unfold op_exp, op_g in * ;
  rewrite !otf_fto expgAC.

Theorem cka_security_ddh_perf bit t: (t > 1)%N →
  perfect
    (I_CKA_SECURITY cka_ddh)
    (CKA_SECURITY cka_ddh bit t)
    (CKA_SECURITY_RED t ∘ DDH bit).
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
      move => /negP H5 /negP H6.   
      intros Q.
      unfold triple_lrr.
      do 4 try rewrite get_set_heap_neq //.
      1-3: apply /eqP; move=> h'; subst.
      1-3: apply H6; simpl; fset_solve.
    + simpl. 
      rewrite get_empty_heap //=.
      subst.
      intro t1.
      by subst.
  -  eapply Build_SemiInvariant.
    + intros s0 s1 l v.
      move => /negP H5 /negP H6.   
      intros Q.
      unfold triple_lrr.
      do 4 try rewrite get_set_heap_neq //.
      1-3: apply /eqP; move => h'; subst.
      1-3: apply H6; simpl; fset_solve.
    + simpl. 
      rewrite get_empty_heap //=.
   -  eapply Build_SemiInvariant.
    + intros s0 s1 l v.
      move => /negP H5 /negP H6.   
      intros Q.
      unfold triple_lrr.
      do 4 try rewrite get_set_heap_neq //.
      1-3: apply /eqP; move => h'; subst.
      1-3: apply H6; simpl; fset_solve.
    + simpl. 
      rewrite get_empty_heap //=.
   -  eapply Build_SemiInvariant.
    + intros s0 s1 l v.
      move => /negP H5 /negP H6.   
      intros Q.
      unfold triple_lhs.
      do 4 try rewrite get_set_heap_neq //.
      1-3: apply /eqP; move => h'; subst.
      1-3: apply H6; simpl; fset_solve.
    + simpl. 
      rewrite get_empty_heap //=.
  - simplify_eq_rel x.
    rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move => //= epoch.
    destruct epoch; ssprove_code_simpl; simpl.
    (* ========== Init epoch ========== *)
    1: {
      ssprove_sync => x_init.
      ssprove_swap_seq_lhs [:: 1%N; 0%N].
      ssprove_swap_seq_rhs [:: 1%N; 0%N].
      eapply r_get_remind_lhs.
      1: exact _.
      eapply r_get_remind_rhs.
      1: exact _.
      ssprove_swap_seq_lhs [:: 2%N; 1%N].
      ssprove_contract_put_get_lhs.
      ssprove_swap_seq_lhs [:: 1%N; 0%N].
      (* Cannot have t_max = 1 as we cannot challenge there *)
      replace (t == 1%N)%B with false.
      - replace (1%N == t)%B with false.
        + simpl.
          (* init epoch and t = t_max - 1 *)
          destruct ((2%N == t)%B) eqn:E2.
          * simpl.
            ssprove_swap_seq_lhs [:: 1%N; 0%N; 3%N; 2%N; 1%N].
            ssprove_contract_put_get_lhs.
            ssprove_swap_seq_rhs [:: 2%N; 1%N; 0%N].
            ssprove_swap_seq_lhs [:: 2%N; 1%N; 0%N].
            ssprove_sync => a.
            swap_exp.
            rewrite eq_refl.
            simpl.
            ssprove_swap_seq_rhs [:: 0%N; 3%N; 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_seq_rhs [:: 0%N; 3%N; 2%N; 1%N].
            ssprove_contract_put_rhs.
            ssprove_swap_seq_lhs [:: 2%N; 1%N].
            ssprove_contract_put_lhs.
            ssprove_swap_rhs 0%N.
            apply r_put_vs_put.
            ssprove_swap_seq_lhs [:: 0%N; 1%N].
            ssprove_contract_put_lhs.
            do 2 apply r_put_vs_put.
            apply r_put_rhs.
            ssprove_restore_mem.
            2: {
              apply r_ret.
              done.
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
            -- intros h0 h1 [[H0 H1] H2] H3.
               get_heap_simpl.
               done.
          (* init epoch and else case *)
          * simpl.
            ssprove_swap_seq_rhs [:: 2%N; 1%N].
            ssprove_contract_put_get_rhs.
            ssprove_swap_seq_rhs [:: 0%N; 2%N; 1%N].
            ssprove_contract_put_rhs.
            ssprove_swap_seq_rhs [:: 0%N; 2%N; 1%N].
            ssprove_contract_put_rhs.
            ssprove_swap_seq_lhs [:: 1%N; 0%N; 2%N; 1%N].
            ssprove_contract_put_get_lhs.
            swap_exp.
            rewrite eq_refl.
            simpl.
            ssprove_swap_seq_lhs [:: 2%N; 1%N].
            ssprove_contract_put_lhs.
            ssprove_swap_seq_lhs [:: 1%N; 0%N; 2%N; 1%N].
            ssprove_contract_put_lhs.
            do 3 apply r_put_vs_put.
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
               ++  intros h0 h1 [[H0 H1] H2] H3.
                  get_heap_simpl.
                  done.
            -- apply r_ret.
               done.
        +  symmetry. apply /eqP. intro h. subst. done.  
      -  symmetry. apply /eqP. intro h. subst. done.
      }
     (* ========== None init epoch ========== *)
     eapply r_get_remind_lhs.
     1: exact _.
     eapply r_get_remind_rhs.
     1: exact _.
     (* Not init epoch and t = t_max - 1 *)
     destruct (epoch.+3 == t)%B eqn:E1.
     + simpl.
       ssprove_swap_seq_lhs [:: 1%N; 0%N].
       ssprove_swap_rhs 0%N.
       ssprove_sync => a.
       ssprove_swap_seq_rhs [:: 1%N; 0%N; 2%N; 1%N].
       ssprove_swap_seq_lhs [:: 0%N; 1%N].
       eapply r_get_remember_lhs => x0.
       eapply r_get_remember_lhs => rcv_l.
       eapply r_get_remember_rhs => rcv_r.
       eapply rpre_learn.
       {
         intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
         unfold triple_lhs in I4.
         rewrite I5 I7 I8 in I4.
         apply I4.
         done.
       }
       intros send_fact.
       eapply rpre_learn.
       {
         intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
         unfold triple_lrr in I2.
         rewrite I6 I8 I9 in I2.
         apply I2.
         move: E1 => /eqP.
         done.
       }
       intros rcv_fact.
       subst.
       swap_exp.
       rewrite eq_refl.
       simpl.
       ssprove_swap_rhs 0%N.
       apply r_put_vs_put.
       ssprove_swap_lhs 0%N.
       apply r_put_vs_put.
       apply r_put_rhs.
       apply r_put_lhs.
       replace (epoch.+2 == t)%B with false.
       * simpl.
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
            ++ intros h0 h1 [[[[H0 H5] H4] H1] H2] H3.
               get_heap_simpl.
               done.
         -- apply r_ret. done.
       * move: E1 => /eqP E1.
         subst.
         simpl.
         symmetry.
         apply /eqP => //.
     + simpl.
       ssprove_swap_lhs 0%N.
       destruct (epoch.+2 == t)%B eqn:E3.
       * destruct (bit) eqn:E4.
         (* Not init epoch
            and challenging epoch (t = t_max)
            and CKA-norm/RED-norm (bit = true) *)
         ** eapply r_get_remember_lhs => x0.
            ssprove_swap_seq_lhs [:: 1%N; 0%N].
            ssprove_swap_rhs 0%N.
            apply r_get_remember_lhs => rcv_l.
            apply r_get_remember_rhs => mga.
            eapply rpre_learn.
            {
              intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
              unfold triple_lhs in I4.
              rewrite I5 I7 I8 in I4.
              apply I4.
              done.
            }
            intros send_fact.
            eapply rpre_learn.
            {
              intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
              unfold triple_lrr in I1.
              rewrite I6 I8 I9 in I1.
              apply I1.
              move: E3 => /eqP.
              done.
            }
            intros mga_fact.
            subst.
            simpl.
            ssprove_swap_lhs 0%N.
            ssprove_swap_seq_rhs [:: 1%N; 0%N].
            ssprove_sync => a0.
            swap_exp.
            rewrite eq_refl.
            simpl.
            do 3 apply r_put_vs_put.
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
                ++ intros h0 h1 [[[[H0 H2] H3] H4] H5] H6.
                   get_heap_simpl.
                   done.
              -- apply r_ret.
                 done.
         (* Not init epoch
            and challenging epoch (t = t_max)
            and CKA-norm/RED-norm (bit = false) *)
         ** eapply r_get_remember_lhs => x0.
            ssprove_swap_seq_lhs [:: 1%N; 0%N].
            ssprove_swap_rhs 0%N.
            apply r_get_remember_lhs => rcv_l.
            apply r_get_remember_rhs => mga.
            eapply rpre_learn.
            {
              intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
              unfold triple_lhs in I4.
              rewrite I5 I7 I8 in I4.
              apply I4.
              done.
            }
            intros send_fact.
            eapply rpre_learn.
            {
              intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
              unfold triple_lrr in I1. 
              rewrite I6 I8 I9 in I1.
              apply I1.
              move: E3 => /eqP.
              done.
            }
            intros mga_fact.
            subst. 
            simpl.
            ssprove_swap_seq_lhs [:: 0%N; 4%N; 3%N; 2%N; 1%N].
            ssprove_swap_seq_rhs [:: 1%N; 0%N; 2%N; 1%N].
            ssprove_sync => x1.
            eapply rsymmetry.
            eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
            eapply rsymmetry.
            swap_exp.
            rewrite eq_refl.
            simpl.
            do 3 apply r_put_vs_put.
            ssprove_restore_mem.
              -- ssprove_invariant.
                ++ intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
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
                ++ intros h0 h1 [[[[H0 H1] H2] H3] H4] H5.
                   get_heap_simpl.
                   done.
              -- apply r_ret. done.
       (* non-init and else case *)
       * eapply r_get_remember_lhs => x0.
         ssprove_swap_seq_rhs [:: 0%N].
         eapply r_get_remember_rhs => send_x0.
         ssprove_swap_seq_rhs [:: 0%N].
         ssprove_swap_seq_lhs [:: 0%N].
         eapply r_get_remember_lhs => rcv_l.
         eapply rpre_learn.
         {
           intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
           unfold triple_lhs in I4.
           rewrite I5 I7 I9 in I4.
           apply I4.
           done.
         }
         intros send_fact_left.
         eapply rpre_learn.
         {
           intros h0 h1 [[[[[[[[[I0 I1] I2] I3] I4] I5] I6] I7] I8] I9]. 
           unfold triple_lrr in I3.
           rewrite I6 I8 I9 in I3.
           apply I3.
           done.
         }
         intros send_fact.
         subst.
         ssprove_swap_seq_rhs [:: 0%N].
         swap_exp.
         rewrite eq_refl.
         simpl.
         do 3 apply r_put_vs_put.
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
            ++  intros h0 h1 [[[H0 H2] H3] H4] H5.
                get_heap_simpl.
                done.
         -- ssprove_invariant.
            apply r_ret.
            done.
Qed.

Lemma cka_security_ddh
  : ∀ (A : adversary (I_CKA_SECURITY cka_ddh)) t, (t > 1)%N →
  AdvFor (fun bit => CKA_SECURITY cka_ddh bit t) A = AdvFor DDH (A ∘ CKA_SECURITY_RED t).
Proof.
  intros A t tH.
  unfold AdvFor.
  rewrite (Adv_perfect_l (cka_security_ddh_perf _ t tH)).
  rewrite (Adv_perfect_r (cka_security_ddh_perf _ t tH)).
  rewrite Adv_sep_link.
  done.
Qed.

End CKA.
