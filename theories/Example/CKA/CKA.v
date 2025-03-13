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



Definition red_epoch_a : Location := ('nat; 10%N).
Definition red_epoch_b : Location := ('nat; 11%N).

Definition state_sa_loc (K: cka_scheme) : Location := ('stateS K; 13%N).
Definition state_sb_loc (K: cka_scheme) : Location := ('stateS K; 14%N).
Definition state_ra_loc (K: cka_scheme) : Location := ('stateR K; 15%N).
Definition state_rb_loc (K: cka_scheme) : Location := ('stateR K; 16%N).

Definition red_max_epoch : Location := ('nat; 17%N).

Definition RED_loc :=
  fset [::red_epoch_a ; red_epoch_b ; state_rb_loc cka; state_ra_loc cka; state_sb_loc cka ].

Definition RED t :
  module I_DDH (I_CKA_PCS cka) :=
  [module CKA_PCS_locs cka;
    #def #[ INIT ] (_ : 'unit) : 'unit {
      '(pk, x) ← cka.(keygen) ;;

      #put (state_sa_loc cka) := pk ;;
      #put (state_sb_loc cka) := pk ;;
      #put (state_ra_loc cka) := x ;;
      #put (state_rb_loc cka) := x ;;

      #put epoch_a := 0 ;;
      #put epoch_b := 0 ;;

      @ret 'unit Datatypes.tt
    } ;

    #def #[ SEND_A ] (_ : 'unit) : ('mes cka × 'key cka) {    
      #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
      #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;

      epoch ← get epoch_a ;;
      let epoch_inc := epoch.+1 in
      #put epoch_a := epoch_inc ;;

      if epoch_inc == t.-1 then
        DDH_a ← GETA tt ;;
        stateRB ← get state_rb_loc cka ;;
        @ret ('el × 'el) (DDH_a, op_exp DDH_a stateRB)

      else if epoch_inc == t then 
        (*locations need fixing*)
        '(DDH_b, DDH_c) ← GETBC tt ;; 
        @ret ('el × 'el) (DDH_b, DDH_c)

      (* for the case of t+1, 
         we see that the behavior is captured by the default case *)
      else
        stateSA ← get state_sa_loc cka ;;
        '(stateRA, m, k) ← cka.(ckaS) stateSA ;;
        #put (state_ra_loc cka) := stateRA ;;
        @ret ('mes cka × 'key cka) (m, k)
    } ;

    #def #[ RCV_A ] (m : 'mes cka) : 'unit {
      epoch ← get epoch_a ;;
      #put epoch_a := epoch.+1 ;;
      (* if epoch_inc == t.-1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t then (* should this not exist here *)
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t.+1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else *)
      stateRA ← get state_ra_loc cka ;;
      '(stateSA, k) ← cka.(ckaR) stateRA m ;;
      #put (state_sa_loc cka) := stateSA ;;
      @ret 'unit Datatypes.tt
    } ;

    #def #[ SEND_B ] (_ : 'unit) : ('mes cka × 'key cka) {
      #import {sig #[ GETA ] : 'unit → 'el } as GETA ;;
      #import {sig #[ GETBC ] : 'unit → 'el × 'el } as GETBC ;;

      epoch ← get epoch_b ;;
      let epoch_inc := epoch.+1 in
      #put epoch_b := epoch_inc ;;

      if epoch_inc == t.-1 then
        DDH_a ← GETA tt ;;
        stateRA ← get state_ra_loc cka ;;
        @ret ('el × 'el) (DDH_a, op_exp DDH_a stateRA)

      else if epoch_inc == t then 
        (* locations need fixing *)
        '(DDH_b, DDH_c) ← GETBC tt ;; 
        @ret ('el × 'el) (DDH_b, DDH_c)

      (* For the case of t+1, 
         we see that the behavior is captured by the default case *)
      else
        stateSB ← get state_sb_loc cka ;;
        '(stateRB, m, k) ← cka.(ckaS) stateSB ;;
        #put (state_rb_loc cka) := stateRB ;;
        @ret ('mes cka × 'key cka) (m, k)
      
    } ;

    #def #[ RCV_B ] (m : 'mes cka) : 'unit {
      epoch ← get epoch_b ;;
      #put epoch_b := epoch.+1 ;;
      (* if epoch_inc == t.-1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t then (* should this not exist here *)
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else if epoch_inc == t.+1 then
        #put (state_sa_loc cka) := m ;;
        @ret 'unit Datatypes.tt
        
      else *)
      stateRB ← get state_rb_loc cka ;;
      '(stateSB, k) ← cka.(ckaR) stateRB m ;;
      #put (state_sb_loc cka) := stateSB ;;
      @ret 'unit Datatypes.tt
    }
  ].
  
Notation inv0 t_max := (
  heap_ignore (fset[::mga_loc])
  ⋊ triple_rhs (epoch_a) (state_sb_loc cka) mga_loc
      (λ t r a, t = t_max.-1 → Some r = a)
).
  

Theorem cka_pcs_ddh_perf b t :
  perfect (I_CKA_PCS cka)(CKA_PCS cka b t)(RED t ∘ DDH b).

Proof.
  nssprove_share. eapply prove_perfect.
  Search precond.
  Search triple_rhs.
  apply (eq_rel_perf_ind _ _ (inv0 t)).
  1:admit.
  simplify_eq_rel x.
  2:{}
  - ssprove_sync.
  intros a.
  ssprove_sync.
  ssprove_sync.
  ssprove_sync.
  
Qed.
