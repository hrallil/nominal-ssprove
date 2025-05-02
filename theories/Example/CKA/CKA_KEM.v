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

From NominalSSP Require Import DDH CKAScheme KEMScheme.

Module CKA_KEM (GP : GroupParam).

Module DDH' := DDH GP.
Import CKAScheme DDH'.
Import KEMScheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

Context (η : kem_scheme).

Definition cka_kem: cka_scheme := {|
    Mes := η.(KEM_EKey) × η.(KEM_PKey) 
  ; Key := η.(KEM_Key) 
  ; StateS := η.(KEM_PKey) 
  ; StateR := η.(KEM_SKey) 

  ; sampleKey :=
    {code 
      '(kemPKey, _) ← η.(KEM_kgen) ;;
      '(kemKey, _) ← η.(KEM_encap)(kemPKey) ;;
      ret kemKey
    }

  ; keygen :=
    {code
      '(kemPKey, kemSKey) ← η.(KEM_kgen) ;;
      ret (kemPKey, kemSKey)
    }

  ; ckaS := λ γ kgen,
    {code
      '(kemKey, kemEKey) ← η.(KEM_encap)(γ) ;;
      let '(kemPKey, kemSKey) := kgen in

      (* (sk, (c, pk), I) *)
      ret (kemSKey, (kemEKey, kemPKey), kemKey)
    }

  ; ckaR := λ γ m,
    {code
      let '(kemEKey, kemPKey) := m in
      let kemKey := η.(KEM_decap)(γ)(kemEKey) in
      ret (kemPKey, kemKey)
    }

  (* Corruption not implemented *)
  ; keygen_corr := λ r,
    {code
      '(kemPKey, kemSKey) ← η.(KEM_kgen) ;;
      ret (kemPKey, kemSKey)
    }
  |}.

Lemma destruct_let_pair :
  ∀ A B C (xy : A * B) (f : A → B → C), (let (x, y) := xy in f x y) = f xy.1 xy.2.
Proof.
  intros A B C xy f.
  destruct xy.
  by simpl.
Qed.

(* Reduction on correctness with two key exchanges *)
Definition CORR_KEM_RED_simple (K : cka_scheme) :
  module (I_KEM η) (I_CORR_simple K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (_ : 'unit) : 'unit {
      #import {sig #[ GET ] : 'unit → ('kemKey η × 'kemKey η) } as GET_KEM ;;

      '(kemKey, kemKey') ← GET_KEM tt ;;
      #assert (kemKey == kemKey') ;;

      '(kemKey, kemKey') ← GET_KEM tt ;;
      #assert (kemKey == kemKey') ;;

      @ret 'unit Datatypes.tt
    }
  ].

Theorem corr_kem_perfect_0_simple :
  NoFail η.(KEM_kgen) ->
  perfect (I_CORR_simple cka_kem)
    (CORR0_simple cka_kem)
    (CORR_KEM_RED_simple cka_kem ∘ KEM_0 η).
Proof.
  intros nofail_kgen.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_simpl; simpl.
  simplify_linking.
  rewrite cast_fun_K.
  ssprove_code_simpl; simpl.
  eapply r_scheme_bind_spec.
  1: eapply η.(KEM_kgen_spec).
  intros [pk sk] pps.
  eapply rel_jdg_replace_sem_r; simpl.
  2: {
    eapply rsame_head => x.
    rewrite destruct_let_pair.
    eapply rreflexivity_rule.
  }
  eapply rel_jdg_replace_sem_l; simpl.
  2: {
    eapply rsame_head => x.
    rewrite destruct_let_pair.
    eapply rreflexivity_rule.
  }
  eapply rel_jdg_replace_sem_l; simpl.
  2: {
    eapply swap_code. 
    all: ssprove_valid.
    eapply fdisjoint0s.
  }
  eapply r_scheme_bind_spec.
  1: eapply η.(KEM_encap_spec).
  intros [k ek] hkek.
  ssprove_code_simpl; simpl.
  elim: (k == η.(KEM_decap) sk ek)%B.
  1: {
    ssprove_code_simpl; simpl.
    eapply r_scheme_bind_spec.
    1: eapply η.(KEM_kgen_spec).
    intros [pk' sk'] pps'.
    apply r_NoFail_L.
    1: { done. }
    intros [pk'' sk''].
    eapply r_scheme_bind_spec.
    1: eapply η.(KEM_encap_spec).
    intros [k' ek'] hkek'.
    rewrite hkek'.
    2: { done. }
    rewrite eq_refl; simpl.
    apply r_ret.
    done.
  }
  ssprove_code_simpl; simpl.
  apply r_NoFail_L.
  1: { done. }
  intros [pk' sk'].
  apply r_fail.
  Unshelve.
  exact fset0.
Qed.

Theorem corr_kem_perfect_1_simple :
  NoFail η.(KEM_kgen) ->
  (forall pk, NoFail (η.(KEM_encap) pk)) ->
    perfect (I_CORR_simple cka_kem)
    (CORR1_simple cka_kem)
    (CORR_KEM_RED_simple cka_kem ∘ KEM_1 η).
Proof.
  intros nofail_kgen.
  intros nofail_encap.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_simpl; simpl.
  simplify_linking.
  rewrite cast_fun_K.
  ssprove_code_simpl; simpl.
  apply r_NoFail_R.
  1: { done. }
  intros [pk sk].
  apply r_NoFail_R.
  1: { done. }
  intros [k ek].
  rewrite eq_refl; simpl.
  apply r_NoFail_R.
  1: { done. }
  intros [pk' sk'].
  apply r_NoFail_R.
  1: { done. }
  intros [k' ek'].
  rewrite eq_refl; simpl.
  apply r_ret.
  done.
Qed.

Theorem adv_cka_kem_simple: ∀ (A : adversary (I_CORR_simple cka_kem)),
  NoFail η.(KEM_kgen) ->
  (forall pk, NoFail (η.(KEM_encap) pk)) ->
    AdvFor (CORR_simple cka_kem) A <=
    AdvFor (KEM η) (A ∘ (CORR_KEM_RED_simple cka_kem)).
Proof.
  intros A nofail_kgen nofail_encap.
  unfold AdvFor.
  rewrite (Adv_perfect_l (corr_kem_perfect_0_simple nofail_kgen)).
  rewrite (Adv_perfect_r (corr_kem_perfect_1_simple nofail_kgen nofail_encap)).
  rewrite Adv_sep_link.
  done.
Qed.

(* Reduction on full correctness *)
Definition CORR_KEM_RED (K : cka_scheme) :
  module (I_KEM η) (I_CORR K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (n : 'nat) : 'unit {
      #import {sig #[ GET ] : 'unit → ('kemKey η × 'kemKey η) } as GET_KEM ;;
      '(kemKey, kemKey') ← GET_KEM tt ;;

      repeat (n) ((kemKey, kemKey') : ('kemKey η × 'kemKey η)) (fun state =>
        let '(k, k') := state in
        #assert (k == k') ;;

        nextState ← GET_KEM tt ;;
        @ret ('kemKey η × 'kemKey η) (nextState)
      ) ;;

      @ret 'unit Datatypes.tt
    }
  ].

Theorem corr_kem_perfect_0 :
  (forall pk, NoFail (η.(KEM_encap) pk)) ->
    perfect (I_CORR cka_kem)
    (CORR0 cka_kem)
    (CORR_KEM_RED cka_kem ∘ KEM_0 η).
Proof.
  intros nofail_encap.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_simpl; simpl.
  simplify_linking.
  rewrite cast_fun_K.
  ssprove_code_simpl; simpl.
  eapply r_scheme_bind_spec.
  1: eapply η.(KEM_kgen_spec).
  induction m.
    - intros [pk sk] pps.
      ssprove_code_simpl; simpl.
      apply r_NoFail_R.
      1: { done. }
      destruct x.
      apply r_ret.
      done.
    - intros [pk sk] pps.
      ssprove_code_simpl; simpl.
      rewrite cast_fun_K.
      simplify_linking.
      ssprove_code_simpl; simpl.
      eapply rel_jdg_replace_sem_l; simpl.
      2: {
        eapply rsame_head => x.
        rewrite destruct_let_pair.
        eapply rreflexivity_rule.
      }
      eapply rel_jdg_replace_sem_l; simpl.
      2: {
        eapply swap_code.
        all: ssprove_valid.
        eapply fdisjoint0s.
      }
      eapply r_scheme_bind_spec.
      1: eapply KEM_encap_spec.
      intros [k ek] hkek.
      rewrite hkek.
      2: { done. }
      rewrite eq_refl; simpl.
      ssprove_code_simpl; simpl.
      eapply r_scheme_bind_spec.
      1: eapply KEM_kgen_spec.
      intros [pk' sk'] pps'.
      eapply rel_jdg_replace_sem_r in IHm; simpl.
      2: { apply pps'. }
      2: {
        eapply rreflexivity_rule.
      }
      simpl in IHm.
      apply IHm.
      Unshelve.
      exact fset0.
Qed.

Theorem corr_kem_perfect_1 :
  NoFail η.(KEM_kgen) ->
  (forall pk, NoFail (η.(KEM_encap) pk)) ->
    perfect (I_CORR cka_kem)
    (CORR1 cka_kem)
    (CORR_KEM_RED cka_kem ∘ KEM_1 η).
Proof.
  intros nofail_kgen.
  intros nofail_encap.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  ssprove_code_simpl; simpl.
  simplify_linking.
  rewrite cast_fun_K.
  ssprove_code_simpl; simpl.
  apply r_NoFail_R.
  1: { done. }
  induction m.
    - intros [pk sk].
      apply r_NoFail_R.
      1: { done. }
      intros [k ek].
      ssprove_code_simpl; simpl.
      apply r_ret.
      done.
    - intros [pk sk].
      apply r_NoFail_R.
      1: { done. }
      intros [k ek].
      ssprove_code_simpl; simpl.
      rewrite eq_refl.
      ssprove_code_simpl; simpl.
      rewrite cast_fun_K.
      ssprove_code_simpl; simpl.
      apply r_NoFail_R.
      1: { done. }
      apply IHm.
Qed.

Theorem adv_cka_kem: ∀ (A : adversary (I_CORR cka_kem)),
  NoFail η.(KEM_kgen) ->
  (forall pk, NoFail (η.(KEM_encap) pk)) ->
    AdvFor (CORR cka_kem) A <=
    AdvFor (KEM η) (A ∘ (CORR_KEM_RED cka_kem)) .
Proof.
  intros A nofail_kgen nofail_encap.
  unfold AdvFor.
  rewrite (Adv_perfect_l (corr_kem_perfect_0 nofail_encap)).
  rewrite (Adv_perfect_r (corr_kem_perfect_1 nofail_kgen nofail_encap)).
  rewrite Adv_sep_link.
  done.
Qed.

End CKA_KEM.