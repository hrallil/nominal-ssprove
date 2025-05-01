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

Module CKA_KEM (GP : GroupParam).

Module DDH' := DDH GP.
Import CKAScheme DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

(* ------------ KEM START -------------- *)

(* Public and secret key *)
Context (chPKey chSKey : choice_type).

(* Plain text *)
Context (chPlain : choice_type).

(* Symmetric key *)
Context (keyD : Op).
Definition chKey := keyD.π1.

Context (ekeyD : Op).
Definition chEKey := ekeyD.π1.

(* Cipher text *)
Context (cipherD : Op).
Definition chCipher := cipherD.π1.

Notation "'smkey" := (chKey) (in custom pack_type at level 2).
Notation "'smkey" := (chKey) (at level 2) : package_scope.

Notation "'pkey" := (chPKey) (in custom pack_type at level 2).
Notation "'pkey" := (chPKey) (at level 2) : package_scope.

Notation "'skey" := (chSKey) (in custom pack_type at level 2).
Notation "'skey" := (chSKey) (at level 2) : package_scope.

Notation "'plain" := (chPlain) (in custom pack_type at level 2).
Notation "'plain" := (chPlain) (at level 2) : package_scope.

Notation "'ekey" := (chEKey) (in custom pack_type at level 2).
Notation "'ekey" := (chEKey) (at level 2) : package_scope.

Notation "'cipher" := (chCipher) (in custom pack_type at level 2).
Notation "'cipher" := (chCipher) (at level 2) : package_scope.

Record KEM_scheme := {
    KEM_kgen : code fset0 [interface] ('pkey × 'skey) ;
    KEM_encap : 'pkey → code fset0 [interface] ('smkey × 'ekey) ;
    KEM_decap : 'skey → 'ekey → 'smkey
}.

Context (η : KEM_scheme).

(* ------------ KEM END -------------- *)

Definition cka_kem : cka_scheme := {|
    Mes := chEKey × chPKey 
  ; Key := chKey
  ; StateS := chPKey
  ; StateR := chSKey

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

  (* not used in KEM *)
  ; keygen_corr := λ r,
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
  |}.
  
Inductive NoFail {A} : raw_code A → Prop :=
  | NoFail_ret : ∀ x,
      NoFail (ret x)
  | NoFail_sampler : ∀ op k,
      LosslessOp op →
      (∀ v, NoFail (k v)) →
      NoFail (pkg_core_definition.sampler op k).

Lemma r_NoFail_L {A B : choiceType} (c : raw_code B) (c₀ : B → raw_code A) (c₁ : raw_code A)
    (pre : precond) (post : postcond A A) :
    NoFail c →
    (∀ x : B, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ x ← c ;; c₀ x ≈ c₁ ⦃ post ⦄.
Proof.
  intros H H'.
  elim: H; intros.
  + apply H'.
  + by apply r_const_sample_L.
Qed.

Lemma r_NoFail_R {A B : choiceType} (c : raw_code B) (c₀ : raw_code A) (c₁ : B → raw_code A)
    (pre : precond) (post : postcond A A) :
    NoFail c →
    (∀ x : B, ⊢ ⦃ pre ⦄ c₀ ≈ c₁ x ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ c₀ ≈ x ← c ;; c₁ x ⦃ post ⦄.
Proof.
  intros H H'.
  elim: H; intros.
  + apply H'.
  + by apply r_const_sample_R.
Qed.

Context (pkey_pair : ('pkey × 'skey) → Prop).
Context (KEM_kgen_spec : ⊢ₛ η.(KEM_kgen) ⦃ pkey_pair ⦄).

Definition encap_spec (pk : 'pkey) (kek : 'smkey × 'ekey) : Prop :=
  ∀ sk, pkey_pair (pk, sk) → η.(KEM_decap) sk kek.2 = kek.1.

Context (KEM_encap_spec : ∀ pk, ⊢ₛ η.(KEM_encap) pk ⦃ encap_spec pk ⦄).

Definition CKA_CORR_KEM := 0%N.
Definition CKA_CORR_KEM_KGEN := 1%N.

Definition I_CORR_KEM_simple :=
  [interface
    #val #[ CKA_CORR_KEM ] : 'unit  → ('smkey × 'smkey)
  ].


Definition CORR1_kem (K : KEM_scheme) :
  game I_CORR_KEM_simple :=
  [module no_locs ;
    #def #[ CKA_CORR_KEM ] (_ : 'unit) : ('smkey × 'smkey) {
      '(kemPKey, kemSKey) ← K.(KEM_kgen) ;;
      '(kemKey, kemEKey) ← K.(KEM_encap)(kemPKey) ;;

      ret (kemKey, kemKey)
    }
  ].

Definition CORR0_kem (K : KEM_scheme) :
  game I_CORR_KEM_simple :=
  [module no_locs ;
    #def #[ CKA_CORR_KEM ] (_ : 'unit) : ('smkey × 'smkey) {
      '(kemPKey, kemSKey) ← K.(KEM_kgen) ;;

      '(kemKey, kemEKey) ← K.(KEM_encap)(kemPKey) ;;

      let kemKey' := K.(KEM_decap)(kemSKey)(kemEKey) in

      ret (kemKey, kemKey')
    }
  ].

Definition CORR_KEM_RED (K : cka_scheme) :
  module I_CORR_KEM_simple (I_CORR_simple K) :=
  [module no_locs ;
    (* CKAKEY matches the oracle name from CORR_simple from the CKAScheme.v *)
    #def #[ CKAKEY ] (_ : 'unit) : 'unit {
      #import {sig #[ CKA_CORR_KEM ] : 'unit → ('smkey × 'smkey) } as GET_CORR_KEM ;;

      '(kemKey, kemKey') ← GET_CORR_KEM tt ;;
      #assert ((kemKey == kemKey')%bool) ;;

      '(kemKey, kemKey') ← GET_CORR_KEM tt ;;
      #assert ((kemKey == kemKey')%bool) ;;
      
      @ret 'unit Datatypes.tt
    }
  ].

Fixpoint repeat_kem {A : choiceType} (n : nat) (x : A) (c : A → raw_code A) := 
  match n with
   | 0%N => ret x
   | n.+1 => 
      x' ← c x ;;
      repeat_kem n x' c
  end.


Instance valid_repeat_kem:
∀ {A : choiceType} (L : {fset Location}) (I : Interface) (c : A → raw_code A) (x : A) (N : nat),
    (∀ i : A, ValidCode L I (c i)) → ValidCode L I (repeat_kem N x c).
    intros.
    generalize dependent x.
    induction N as [|N IH]; intros x0.
    - simpl. eapply valid_ret.
    - simpl. eapply valid_bind.
      + eapply H.
      + intros x'.
        apply IH.
Qed.
  
(*Definition CORR_KEM_FULL_RED (K : cka_scheme) :
  module I_CORR_KEM_simple (I_CORR K) :=
  [module no_locs ;
    (* CKAKEY matches the oracle name from CORR_simple from the CKAScheme.v *)
    #def #[ CKAKEY ] (n : ('nat)) : 'unit {
      #import {sig #[ CKA_CORR_KEM ] : 'unit → ('smkey × 'smkey) } as GET_CORR_KEM ;;
      
       '(pk, x) ← K.(keygen) ;;
      
      repeat (n) ((pk, x) : ('stateS K × 'stateR K))  (fun state =>       
        let '(stateS, stateR) := state in
        
        k ← K.(keygen) ;;
        '(stateR', m, kS) ← K.(ckaS) stateS k ;;
        '(stateS', kR) ← K.(ckaR) stateR m ;;

        #assert (kS == kR) ;;
        @ret ('stateS K × 'stateR K) (stateS', stateR')
      ) ;;
      @ret 'unit Datatypes.tt
    }
  ].*)
Lemma destruct_let_pair : ∀ A B C (xy : A * B) (f : A → B → C), (let (x, y) := xy in f x y) = f xy.1 xy.2.
Proof.
  intros A B C xy f.
  destruct xy.
  by simpl.
Qed.
(*Theorem perfect_0_full :
  (forall k, NoFail (KEM_kgen k)) -> perfect (I_CORR (cka_kem))(CORR0 (cka_kem))
          (CORR_KEM_FULL_RED (cka_kem) ∘ CORR0_kem η).
Proof.
  intros nofail_kgen.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  simplify_linking.
  ssprove_code_simpl; simpl.
  rewrite bind_assoc.
  ssprove_code_simpl; simpl.
  eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec.
  induction m.
    -  intros [pk' sk'] pps'. ssprove_code_simpl; simpl.
      apply r_ret.
      done.
    -  intros [pk' sk'] pps'. ssprove_code_simpl; simpl.
      simplify_linking.
      rewrite bind_assoc.
      ssprove_code_simpl; simpl.
      simplify_linking.
      eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk'' sk''] pps''.
      eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k'' ek''] hkek'.
      rewrite hkek'.
      2: { done. }
      rewrite eq_refl.
      ssprove_code_simpl; simpl.
      eapply rel_jdg_replace_sem_r in IHm; simpl.
      2: { apply pps''. }
      2: {
        ssprove_code_simpl; simpl.
          eapply rreflexivity_rule.
      }
      simpl in IHm.
      apply IHm.
Qed.*)

Definition CORR_KEM_FULL_RED_FINAL (K : cka_scheme) :
  module I_CORR_KEM_simple (I_CORR K) :=
  [module no_locs ;
    (* CKAKEY matches the oracle name from CORR_simple from the CKAScheme.v *)
    #def #[ CKAKEY ] (n : ('nat)) : 'unit {
      #import {sig #[ CKA_CORR_KEM ] : 'unit → ('smkey × 'smkey) } as GET_CORR_KEM ;;
      '(kemKey, kemKey') ← GET_CORR_KEM tt ;;

      repeat (n) ((kemKey, kemKey') : ('smkey × 'smkey)) (fun state =>
        let '(k, k') := state in 
        #assert ((k == k')%bool) ;;
        
        '(k1, k1') ← GET_CORR_KEM tt ;;
        @ret ('smkey × 'smkey) (k1, k1')
      ) ;;

      @ret 'unit Datatypes.tt
    }
  ].
  
Theorem perfect_0_full_final :
  (forall pk, NoFail (KEM_encap η pk)) -> perfect (I_CORR (cka_kem))(CORR0 (cka_kem))
          (CORR_KEM_FULL_RED_FINAL (cka_kem) ∘ CORR0_kem η).
Proof.
  intros nofail_encap.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  simplify_linking.
  ssprove_code_simpl; simpl.
  rewrite cast_fun_K.
  simplify_linking.
  ssprove_code_simpl; simpl.
  eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec.
  induction m.
    - intros [pk' sk'] pps'. ssprove_code_simpl; simpl.
      apply r_NoFail_R.
      1: { done. }
      destruct x.
      apply r_ret.
      done.
    - intros [pk' sk'] pps'. ssprove_code_simpl; simpl.
      simplify_linking.
      ssprove_code_simpl; simpl.
      simplify_linking.
      eapply rel_jdg_replace_sem_l; simpl.
      2: eapply rsame_head => x; rewrite destruct_let_pair; eapply rreflexivity_rule.
        eapply rel_jdg_replace_sem_l; simpl.
      2: eapply swap_code; ssprove_valid; eapply fdisjoint0s.
      eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k' ek'] hkek.

      rewrite hkek.
      2: { done. }
      rewrite eq_refl; simpl.
      rewrite cast_fun_K.
      ssprove_code_simpl; simpl.
      eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk'' sk''] pps''.
      eapply rel_jdg_replace_sem_r in IHm; simpl.
      2: { apply pps''. }
      2: {
        ssprove_code_simpl; simpl.
          eapply rreflexivity_rule.
      }
      simpl in IHm.
      apply IHm.
      Unshelve.
      exact fset0.
Qed.

  
Theorem perfect_1_full_final :
   (forall k, NoFail (KEM_kgen k)) -> (forall pk, NoFail (KEM_encap η pk)) -> perfect (I_CORR (cka_kem))(CORR1 (cka_kem))
          (CORR_KEM_FULL_RED_FINAL (cka_kem) ∘ CORR1_kem η).
Proof.
   intros nofail.
  intros nofail_encap.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  simplify_linking.
  ssprove_code_simpl; simpl.
  rewrite bind_assoc.
  ssprove_code_simpl; simpl.
  apply r_NoFail_R.
  1: { done. }
  induction m.
  - intros [a  a'].
    apply r_NoFail_R.
    1: { done. }
    intros [b b'].
    ssprove_code_simpl; simpl.
    apply r_ret.
    done.
  - intros [a  a'].
    apply r_NoFail_R.
    1: { done. }
    intros [b b'].
    ssprove_code_simpl; simpl.
    rewrite eq_refl.
    ssprove_code_simpl; simpl.
    rewrite cast_fun_K.
    rewrite bind_assoc.
    ssprove_code_simpl; simpl.
    apply r_NoFail_R.
    1: { done. }
    apply IHm.
Qed.


Definition CORR_simple K b := if b then CORR0_simple K else CORR1_simple K.
Definition CORR_KEM η b := if b then CORR0_kem η else CORR1_kem η.

Theorem cka_security_kem_full: ∀ (A : adversary (I_CORR cka_kem)),
  (forall k, NoFail (KEM_kgen k)) ->
  (forall pk, NoFail (KEM_encap η pk)) ->
  AdvFor (CORR (cka_kem)) A <= AdvFor (CORR_KEM η) (A ∘ (CORR_KEM_FULL_RED_FINAL cka_kem)) .
Proof.
  intros A nofail_kgen nofail_encap.
  unfold AdvFor.
  rewrite (Adv_perfect_l (perfect_0_full_final nofail_encap)).
  rewrite (Adv_perfect_r (perfect_1_full_final nofail_kgen nofail_encap)).
  rewrite Adv_sep_link.
  done.
Qed.


Theorem perfect_0 :
  (forall k, NoFail (KEM_kgen k)) -> perfect (I_CORR_simple (cka_kem))(CORR0_simple (cka_kem))
          (CORR_KEM_RED (cka_kem) ∘ CORR0_kem η).
Proof.
  intros nofail_kgen.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  simplify_linking.
  ssprove_code_simpl; simpl.
  rewrite bind_assoc.
  ssprove_code_simpl; simpl.
  rewrite cast_fun_K.
  rewrite bind_assoc.
  ssprove_code_simpl; simpl.
  eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk sk] pps.
  eapply rel_jdg_replace_sem_r; simpl.
  2: {
      eapply rsame_head => x.
      rewrite destruct_let_pair.
      eapply rreflexivity_rule.
  }
  eapply rel_jdg_replace_sem_l; simpl.
    2: eapply rsame_head => x; rewrite destruct_let_pair; eapply rreflexivity_rule.
  eapply rel_jdg_replace_sem_l; simpl.
    2: eapply swap_code; ssprove_valid; eapply fdisjoint0s.
  eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k' ek'] hkek.
  ssprove_code_simpl; simpl.
  elim: (k' == KEM_decap η sk ek')%B.
  1: {
     ssprove_code_simpl; simpl.
     eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk' sk'] pps'.
      apply r_NoFail_L.
      1: { done. }
      intros [pk'' sk''].
      eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k'' ek''] hkek'.
      rewrite hkek'.
    2: { done. }
    rewrite eq_refl; simpl.
    apply r_ret.
    done.
  }
  ssprove_code_simpl; simpl.
  apply r_NoFail_L.
  1: { done. }
  intros [pk'' sk''].
  apply r_fail.
  Unshelve.
  exact fset0.
Qed.

Theorem perfect_1 :
  (forall k, NoFail (KEM_kgen k)) -> (forall pk, NoFail (KEM_encap η pk)) -> perfect (I_CORR_simple (cka_kem))(CORR1_simple (cka_kem))
          (CORR_KEM_RED (cka_kem) ∘ CORR1_kem η).
Proof.
  intros nofail.
  intros nofail_encap.
  nssprove_share.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  simplify_linking.
  ssprove_code_simpl; simpl.
  rewrite bind_assoc.
  ssprove_code_simpl; simpl.
  apply r_NoFail_R.
  1: { done. }
  intros [pk' sk'].
  apply r_NoFail_R.
  1: { done. }
  intros [s sx].
  rewrite cast_fun_K.
  ssprove_code_simpl.
  rewrite eq_refl; simpl.
  apply r_NoFail_R.
  1: { done. }
  intros [pk''' sk'''].
  apply r_NoFail_R.
  1: { done. }
  intros [s'' sx''].
  rewrite eq_refl; simpl.
  apply r_ret.
  done.
Qed.




Theorem cka_security_kem: ∀ (A : adversary (I_CORR_simple cka_kem)),
  (forall k, NoFail (KEM_kgen k)) ->
  (forall pk, NoFail (KEM_encap η pk)) ->
  AdvFor (CORR_simple (cka_kem)) A <= AdvFor (CORR_KEM η) (A ∘ (CORR_KEM_RED cka_kem)) .
Proof.
  intros A nofail_kgen nofail_encap.
  unfold AdvFor.
  rewrite (Adv_perfect_l (perfect_0 nofail_kgen)).
  rewrite (Adv_perfect_r (perfect_1 nofail_kgen nofail_encap)).
  rewrite Adv_sep_link.
  done.
Qed.

End CKA_KEM.
