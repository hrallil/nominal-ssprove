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

Definition I_PK_OTSR (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P → 'cip P
  ].

Definition PK_OTSR_loc (P : pk_scheme) :=
  fset [:: mpk_loc P ; flag_loc ].

Definition PK_OTSR0 (P : pk_scheme) :
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
      P.(enc) pk m
    }
  ].

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


Definition I_PK_OTS (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P × 'mes P → 'cip P
  ].

Definition PK_OTS_loc (P : pk_scheme) :=
  fset [:: mpk_loc P ; flag_loc ].

Definition PK_OTS0 (P : pk_scheme) :
  game (I_PK_OTS P) :=
  [module PK_OTS_loc P ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      getNone (mpk_loc P) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, _) : 'mes P × 'mes P) : ('cip P) {
      pk ← getSome (mpk_loc P) ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      P.(enc) pk m
    }
  ].

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

Lemma pk_ots0_perf {P} : PK_OTS P true ≈₀ (CHOOSE P true ∘ PK_OTSR0 P)%share.
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  1,2: simplify_linking.
  1,2: ssprove_code_simpl; simpl.
  + ssprove_sync_eq => mpk.
    ssprove_code_simpl_more.
    ssprove_sync_eq => H.
    ssprove_code_simpl.
    apply rsame_head.
    intros [_ pk].
    apply (r_put_vs_put _ _ _ _ _ _ (λ '(h₀, h₁), h₀ = h₁)).
    apply r_ret.
    intros s0 s1 [s1' [[s0' [H' H''']] H'']].
    subst; done.
  + move: m => //= [m _].
    ssprove_sync_eq => mpk.
    ssprove_code_simpl_more.
    ssprove_sync_eq => H.
    ssprove_sync_eq => flag.
    ssprove_sync_eq => H'.
    apply (r_put_vs_put _ _ _ _ _ _ (λ '(h₀, h₁), h₀ = h₁)).
    rewrite -{1}(bind_ret _ (enc P (getSome mpk H) m)).
    admit.
Admitted.

Lemma pk_ots1_perf {P} : PK_OTS P false ≈₀ (CHOOSE P false ∘ PK_OTSR0 P)%share.
Proof.
Admitted.

Lemma choose_perf {P} : (CHOOSE P true ∘ PK_OTSR1 P)%share ≈₀ (CHOOSE P false ∘ PK_OTSR1 P)%share.
Proof.
Admitted.

Lemma Adv_PK_OTS {P} (A : adversary (I_PK_OTS P)) :
  AdvFor (PK_OTS P) A
  <= AdvFor (PK_OTSR P) (A ∘ CHOOSE P true)
  +  AdvFor (PK_OTSR P) (A ∘ CHOOSE P false).
Proof.
  rewrite /AdvFor //=.
  rewrite (Adv_perf_l pk_ots0_perf).
  rewrite (Adv_perf_r pk_ots1_perf).
  nssprove_adv_trans (CHOOSE P true ∘ PK_OTSR1 P)%share.
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
Definition PK_CPA_loc (P : pk_scheme) :=
  fset [:: mpk_loc P ; count_loc ].

Definition PK_CPA0 (P : pk_scheme) (max : nat) :
  game (I_PK_CPA P) :=
  [module fset [:: mpk_loc P ; count_loc ] ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      getNone (mpk_loc P) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, _) : 'mes P × 'mes P) : ('cip P) {
      pk ← getSome (mpk_loc P) ;;
      count ← get count_loc ;; 
      #assert (count < max)%N ;;
      #put count_loc := count + 1 ;;
      P.(enc) pk m
    }
  ].

Definition PK_CPA1 (P : pk_scheme) (max : nat) :
  game (I_PK_CPA P) :=
  [module fset [:: mpk_loc P ; count_loc ] ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      getNone (mpk_loc P) ;;
      '(_, pk) ← P.(keygen) ;;
      #put (mpk_loc P) := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(_, m) : 'mes P × 'mes P) : ('cip P) {
      pk ← getSome (mpk_loc P) ;;
      count ← get count_loc ;; 
      #put count_loc := count + 1 ;;
      #assert (count < max)%N ;;
      P.(enc) pk m
    }
  ].

Definition PK_CPA P max b := if b then PK_CPA0 P max else PK_CPA1 P max.

Definition succ_loc : Location := ('bool; 10%N).
Definition mpk'_loc (P : pk_scheme) : Location := ('option ('pub P); 11%N).

Definition SLIDE (P : pk_scheme) (i n : nat) :
  module (I_PK_OTS P) (I_PK_CPA P) :=
  [module fset [:: count_loc ; mpk'_loc P ] ;
    #def #[ GET ] (_ : 'unit) : ('pub P) {
      #import {sig #[ GET ] : 'unit → 'pub P } as GET ;;
      pk ← GET tt ;;
      #put mpk'_loc P := Some pk ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, m') : 'mes P × 'mes P) : ('cip P) {
      #import {sig #[ QUERY ] : 'mes P × 'mes P → 'cip P } as QUERY ;;
      pk ← getSome mpk'_loc P ;;
      count ← get count_loc ;;
      #put count_loc := count + 1 ;;
      #assert (count < n)%N ;;
      if (count < i)%N then
        c ← P.(enc) pk m ;;
        ret c
      else if (count > i)%N then
        c ← P.(enc) pk m' ;;
        ret c
      else 
        c ← QUERY (m, m') ;;
        ret c
    }
  ].

Lemma cpa_hyb0 {P} {n} : PK_CPA0 P n ≈₀ (SLIDE P 0 n ∘ PK_OTS0 P)%share.
Admitted.

Lemma cpa_hyb1 {P} {n} : PK_CPA1 P n ≈₀ (SLIDE P n n ∘ PK_OTS0 P)%share.
Admitted.

Lemma hyb_succ {P} {n} {i} : (SLIDE P i n ∘ PK_OTS1 P)%share ≈₀ (SLIDE P i.+1 n ∘ PK_OTS0 P)%share.
Admitted.


#[local] Hint Unfold PK_OTS_loc : in_fset_eq.

Lemma cpa_adv {P} {n} :
  ∀ A : adversary (I_PK_CPA P),
  AdvFor (PK_CPA P n) A <= \sum_(i <- iota 0 n) AdvFor (PK_OTS P) (A ∘ SLIDE P i n).
Proof.
  intros A.
  rewrite /AdvFor //=.
  rewrite (Adv_perf_l cpa_hyb0).
  rewrite (Adv_perf_r cpa_hyb1).
  elim: {+ 2 4}n.
  { rewrite Adv_same big_nil //. }
  intros i IH.
  replace (iota 0 i.+1) with ((iota 0 i) ++ [:: i ]).
  2: {
    replace (i.+1) with (i + 1).
    rewrite iotaD.
    simpl.
  }
  Search bigop ([:: _]).
  rewrite big_cat big_seq1 //=.
  nssprove_adv_trans (SLIDE P i n ∘ PK_OTS0 P)%share.
  apply Num.Theory.lerD.
  1: apply IH.
  rewrite -(Adv_perf_r hyb_succ).
  nssprove_separate.
  rewrite Adv_sep_link //.
Qed.


End PKScheme.
