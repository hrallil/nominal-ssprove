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

From NominalSSP Require Import Prelude.
Import PackageNotation.
#[local] Open Scope package_scope.

Module KEMScheme.

Record kem_scheme := {
  KEM_pkey : choice_type ;
  KEM_skey: choice_type ;
  KEM_key: choice_type ;
  KEM_ekey: choice_type ;

  KEM_kgen : code fset0 [interface] (chProd KEM_pkey KEM_skey) ;
  KEM_encap : KEM_pkey → code fset0 [interface] (chProd KEM_key KEM_ekey) ;
  KEM_decap : KEM_skey → KEM_ekey → KEM_key
}.

Notation " 'kemPKey p " := (KEM_pkey p)
  (at level 3) : package_scope.

Notation " 'kemPKey p " := (KEM_pkey p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'kemSKey p " := (KEM_skey p)
  (at level 3) : package_scope.

Notation " 'kemSKey p " := (KEM_skey p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'kemKey p " := (KEM_key p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'kemKey p " := (KEM_key p)
  (at level 3) : package_scope.

Notation " 'kemEKey p " := (KEM_ekey p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'kemEKey p " := (KEM_ekey p)
  (at level 3) : package_scope.
  
End KEMScheme.