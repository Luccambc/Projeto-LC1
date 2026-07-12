(** Equivalência entre o Princípio da Indução Matemática e o Princípio da Indução Forte *)

(* begin hide *)
Require Import Arith Lia.
(* end hide *)

(** Seja [P] uma propriedade sobre os números naturais. O Princípio da Indução Matemática (PIM) pode ser enunciado da seguinte forma:  *)

Definition PIM :=
  forall P: nat -> Prop,
    (P 0) ->
    (forall k, P k -> P (S k)) ->
    forall n, P n.

(** Seja [Q] uma propriedade sobre os números naturais. O Princípio da Indução Forte (PIF) pode ser enunciado da seguinte forma:  *)

Definition PIF :=
  forall Q: nat -> Prop,
    (forall k, (forall m, m<k -> Q m) -> Q k) ->
    forall n, Q n.


(** Dado um predicado [P] sobre naturais, se existe um natural [n] que satisfaz a propriedade [P], então existe um [m] que é o menor natural que satisfaz a propriedade [P]. Esta propriedade é conhecida como o Princípio da Boa Ordenação (PBO): *)
Definition PBO := forall P : nat -> Prop,
  (exists n : nat, P n) ->
  exists m : nat, P m /\ forall x : nat, x < m -> ~ P x.

(** ** Lemas: as quatro implicações fundamentais

    *** PIM implica PIF

    Esta é a direção mais sutil da primeira equivalência. A
    dificuldade é que a hipótese de indução do PIM ([P k]) é mais
    fraca do que a do PIF ([forall m, m < k -> Q m]), de modo que
    não é possível aplicar o PIM diretamente ao predicado [Q].

    A solução é a técnica clássica de _fortalecimento do predicado_:
    aplicamos o PIM não a [Q], mas ao predicado auxiliar

    [P n := forall m, m < n -> Q m]

    ("todos os naturais menores que [n] satisfazem [Q]"). Para esse
    predicado fortalecido, o esquema base/passo do PIM funciona:

    - _Base_ ([P 0]): não existe [m < 0], logo a afirmação vale por
      vacuidade;

    - _Passo_ ([P k -> P (S k)]): supondo que todo [m < k] satisfaz
      [Q], queremos que todo [m < S k] satisfaça [Q]. Ora, [m < S k]
      significa [m < k] ou [m = k]. No primeiro caso, a hipótese de
      indução resolve; no segundo, [Q k] segue exatamente da premissa
      do PIF aplicada à hipótese de indução.

    Concluído o argumento indutivo, obtemos [forall n m, m < n -> Q m];
    para extrair [Q n], basta instanciar essa conclusão em [S n] e
    usar [n < S n]. *)

Lemma PIM_implies_PIF: PIM -> PIF.
Proof.
  intros Hpim Q Hstep n.
  assert (Hacc: forall n, forall m, m < n -> Q m).
  { apply (Hpim (fun n => forall m, m < n -> Q m)).
    - (* caso base: não há m < 0 *)
      intros m Hm. lia.
    - (* passo indutivo *)
      intros k IH m Hm.
      assert (Hcase: m < k \/ m = k) by lia.
      destruct Hcase as [Hlt | Heq].
      + apply IH. exact Hlt.
      + subst m. apply Hstep. exact IH. }
  apply (Hacc (S n)). lia.
Qed.

(** *** PIF implica PIM

    Esta direção é direta, pois a hipótese de indução do PIF é mais
    forte que a do PIM. Dado um predicado [P] com caso base [P 0] e
    passo [forall k, P k -> P (S k)], aplicamos o PIF a [P] e
    precisamos apenas mostrar a sua premissa: para todo [k], se todo
    [m < k] satisfaz [P], então [P k]. Fazemos análise de casos
    (não indução!) sobre [k]:

    - se [k = 0], o objetivo é [P 0], que é exatamente o caso base;

    - se [k = S k'], a hipótese do PIF aplicada a [k' < S k'] fornece
      [P k'], e o passo indutivo do PIM produz [P (S k')].

    Vale destacar que aqui usamos apenas [destruct] (análise de
    casos sobre os construtores de [nat]), e não a tática
    [induction]: a "força" indutiva vem inteiramente da hipótese
    PIF, como deve ser em uma prova de implicação entre princípios. *)

Lemma PIF_implies_PIM: PIF -> PIM.
Proof.
  intros Hpif P Hbase Hstep n.
  apply Hpif.
  intros k IH.
  destruct k as [| k'].
  - exact Hbase.
  - apply Hstep. apply IH. lia.
Qed.

(** Prove que estes princípios são equivalentes: *)

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof. Admitted.

Theorem PBO_equiv_PIM: PBO <-> PIM.
Proof. Admitted.

Theorem PBO_equiv_PIF: PBO <-> PIF.
Proof. Admitted.

(** Repositório: %\url{https://github.com/flaviodemoura/ind_equiv}% *)
