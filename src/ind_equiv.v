(** * Equivalência entre diferentes noções de indução

    Este trabalho formaliza, no assistente de provas Coq/Rocq, a
    equivalência entre três princípios fundamentais sobre os números
    naturais: o Princípio da Indução Matemática (PIM), o Princípio da
    Indução Forte (PIF) e o Princípio da Boa Ordenação (PBO).

    A formalização está organizada da seguinte forma: primeiro
    enunciamos os três princípios como definições de ordem superior
    (proposições que quantificam sobre predicados [P: nat -> Prop]);
    em seguida, provamos quatro lemas, um para cada implicação
    fundamental ([PIM -> PIF], [PIF -> PIM], [PBO -> PIM] e
    [PIF -> PBO]); por fim, os três teoremas de equivalência pedidos
    no enunciado são obtidos por composição desses lemas.

    Uma observação importante, discutida em detalhe ao longo do
    texto: a equivalência entre PIM e PIF é provada de forma
    puramente construtiva (intuicionista), mas as duas direções que
    envolvem o PBO exigem raciocínio clássico. Por esse motivo,
    adicionamos ao código original do professor a importação da
    biblioteca [Classical], que disponibiliza o axioma do terceiro
    excluído e, em particular, a eliminação da dupla negação
    ([NNPP : forall P, ~~P -> P]). Também importamos a biblioteca
    [Lia], que fornece uma tática de decisão para aritmética linear,
    usada para descartar obrigações aritméticas simples (como
    [m < 0 -> False] ou [m < S k -> m < k \/ m = k]) sem poluir as
    provas com manipulações manuais de desigualdades. *)

(* begin hide *)
Require Import Arith Lia.
Require Import Classical.
(* end hide *)

(** ** Os três princípios

    Seja [P] uma propriedade sobre os números naturais. O Princípio
    da Indução Matemática (PIM) afirma que, para provar que todo
    natural satisfaz [P], basta provar o caso base [P 0] e o passo
    indutivo: se [P] vale para um natural [k] qualquer, então vale
    para o seu sucessor [S k]. *)

Definition PIM :=
  forall P: nat -> Prop,
    (P 0) ->
    (forall k, P k -> P (S k)) ->
    forall n, P n.

(** O Princípio da Indução Forte (PIF) substitui a hipótese de
    indução "[P] vale para o antecessor" pela hipótese mais rica
    "[P] vale para _todos_ os naturais estritamente menores que
    [k]". Note que o PIF não possui caso base explícito: quando
    [k = 0], a hipótese [forall m, m < 0 -> Q m] é satisfeita por
    vacuidade, e portanto a premissa do PIF exige que [Q 0] seja
    provado "do nada", o que faz o papel do caso base. *)

Definition PIF :=
  forall Q: nat -> Prop,
    (forall k, (forall m, m<k -> Q m) -> Q k) ->
    forall n, Q n.

(** O Princípio da Boa Ordenação (PBO) afirma que todo predicado
    habitado sobre os naturais possui um menor elemento: se existe
    algum [n] tal que [P n], então existe um [m] tal que [P m] e
    nenhum natural estritamente menor que [m] satisfaz [P]. *)

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

(** *** PBO implica PIM

    Este é o clássico argumento do _menor contraexemplo_, e é aqui
    que a lógica clássica entra pela primeira vez. Queremos provar
    [P n] para um [n] arbitrário, dados o caso base e o passo
    indutivo. Raciocinamos por contradição (via [NNPP]): suponha
    [~ P n]. Então o predicado [fun x => ~ P x] é habitado (por [n]),
    e o PBO aplicado a ele fornece um _menor contraexemplo_: um
    natural [m] tal que [~ P m] e todo [x < m] satisfaz [~ ~ P x].
    Analisamos os dois casos possíveis para [m]:

    - [m = 0]: então [~ P 0], contradizendo diretamente o caso base;

    - [m = S m']: como [m' < S m'], a minimalidade fornece [~ ~ P m'];
      por eliminação da dupla negação ([NNPP]), obtemos [P m'], e o
      passo indutivo produz [P (S m')], contradizendo [~ P m].

    Em ambos os casos chegamos ao absurdo, o que encerra a prova.
    Note que o [NNPP] é usado em dois pontos: na estrutura externa
    (provar [P n] por contradição) e na extração de [P m'] a partir
    de [~ ~ P m']. Nenhum dos dois passos é válido em lógica
    intuicionista, o que é coerente com o fato, visto em sala, de
    que LPM %$\subset$% LPI %$\subset$% LPC em poder dedutivo. *)

Lemma PBO_implies_PIM: PBO -> PIM.
Proof.
  intros Hpbo P Hbase Hstep n.
  apply NNPP. intro HnPn.
  destruct (Hpbo (fun x => ~ P x)) as [m [HnPm Hmin]].
  { exists n. exact HnPn. }
  destruct m as [| m'].
  - (* o menor contraexemplo seria 0: contradiz o caso base *)
    apply HnPm. exact Hbase.
  - (* o menor contraexemplo seria S m': contradiz o passo *)
    apply HnPm. apply Hstep.
    apply NNPP. apply Hmin. lia.
Qed.

(** *** PIF implica PBO

    Esta direção também exige lógica clássica, pois o PBO pede a
    _existência_ de um mínimo, e a estratégia natural é prová-la por
    contradição. Suponha que exista [n] com [P n], mas que _não_
    exista o menor elemento prometido pelo PBO. Mostramos então, por
    indução forte, que na verdade nenhum natural satisfaz [P] — o
    que contradiz a hipótese de que [P] é habitado.

    O passo da indução forte é o coração do argumento: seja [k]
    arbitrário e suponha (hipótese de indução) que nenhum [m < k]
    satisfaz [P]. Se, ainda assim, valesse [P k], então [k] seria
    exatamente um menor elemento de [P]: ele satisfaz [P], e todos os
    menores não satisfazem (pela hipótese de indução). Isso contradiz
    a suposição de que o mínimo não existe. Logo [~ P k], fechando o
    passo indutivo.

    O uso de [NNPP] aparece na estrutura externa da prova: para
    provar a existência do mínimo por contradição, assumimos a sua
    negação e derivamos o absurdo. Provar uma fórmula existencial
    dessa maneira (sem exibir uma testemunha explícita) é um
    raciocínio essencialmente clássico. *)

Lemma PIF_implies_PBO: PIF -> PBO.
Proof.
  intros Hpif P Hex.
  destruct Hex as [n Hn].
  apply NNPP. intro Hno.
  assert (Hall: forall x, ~ P x).
  { apply (Hpif (fun x => ~ P x)).
    intros k IH HPk.
    apply Hno. exists k. split.
    - exact HPk.
    - exact IH. }
  apply (Hall n). exact Hn.
Qed.

(** ** Os teoremas de equivalência

    Com as quatro implicações estabelecidas, os três teoremas do
    enunciado seguem por composição. O primeiro é imediato a partir
    dos dois primeiros lemas. *)

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  split.
  - apply PIM_implies_PIF.
  - apply PIF_implies_PIM.
Qed.

(** Para a segunda equivalência, a direção [PBO -> PIM] é o lema do
    menor contraexemplo. A direção [PIM -> PBO] é obtida compondo
    [PIM -> PIF] com [PIF -> PBO]: em vez de provar essa implicação
    do zero, reaproveitamos o trabalho já feito, o que torna a
    formalização mais enxuta e evita duplicação de argumentos. *)

Theorem PBO_equiv_PIM: PBO <-> PIM.
Proof.
  split.
  - apply PBO_implies_PIM.
  - intro Hpim. apply PIF_implies_PBO.
    apply PIM_implies_PIF. exact Hpim.
Qed.

(** A terceira equivalência também é obtida por composição:
    [PBO -> PIF] é a composição de [PBO -> PIM] com [PIM -> PIF], e
    [PIF -> PBO] é o quarto lema. Assim, as três equivalências
    formam um "triângulo" fechado de implicações
    (PIM %$\to$% PIF %$\to$% PBO %$\to$% PIM), do qual qualquer
    equivalência par a par pode ser extraída. *)

Theorem PBO_equiv_PIF: PBO <-> PIF.
Proof.
  split.
  - intro Hpbo. apply PIM_implies_PIF.
    apply PBO_implies_PIM. exact Hpbo.
  - apply PIF_implies_PBO.
Qed.

(** ** Verificação dos axiomas utilizados

    O comando [Print Assumptions PBO_equiv_PIF] confirma que a única
    hipótese não construtiva usada em toda a formalização é o axioma
    [classic : forall P : Prop, P \/ ~ P] (terceiro excluído),
    proveniente da biblioteca [Classical]. O teorema [PIM_equiv_PIF],
    por sua vez, não depende de axioma algum: sua prova é totalmente
    construtiva. Isso reflete com precisão a situação teórica: a
    equivalência entre indução matemática e indução forte é um fato
    intuicionista, enquanto o Princípio da Boa Ordenação é um
    princípio genuinamente clássico.

    Poderíamos parar nessa constatação empírica, mas é possível ir
    além e _demonstrar_ que o uso de lógica clássica não é uma
    escolha de conveniência, e sim uma necessidade: o lema a seguir
    mostra que o PBO, enunciado para um predicado arbitrário,
    _implica_ o próprio terceiro excluído — e a prova dessa
    implicação é totalmente construtiva.

    A ideia é reduzir uma proposição arbitrária [Q] a um problema de
    minimização. Dado [Q], considere o predicado

    [P n := (n = 1) \/ (n = 0 /\ Q)]

    Esse predicado é sempre habitado (o natural [1] o satisfaz
    incondicionalmente), e o natural [0] o satisfaz se, e somente
    se, [Q] vale. Aplicando o PBO, obtemos um menor elemento [m], e
    a análise de casos sobre [m] decide [Q]:

    - se [m = 0], então [P 0] vale, o que força [Q];

    - se [m = 1], a minimalidade fornece [~ P 0], o que força [~ Q];

    - [m >= 2] é impossível, pois nenhum natural maior que [1]
      satisfaz [P].

    Em outras palavras: o menor elemento prometido pelo PBO funciona
    como um _oráculo_ que decide qualquer proposição. Como o
    terceiro excluído não é demonstrável na lógica intuicionista do
    Coq, segue que nenhuma das direções [PIM -> PBO] e [PIF -> PBO]
    poderia ser provada sem axiomas clássicos: se fosse possível,
    como o PIM é demonstrável construtivamente no Coq (via
    [nat_ind]), o PBO seria um teorema, e por este lema o terceiro
    excluído também seria — um absurdo. *)

Lemma PBO_implies_classic: PBO -> forall Q: Prop, Q \/ ~ Q.
Proof.
  intros Hpbo Q.
  destruct (Hpbo (fun n => n = 1 \/ (n = 0 /\ Q))) as [m [Hm Hmin]].
  - (* o predicado é habitado: 1 o satisfaz *)
    exists 1. left. reflexivity.
  - destruct m as [| [| m']].
    + (* m = 0: P 0 vale, logo Q *)
      destruct Hm as [H01 | [_ HQ]].
      * discriminate H01.
      * left. exact HQ.
    + (* m = 1: a minimalidade dá ~ P 0, logo ~ Q *)
      right. intro HQ.
      apply (Hmin 0).
      * lia.
      * right. split. reflexivity. exact HQ.
    + (* m >= 2: impossível *)
      destruct Hm as [H | [H _]]; discriminate H.
Qed.

(** O comando [Print Assumptions PBO_implies_classic] confirma que
    este lema é fechado sob o contexto global, isto é, não usa
    axioma algum. Neste desenvolvimento, portanto, o PBO mostra-se
    _equivalente aos princípios clássicos_ em um sentido preciso:
    ele implica construtivamente o terceiro excluído (por este
    lema) e, reciprocamente, toda demonstração de PBO a partir do
    PIM depende de raciocínio clássico (por [PIF_implies_PBO], que
    usa [NNPP]). A fronteira entre o construtivo e o clássico neste
    projeto está exatamente sobre o Princípio da Boa Ordenação. *)

(* begin hide *)
Print Assumptions PIM_equiv_PIF.
Print Assumptions PBO_equiv_PIF.
Print Assumptions PBO_implies_classic.
(* end hide *)
