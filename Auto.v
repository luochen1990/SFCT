(** * Auto: More Automation *)

Require Export Imp.

(** 到现在，我们一直用的是 Coq 的策略系统中的非常有限的一部分。在这章中，
    我们会学习 Coq 的策略语言的两个强大的功能：使用 [auto] 和 [eauto]
    进行证明搜索，和使用 [Ltac] 的前提搜索功能进行自动化正向推理。
    这些功能和 Ltac 的脚本功能可以使我们能把证明搞的很短。
    适当使用这些功能，我们也可以把我们的证明可维护性更好，在以后增量修改
    底层的定义后也可以更健壮。
    
    还有第三种主要自动化的的方式，我们还没有完全了解，这就是自带的
    对某些特定种类问题决策算法：[omega] 是这样的一个例子，不过还有其他的。
    我们将稍微多推迟一下这个话题。
*)

(** 我们的动机例子将是这个证明，加上几个在 [Imp] 里的小的改动。
    我们将分几个阶段将它简化。*)

Ltac inv H := inversion H; subst; clear H. 

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2. 
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* 断言的证明 *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b 求值为真 *)
    apply IHE1. assumption.
  - (* b 求值为假（矛盾） *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b 求值为真（矛盾） *)
    rewrite H in H5. inversion H5.
  - (* b 求值为假 *)
    apply IHE1. assumption.
  (* E_WhileEnd *)
  - (* b 求值为假 *)
    reflexivity.
  - (* b 求值为真（矛盾） *)
    rewrite H in H2. inversion H2.
  (* E_WhileLoop *)
  - (* b 求值为假（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为真 *)
    assert (st' = st'0) as EQ1.
    { (* 断言的证明 *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.  Qed.

(** * 证明策略 [auto] 和 [eauto] *)

(** 话说这么久以来，我们（几乎）总是在写证明脚本时通过名字来使用有关的前提和
    引理。特别的，当我们需要一系列的前提的应用时，我们将它们显式地把它们列出。
    （目前讲过的仅有的例外是使用 [assumption] 来搜索一个与目标匹配的没有量词的
    前提和使用 [(e)constructor] 来搜索一个匹配的构造子） *)


Example auto_example_1 : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R. 
Proof.  
  intros P Q R H1 H2 H3. 
  apply H2.  apply H1. assumption.
Qed.

(** 证明策略 [auto] 可以使我们免于这些苦役，办法是 _搜索_ 一个可以
    解决证明目标的一系列应用。
 *)

Example auto_example_1' : forall (P Q R: Prop), (P -> Q) -> (Q -> R) -> P -> R. 
Proof.  
  intros P Q R H1 H2 H3. 
  auto. 
Qed.

(** [auto] 策略可以解决任何可由如下策略的组合解决的证明目标：
    - [intros]
    - [apply]（默认使用一个当前的前提）

    [eauto] 策略与 [auto] 的效果非常相似，除了它使用的是 [eapply]
    而不是 [apply]。
    
 *)

(** 使用 [auto] 一定是“安全”的，意思是说，它不会失败，也不会改变
    当前证明状态：[auto] 要么完全解决它，要么什么也不做。 *)

(** 一个更复杂的例子 *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.


(** 搜索可能需要任意长的时间，所以有限制参数来控制 [auto] 的搜索深度。 *)

Example auto_example_3 : forall (P Q R S T U: Prop), 
                           (P -> Q) -> (Q -> R) -> (R -> S) -> 
                           (S -> T) -> (T -> U) -> P -> U. 
Proof.
  auto. (* 不能解决目标的话，什么也不会发生 *)
  auto 6.  (* 可选参数控制它的搜索深度（默认是 5） *)
Qed.


(** 当搜索当前目标可能的证明时，[auto] 和 [eauto] 会同时考虑当前上下文中的前提
    和一个包含了其他引理和构造子的 _提示库_ 。有些我们已经见到引理和构造子已经
    在默认的提示库里装好了，如 [eq_refl] 、[conj] 、 [or_introl] 、 [or_intror]
 *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto. Qed.


(** 如果我们想看 [auto] 用到了什么，我们可以使用 [info_auto] *)

Example auto_example_5: 2 = 2.
Proof.
  info_auto.  (* 可以代替 reflexivity，因为提示库里有 eq_refl *)
Qed.


(** 我们可以为某一次 [auto] 或 [eauto] 的调用扩展提示库，方法是使用 [auto using ...] *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) -> 
  n <= p -> 
  n = m. 
Proof.
  intros.
  auto. (* 什么都没发生： auto 不会销毁一个前提 *)
  auto using le_antisym. 
Qed.


(** 当然, 在任何开发过程中我们都会有自己特有的一套构造子和引理会
    在证明中经常用到。我们可以将这些加入全局提示库里，方法是在顶层使用：
      Hint Resolve T.
    其中 [T] 是一个顶层的定理或一个归纳定义的命题（也就是说，任何类型是一个
    “蕴含”的命题）。我们也可以使用一个简写：
      Hint Constructors c.
    告诉 Coq 对归纳定义[c] 的 _每一个_ 构造子进行一个 [Hint Resolve]。

    有时我们可能需要
      Hint Unfold d.
    其中，[d] 是一个定义的标识符。这样，[auto] 就知道展开用到的 [d]
    来获得更多的使用已知的引理的机会。
*)

Hint Resolve le_antisym. 

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) -> 
  n <= p -> 
  n = m. 
Proof.
  intros.
  auto. (* 从提示库里得到了引理 *)
Qed.

Definition is_fortytwo x := x = 42. 

Example auto_example_7: forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* 什么都没发生 *)
Abort.

Hint Unfold is_fortytwo. 

Example auto_example_7' : forall x, (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  info_auto.
Qed.

Hint Constructors ceval. 

Definition st12 := update (update empty_state X 1) Y 2. 
Definition st21 := update (update empty_state X 2) Y 1.

Example auto_example_8 : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st21 || s'. 
Proof.
  eexists. info_auto. 
Qed.

Example auto_example_8' : exists s',
  (IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI) / st12 || s'. 
Proof.
  eexists. info_auto. 
Qed.


(** 现在我们来看看 [ceval_deterministic]，并用 [auto] 来简化证明脚本。
    我们发现所有简单的前提的应用和 [reflexivity] 都可以用 [auto] 代替，
    因此我们把它加到每个情况默认执行的策略里。
*)

Theorem ceval_deterministic': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. 
  - (* E_IfTrue *)
    + (* b 求值为假（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b 求值为真（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_WhileEnd *)
    + (* b 求值为真（矛盾） *)
      rewrite H in H2. inversion H2.
  (* E_WhileLoop *)
  - (* b 求值为假（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为真 *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. 
Qed.

(** 如果我们在证明里反复用到某一个策略，我们可以使用一个 [Proof] 命令的变体
    来使这个策略称为默认策略。

    [Proof with t]（其中 [t] 是任意一个策略）使我们在证明中可以使用 [t1...]
    作为 [t1;t] 的简写。作为一个示范，这是一个上一个证明的另一种写法，用到了
    [Proof with auto]。
*)

Theorem ceval_deterministic'_alt: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2...
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_IfTrue *)
    + (* b 求值为假（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse *)
    + (* b 求值为真（矛盾） *)
      rewrite H in H5. inversion H5.
  - (* E_WhileEnd *)
    + (* b 求值为真（矛盾） *)
      rewrite H in H2. inversion H2.
  (* E_WhileLoop *)
  - (* b 求值为假（矛盾） *)
    rewrite H in H4. inversion H4.
  - (* b 求值为真 *)
    assert (st' = st'0) as EQ1...
    subst st'0...
Qed.

(** * 搜索前提 *)

(** 证明变得简单了，但是还是有一定的恼人的重复。我们先从矛盾的情况开始。这些
    矛盾都是因为我们同时有这两个前提：

    [H1: beval st b = false]

    和

    [H2: beval st b = true]

    矛盾是显然的，但是证明有点麻烦：我们必须找到这两个假设 [H1] 和 [H2]，然后
    用一个 [rewrite] 和一个 [inversion]。我们希望自动化这个过程。

    注：事实上，Coq 有一个自带的策略 [congruence]，可以实现这个目的。但是
    我们暂时忽略掉它的存在，而示范如何自己动手构建正向推理的策略。

*)   

(** 第一步，我们抽象出这个证明脚本中的一部分作为一个参数化的 Ltac *)

Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2. 

Theorem ceval_deterministic'': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. 
  - (* E_IfTrue *)
    + (* b 求值为假（矛盾） *)
      rwinv H H5. 
  - (* E_IfFalse *)
    + (* b 求值为真（矛盾） *)
      rwinv H H5. 
  - (* E_WhileEnd *)
    + (* b 求值为真（矛盾） *)
      rwinv H H2. 
  (* E_WhileLoop *)
  - (* b 求值为假（矛盾） *)
    rwinv H H4. 
  - (* b 求值为真 *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. Qed.


(** 但是这并没有改进多少。我们真正希望的是 Coq 能自动发现有关的前提。
    我们可以使用 Ltac 的 [match goal with ... end] 功能达到这个目标。 *)

Ltac find_rwinv :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _ => rwinv H1 H2
  end. 

(** 用中文表示，这个 [match goal] 搜索两个（不同）的前提，使得它们是左边是任意相同的
    表达式 [E]，右边是两个冲突的布尔值。如果找到了这样的前提，就把它们命名为 [H1] 和 [H2]，
    并执行 [=>] 后面的策略。

    将这个策略加入我们默认执行的策略序列中，就把所有矛盾情况解决了。 *)
    
Theorem ceval_deterministic''': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. 
  - (* E_WhileLoop *)
    + (* b 求值为真 *)
      assert (st' = st'0) as EQ1 by auto.
      subst st'0.
      auto. Qed.

(** 最后我们来看看剩余的情况。每一个都用到了一个有条件的前提以得到一个等式。
    目前我们把这些等式列为了断言，所以我们必须猜出需要的等式是什么（虽然
    我们可以用 [auto] 证明它们）。另一个方式是找出用到的有关的前提，然后
    用他们重写，像这样：
*)

Theorem ceval_deterministic'''': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; try find_rwinv; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *. auto.
  - (* E_WhileLoop *)
    + (* b 求值为真 *)
      rewrite (IHE1_1 st'0 H3) in *. auto. Qed.

(** 现在我们就可以自动化找有关的用来重写的前提的这个过程了。 *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R, H2: ?P ?X |- _ => 
         rewrite (H1 X H2) in * 
  end.

(** 但是有许多对前提都具有这种一般形式，而挑出我们真正需要的好像比较复杂。
    一个关键在于认识到我们可以 _全试一遍_！

    - [rewrite] 在得到一个平凡的形如 [X = X] 的等式时会失败。
    - 每一个 [match goal] 在运行时都会不停的找可行的一对前提，直到
        右面的策略成功。如果没有这样的一对前提就会失败。
    - 我们可以把整个策略包在一个 [repeat] 中，这样就可以一直进行有用
        的重写，直到只剩下平凡的了。
*)

  
Theorem ceval_deterministic''''': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  Qed.

(** 这样做的一个重要的成果是，我们的证明脚本在一些对语言的不太大的改变
    后仍能正常使用。比如，我们可以给这个语言增加一个 [REPEAT] 命令。
    （这是 [Hoare.v]）里的一个练习） *)

Module Repeat.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] 行为和 [WHILE] 类似, 只是循环条件在每次循环主体执行 _之后_
    执行，当条件为 _假_ 时重复执行。因此，循环主体至少会执行一次。 *)

Notation "'SKIP'" := 
  CSkip.
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" := 
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" := 
  (CRepeat e1 b2) (at level 80, right associativity).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_RepeatEnd : forall st st' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = true ->
      ceval st (CRepeat c1 b1) st'
  | E_RepeatLoop : forall st st' st'' b1 c1,
      ceval st c1 st' ->
      beval st' b1 = false ->
      ceval st' (CRepeat c1 b1) st'' ->
      ceval st (CRepeat c1 b1) st''
.

Notation "c1 '/' st '||' st'" := (ceval st c1 st') 
                                 (at level 40, st at level 39).


Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; try find_rwinv; repeat find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b 求值为假（矛盾） *)
       find_rwinv.
       (* 啊呀，为什么刚才 find_rwinv 没有为我们解决这个呢？
          因为我们把顺序搞错了*)
  - (* E_RepeatLoop *)
     + (* b 求值为真（矛盾） *)
        find_rwinv.
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inv E2; repeat find_eqn; try find_rwinv; auto.
Qed.
      
End Repeat.

(** 这些例子只是给大家看看“高级自动化”可以做到什么。

    [match goal] 在使用时的细节十分复杂，调试也很不方便。但是我们非常值得
    在证明时至少加入简单的自动化，来避免繁琐的工作，并为未来的修改做好准备。
*)

(** $Date$ *)
