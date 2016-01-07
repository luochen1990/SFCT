(** * Prop: 命题与证据 *)

Require Export Logic.

(* ####################################################### *)
(** * 归纳定义命题*)

(** 在[Basics]一章中，我们定义了一个用来检测一个数字是否为偶数的 _（函数）_ [evenb]，
    若为偶数这个函数将返回[true]。我们能够用这个函数来定义宣称某个数字[n]是偶数的 _（命题）_ ： *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** 也即是说，我们能够将“[n]是偶数”定义成“函数[evenb]在被应用到[n]上时返回[true]”。

    注意，这里我们使用了一个[Definition]来为一个命题赋予一个名字，就像之前我
    们将名字赋予其他类型的表达式一样。这不是一种全新的命题；这仅仅是一条等式。*)

(** 
    另外一个选择是直接定义出偶数这一概念。作为通过[evenb]函数做出定义（“若对
    某个数计算得到[true]，则这个数是偶数”）的替代，我们能够通过给出两种不
    同的展现某个数是偶数的 _（证据）_ 的方式来说明偶数的概念。*)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** 第一行声明了[ev]是一个命题——或者更为形式化地说，一个与自然数“一一对应”
    的命题的集合（也即是说，对于每一个数字[n]，陈述“[n]是偶数”是一个命
    题）。这样的命题所组成的集合通常被称作数字的 _（性质）_ 。

    最后两行定义了给出证明某个数字[m]是偶数的证据的方式。首先[0]是偶数，而[ev_0]
    则是这一事实的证据；第二，如果有[m = S (S n)]且我们能够给出证明[n]为偶数的
    证据[e]，那么[m]也是偶数，且[ev_SS n e]是这一事实的证据。
*)


(** **** Exercise: 1 star (double_even)  *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ##################################################### *)

(** 对于[ev]，我们已经定义了函数[even]（返回一个布尔值），然后又定义了一个能够
   表示它的归纳性关系。然而我们并不一定需要首先将命题当作布尔值函数来看
   待；我们可以直接思考能够表示它的归纳定义。
*)

(** 作为归纳定义命题的另外一个例子，让我们定义一个简单的自然数的性质——
    我们将它称作"[beautiful]"。*)

(** 非形式地说，如果某个数字是[0]、[3]、[5]或者两个[beautiful]的数字的和，那么它是
    [beautiful]的。

    更为准确地说，通过给出四条规则，我们能够定义[beautiful]数：
        - 规则[b_0]：[0]是[beautiful]的。
        - 规则[b_3]：[3]是[beautiful]的。
        - 规则[b_5]：[5]是[beautiful]的。
        - 规则[b_sum]：如果[n]和[m]都是[beautiful]的，那么它们的和也是[beautiful]的。*)

(** 我们会在接下来的课程中看到许多像这样的定义，因此一个使得这些定义易于读
    写的轻便的表示法将会使非形式化的讨论变得更加方便。 _（推理规则）_ 就是这一类
    表示法的其中一种：*)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** *** *)
(** 
    以上的每一条用文字描述的规则在这里都被重排为一条推理规则；这种描述方式
    意欲表达的解读是：如果在横线上方的所有 _（前提）_ 都成立，那么在横线下方的
     _（结论）_ 成立。举例而言，规则[b_sum]说明如果[n]和[m]都有beautiful这一性质，
    那么[n+m]也拥有这一性质。如果一个规则没有在横线之上的前提，那么它的结论
    无条件成立。

    这些规则 _（定义）_ 了[beautiful]这个性质。也就是说，如果我们想要说服某人某个
    数字[beautiful]，那么我们的推理必须基于这些规则。举个简单的例子：
    假设我们宣称数字[5]拥有性质[beautiful]，为了证明它我们只需要指出规则[b_5]
    中声明了这一点；或者假设我们希望证明[8]拥有这个性质，为了证明它，在首先观察到[3]和
    [5]都是[beautiful]的（来自规则[b_3]和[b_5]）之后，我们能够通过规则
    [b_sum]指出[8]作为拥有这一特性的[3]和[5]的和拥有这一特性。这一推论能够通过下面的
    _（证明树）_ 这一形式图形化地表示出来：*)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    当然也存在其他的使用这些规则证明这一事实的方法，比如说这一个证明：
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty)  *)
(** 有多少种不同的证明[beautiful 8]的方式？ *)

(* FILL IN HERE *)
(** [] *)

(* ####################################################### *)
(** ** 构建证据 *)

(** 在Coq中，我们能够用如下的代码表示[beautiful]的定义：*)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

(** *** *)
(** 
    以这种方式引进的规则与已被证明的定理有着相同的地位；也就是说这些规则
    像公理一样不证自立，因此我们能够使用策略[apply]和这些规则的名字来证明某
    些特定的数字拥有[beautiful]这一性质。*)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* 这能够直接从[b_3]得出。*)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* 首先我们使用规则[b_sum]来让Coq知道如何将[n]和[m]实例化。*)
   apply b_sum with (n:=3) (m:=5).
   (* 为了证明[b_sum]生成的子目标，我们必须提供[beautiful 3]和[beautiful 5]的
      证据。幸运的是我们有能够得出它们的规则。*)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** 就像你会期待的那样，我们也能够证明包含有关[beautiful]的前提的定理。*)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercise: 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** * 在证明中使用证据*)
(** ** 针对证据的归纳法*)

(** 除了 _（构造）_ 某些数字是beautiful的证据以外，我们还能够对这些证据
     _（进行推理）_ 。*)

(** 我们用[Inductive]定义引入了[beautiful]的这一事实在向Coq声明了[b_0]、[b_3]、
    [b_5]以及[b_sum]是构造证据的方式的同时也声明了这四个构造子是构造能够证实某
    个数字拥有beautiful这一性质的证据的 _（唯一）_ 的方法。*)

(** 也就是说，如果有人给出了断言[beautiful n]的证据[E]，那么我们可以知道
    [E]一定有着下面四种形式中的其中一种：

      - [E]是[b_0]，且[n]为[0]；
      - [E]是[b_3]，且[n]为[3]；
      - [E]是[b_5]，且[n]为[5]；
      - [E]是[b_sum n1 n2 E1 E2]，其中[n]为[n1+n2]，[E1]是证明[n1]beautiful
        的证据，[E2]是证明[n2]beautiful的证据。*)

(** *** *)    
(** 这允许我们使用我们已经知道的证明策略对任何有着[beautiful n]形式的前提进
    行 _（分析）_ 以知道这些前提是怎样构造的。具体地说，我们能够用之前我们已经看
    到被用在对归纳定义的_（数据）_ 进行推理的[induction]策略来对归纳定义的 _（证据）_ 进
    行推理。

    为了说明这一点，让我们来定义另外一种数字的性质：*)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree)  *)
(** 使用推理规则的表示法写出[gorgeous]数字的定义。
 
(* FILL IN HERE *)
[]
*)


(** **** Exercise: 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(** *** *)
(** 就直观上而言这看上去十分明显：即使[gorgeous]和[beautiful]是由稍微有些不同
    的两组规则表示的，它们实际上说明了同一种性质：拥有前者的数字都同时拥有
    后者，反之亦然。诚然，我们能够证明这一点。*)

Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   - (* n = 0 *) apply b_0.
   - (* n = S n' *) (* 我们在这里卡住了！ *)
Abort.

(** 这里的问题在于进行基于[n]的归纳并不能产出一个有用的归纳前提：知道某个性
    质是否被[n]的前继所具有并不能帮助我们证明[n]本身是否具有这个性质。但是作为
    替代地，我们希望能够得到有关其他数字的归纳前提，比如说[n - 3]和[n - 5]。这将由
    [gorgeous]的构造子的形式精确地给出。*)


(** *** *)

(** 让我们看看当我们试图通过基于证据[H]的归纳来进行这一证明时将会发生什么。*)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   - (* g_0 *)
       apply b_0.
   - (* g_plus3 *) 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   - (* g_plus5 *)
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.


(* 这些练习也需要对证据使用归纳法。*)

(** **** Exercise: 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)




(** **** Exercise: 3 stars, optional (g_times2)  *)
(** 在不使用[gorgeous__beautiful]的情况下证明[g_times2]这一定理。
    你也许会发现下面的引理在证明过程中十分有用。*)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
   (* FILL IN HERE *) Admitted.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   (* FILL IN HERE *) Admitted.
(** [] *)



(** 下面是“具有归纳定义的偶数性是具有计算上的偶数性的充分条件”这一事实的证明。*)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  - (* E = ev_0 *) 
    unfold even. reflexivity.
  - (* E = ev_SS n' E' *)  
    unfold even. apply IHE'.  
Qed.

(** **** Exercise: 1 star (ev__even)  *) 
(** 这个证明能够通过对[n]进行归纳完成吗？如果不能，为什么？*)

(* FILL IN HERE *)
(** [] *)

(** 直观上，对证据[ev n]的归纳法与对[n]的归纳法相似，但是它限制了我们的注意范
    围，让我们只关注可以让证据[ev n]被生成的数字。 *)

(** **** Exercise: 1 star (l_fails)  *)
(** 以下的对证明的尝试不会成功。
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         - (* O *) simpl. apply ev_0.
         - (* S *)
           ...
   我们会直觉性地认为这个证明会无法被完成，因为并不是所有数字都是偶数。
   但是究竟是什么实际上导致了这一证明的失败？

(* FILL IN HERE *)
*)
(** [] *)

(** 下面是需要对证据进行归纳的又一个练习。*)
(** **** Exercise: 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ####################################################### *)
(** ** 对证据进行反演 *)


(** 证明的时候持有某个命题的证据是十分有用的，因为我们可以通过对这些证据的
     _（观察）_ 得到更多的信息。假设现在正在证明“若[n]是偶数则[pred (pred n)]为偶数”
    这一命题，在这一情况下我们并不需要使用归纳法：[inversion]策略已经能够提供
    我们所需的全部信息。

 *)

Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0. 
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n)  *)
(** 假如我们试图以对[n]使用[destruct]代替对[E]的[inversion]，那么会发生什么？ *)

(* FILL IN HERE *)
(** [] *)

(** *** *)
(** 这里是另外一个展示了[inversion]能够缩小相关情况的范围的例子。 *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(** ** 再访反演策略 *)

(** 刚开始的时候这些[inversion]的应用看上去可能会有一点奇怪。
    至今为止我们只是为了利用构造子的单射性或区分不同的构造子而在等价性命题上使用过
    [inversion]而已。但是我们现在知道了[inversion]也可以被用于分析归纳定义的命
    题的证据。

    （你也许会认为[destruct]在这里会是个更加适合的策略。诚然，使用[destruct]
    是可能的，但是它常常会去掉有用的信息，而且在这里[eqn:]限定符并不能对挽救
    这一点起太大的作用。）  

    [inversion]的一般工作模式：假设[I]是指向一个存在于当前上下文中的假设[P]的标
    识符，那么对于[P]的每一个构造子，[inversion I]将会生成对应的子目标；而且在
    这些子目标中，[I]被这个构造子的能够被用于证明[P]时的特定情况代替。有些子目
    标是自我矛盾的，而[inversion]会去掉他们；剩下的子目标则是我们所必须证
    明以构建原初的目标的。

    在这个例子中，[inversion]分析了[ev (S (S n))]的构造，确定了它只能由
    [ev_SS]构造而来，并生成了一个包含了这个构造子的参数作为新的前提的子目标（它同时
    也生成了一个辅助等式，而在这个例子中它并没有用处。）

    我们会在接下来开始探索inversion的更一般的行为。 *)


(** **** Exercise: 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [inversion]策略也可以被用于显示某个前提的荒谬来证明当前的目标。 *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev)  *)
(** 在这个练习中找到适合进行归纳的对象可能有点困难： *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** 这里是一个只需要应用已经存在的引理的练习。不需要任何的归纳法或分类讨论，
    只是有些重写步骤会稍显冗长。 *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** * 讨论和变形*)
(** ** 计算性定义 vs. 归纳性定义*)

(** 我们已经能够看到“[n]是偶数”这一命题能够从两种方向解释——间接地通过一个
    布尔测试函数[evenb]定义，或者直接归纳性地解释什么可以组成能够证实偶数性
    的证据。这两种不同的定义偶数性的方式同样地容易阐述，也同样地容易讨论。
    因此在这里，选择哪种方式仅仅是个人选择。

    然而对于许多其他的我们关心的性质而言一般推荐使用直接的归纳定义，因为有
    时编写一个测试函数会十分困难，或者甚至不可能。

    [beautiful]就是这样的一种性质。它作为一个数集的定义是完全可被理解的，
    但是我们无法将其转换成一个Coq Fixpoint（或者转换成任何常见的编程语言里的
    一个递归函数）。我们也许能够找到某种取巧的使用Fixpoint的检测这种性质的
    方法（诚然，就这个例子而言，得出这样的方法并不困难），然而就一般而言，
    这会需要十分深刻的思考。事实上，假如我们所关心的性质是不可计算的，那么
    无论我们如何努力，我们都无法用[Fixpoint]定义它，因为Coq要求每一个
    [Fixpoint]都要对应某个将会停机的运算。

    另一方面，就为了定义如何给出能够证实持有[beautiful]这一性质的证据而言，
    直接写出一个归纳定义是十分直接的。 *)



(* ####################################################### *)
(** ** 参数化数据结构*)

(** 至今为止我们只是接触过有关自然数的命题，但是我们能够定义有关任意类型的
    数据的归纳谓词。比如说，假如我们想要将“具有 _（偶数）_ 长度的列表”特征化，我
    们能够通过下面的定义做到这一点： *)

Inductive ev_list {X:Type} : list X -> Prop :=
  | el_nil : ev_list []
  | el_cc  : forall x y l, ev_list l -> ev_list (x :: y :: l).

(** 当然这个命题与声明列表的长度为偶数等价。 *)

Lemma ev_list__ev_length: forall X (l : list X), ev_list l -> ev (length l).
Proof. 
    intros X l H. induction H.
    - (* el_nil *) simpl. apply ev_0.
    - (* el_cc *)  simpl.  apply ev_SS. apply IHev_list.
Qed.

(** 然而由于[ev]的证据包含的信息比[ev_list]的证据所包含的更少，在证明另一个方
    向的时候必须十分小心。 *)

Lemma ev_length__ev_list: forall X n, ev n -> forall (l : list X), n = length l -> ev_list l.
Proof.
  intros X n H. 
  induction H.
  - (* ev_0 *) intros l H. destruct l.
    + (* [] *) apply el_nil. 
    + (* x::l *) inversion H.
  - (* ev_SS *) intros l H2. destruct l as [| x [| x0 l]]. 
    + (* [] *) inversion H2. 
    + (* [x] *) inversion H2.
    + (* x :: x0 :: l *) apply el_cc. apply IHev. inversion H2. reflexivity.
Qed.
    

(** **** Exercise: 4 stars (palindromes)  *)
(** 回文指的是一种从反方向读的结果与从正方向读相同的序列。
    - 定义一个关于[list X]的能够说明什么是一段回文的归纳命题[pal]。

      （提示：你会需要分三种情况。你的定义应该基于列表的结构。

        只用一个构造子：
        c : forall l, l = rev l -> pal l
        看上去或许能够明显地解决这个问题，但是这并不能很好地工作。）

    - 证明[pal_app_rev]：
       forall l, pal (l ++ rev l).
    - 证明[pal_rev]：
       forall l, pal l -> l = rev l.
*)

(* FILL IN HERE *)
(** [] *)

(* 由于缺乏证据，相反方向的证再一次地变得更加困难了。  *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** 使用在之前的练习中你给出的[pal]的定义进行证明： 
     forall l, l = rev l -> pal l.
*)

(* FILL IN HERE *)
(** [] *)



(* ####################################################### *)
(** ** 关系 *)

(** 
    一个附带了一个数字作为其参数的命题（比如[ev]或者[beautiful]）能够被看作是
    一种 _（性质）_ ——它定义了一个[nat]的子集，这个子集中包含了所有能够被证明拥有
    这一性质的数字。同样地，一个有两个参数的命题能够被看作是一种 _（关系）_ ——
    它定义了一个包含所有能够被证明存在这一关系的序对的集合。 *)

Module LeModule.  


(** 其中一个十分有用的例子是数字之间的“小于等于”的关系。 *)

(** 以下的定义应该足够符合直觉。它说明存在两种给出证实某个数字小于或等于另
    外一个数字的证据的方式：声明它们相等，或者声明其中一个数字小于或等于另
    外一个数字的前继。 *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** 
    使用构造子[le_n]和[le_S]证明关于[<=]的事实的方法和证明与性质（比如说[Prop]一章
    中的[ev]）相关的事实的方法相同。我们可以对构造子使用[apply]以证明包含[<=]的
    目标（举例而言，证明[3<=3]或者[3<=6]），也可以使用像[inversion]之类的证明策略
    来从存在于上下文中的包含[<=]的前提提取出信息（如证明[(2 <= 1) -> 2 + 2 = 5]）。  *)

(** *** *)
(** 
    这里有一些针对这个定义的正常性检查。（注意，即使这些与在之前的课程中为
    了测试我们写的函数而写的简单的“单元测试”是同一种事情，我们也必须构造出
    明晰的证明——[simpl]和[reflexivity]并不会完成这一工作，因为证明并不是只需
    通过简化就能完成的计算。） *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** *** *)
(** 现在“小于”关系（[n < m]）能够借助[le]进行定义了。 *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** 这里有一些简单的数字之间的关系： *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation)  *)
(** 定义一个每一对自然数之间都具有的归纳二元关系[total_relation]。*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars (empty_relation)  *)
(** 定义一个不可能被具有的关于数字的归纳二元关系[empty_relation]。*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises)  *)
(** 这里有一些在后来的课程中所需要的关于[<=]和[<]的事实。

    试着证明它们，这将会是很好的练习。 *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  (* FILL IN HERE *) Admitted.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt. 
 (* FILL IN HERE *) Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  (* 提示：对[m]使用归纳法可能是证明这一事实的最容易的方法。*)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  (* 提示：这个定理的证明，不使用[induction]就能轻易地完成。 *)
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, optional (ble_nat_false)  *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 3 stars (R_provability2)  *)
Module R.
(** 我们能够像定义二元关系一样定义三元关系或四元关系等等，例如下面的关于数
    字的三元关系： *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - 下面的命题中哪一个是可被证明的？
      - [R 1 1 2]
      - [R 2 2 6]

    - 如果我们从[R]的定义中去掉了构造子[c5]，定义所描述的可证明的命题的集合
      改变了吗？用一句话给出你的答案。

    - 如果我们去掉构造子[c4]，定义所描述的可证明的命题的集合改变了吗？
      用一句话给出你的答案。

(* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact)  *)  
(** 实际上关系[R]定义了一个熟悉的函数。声明并证明这两个连接这一关系和所定义
    的函数的定理。也即是说，如果[R m n o]为真，那么我们能够声称[m]，[n]和[o]
    之间存在着什么样的关系？以及如果[m]，[n]和[o]存在这一关系，那么我们是否
    能够证明[R m n o]？
*)

(* FILL IN HERE *)
(** [] *)

End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** 如果一个列表中的所有元素在另一个列表中按照相同的顺序（其中可能插有其他
    元素）出现，那么这个列表是另一个列表的 _（子序列）_ 。例如：
    [1;2;3]
    是以下列表的子序列：
    [1;2;3]
    [1;1;1;2;2;3]
    [1;2;7;3]
    [5;6;1;9;9;2;7;3;8]
    而 _（不是）_ 以下任何一个列表的子序列：
    [1;2]
    [1;3]
    [5;6;2;1;7;3;8]

    - 定义一个关于[list nat]的能够准确描述什么是子序列的归纳命题[subseq]。
      （提示：你需要分三种不同的情况。）
    - 证明[subseq_refl]：子序列这一关系具有自反性，即证明任意一个列表都是
      自身的子序列。
    - 证明[subseq_app]：对于任意列表[l1]，[l2]和[l3]，如果[l1]是[l2]的一个子序列，
      那么[l1]是[l2 ++ l3]的一个子序列。
    - （可选的，比较困难）证明[subseq_trans]：子序列这一关系具有传递性，
      即当[l1]是[l2]的一个子序列且[l2]是[l3]的一个子序列时，[l1]也是[l3]的一
      个子序
      列。提示：小心地选择你进行归纳的对象！
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability)  *)
(** 假设我们向Coq给出下面的定义：
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    那么下述命题中哪些是可证实的？

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]
*)

(** [] *)


(* ##################################################### *)
(** * 使用命题进行编程 *)

(** 与我们已经看到的一样， _（命题）_ ，例如“二加二等于四”，是一种表达了对某个事
          实的某种宣称的语句。在Coq中，命题用类型为[Prop]的表达式表示。*)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** 可证的宣称与不可证的宣称都是完全合法的命题； _（是不是）_ 一个命题是一回事，
    而 _（是否可证）_ 则又是另外一回事了。*)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** [2 + 2 = 4]与[2 + 2 = 5]都是合法的类型为[Prop]的表达式。 *)

(** *** *)
(** 至今为止我们主要在Coq中命题能够出现的其中一种地方看到它们：在
    [Theorem]（以及[Lemma]和[Example]）定义中。 *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** 但是它们也有许多其他的使用方式。比如说，我们已经知道我们可以像给其他类
    型的表达式赋予名字一样用[Definition]来给某个命题赋予一个名字。 *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** 在这之后我们能够在任何需要一个命题的地方使用这个名字，例如在一个[Theorem]定义中： *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** 我们已经知道构造命题的几种不同的方式：

       - 我们能够通过[Inductive]定义一个新的命题

       - 给定两个相同类型的表达式[e1]和[e2]，我们能够构造命题[e1 = e2]；这宣称它
         们的值相等。

       - 我们能够通过蕴含和量化来组合命题。 *)
(** *** *)
(** 我们也已经看到类似于[even]和[beautiful]的 _（参数化命题）_ 。 *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** [even]的类型，也即是[nat -> Prop]，可以从三种等价的角度解读：

              (1) “[even]是一个从数字映射到命题的 _（函数）_ 。”

              (2) “[even]是一个与自然数[n]一一对应的命题的集合。”

              (3) “[even]是一个有关数字的 _（性质）_ 。”  *)

(** 在Coq中，命题——包括参数化的命题——是一等公民。举例而言，我们能够定
    义从数字映射至命题的函数…… *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ……然后将它们部分应用： *)

Definition teen : nat->Prop := between 13 19.

(** 我们甚至能够传递命题——包括参数化的命题——作为函数的参数： *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** 这里有两个以参数化命题作为参数传递给函数的例子。

    第一个函数[true_for_all_numbers]取一个命题[P]作为其参数，然后构建宣称[P]对于
    所有自然数都成立的命题。 *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** 第二个函数[preserved_by_S]会在取命题[P]作为参数后构建这样一种命题：它宣称
    如果[P]对于某个自然数[n']为真，那么它对于[n']的后继也为真——也即是说[P] _（通过
    后继被保持）_ ： *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** 最后，我们可以将这些成分组合起来定义自然数的归纳规则： *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercise: 3 stars (combine_odd_even)  *)
(** 完成下面函数[combine_odd_even]的定义。它取两个有关数字的性质[Podd]和[Peven]，
    而它应该返回一个在[n]为奇数时等价于[Peven n]，在[n]为偶数时等价于[Podd n]
的命题[P]。 *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.

(** 看看你是否能够证明下述的事实以测试你的定义： *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ##################################################### *)
(** 这里有一个给热衷冒险的人准备的额外挑战：如果我们可以使用[Definition]定义
    参数化命题，那么我们是否可以用[Fixpoint]定义它们？当然可以！然而这种“递
    归参数化”并不与我们非常熟悉的日常的数学的任何一部分相对应。下面的练习
    给出了一个稍微有些不自然的例子。 *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere)  *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)

(* 
Fixpoint true_upto_n__true_everywhere
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.
*)
(** [] *)

(** $Date$ *)


