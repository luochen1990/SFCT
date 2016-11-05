(** * 基础知识: Coq 中的函数式编程 *)

(* 提醒:

          ##############################
          ###  请勿公开发布习题解答  ###
          ##############################

   （原因见 [Preface]。）

*)

(*
   [Admitted] 是 Coq 的“应急出口”，就是说接受一个定义而暂不证明。
   我们用它来代表学习过程中挖下的“坑”，你需要通过作业练习来填坑。
   当你在实践中逐渐完成一些大型证明时， [Admitted] 也非常有用。 *)
Definition admit {T: Type} : T.  Admitted.

(* ###################################################################### *)
(** * 简介 *)

(** 函数式编程风格让编程更接近简单的、日常的数学：若一个过程或方法没有副作用，
    那么在忽略效率的情况下，我们需要理解的一切便只剩下如何将输入对应到输出了
    —— 或者说，我们只需将它视作一个计算数学函数的具体的方法即可。这也是
    “函数式编程”中“函数式”一词的含义之一。程序与简单数学对象之间的这种联系，
    同时支撑了对程序行为进行形式化证明的正确性以及非形式化论证的健全性。

    函数式编程中“函数式”一词的另一个含义是它强调把函数（或方法）作为_第一等_
    的值 —— 换言之，这类值可以作为参数传递给其它函数，可以作为结果返回，
    也可以包含在数据结构中等等。这种将函数视作数据来接受的方式，
    使很多有用而强大的惯用法成为可能。

    其它一些常见的函数式语言特性包括_代数数据类型（Algebraic Data Type）_，
    能让构造和处理丰富数据结构更加简单的_模式匹配（Pattern Matching）_，
    以及用来支持抽象和代码复用的复杂的_多态类型系统（Polymorphic Type System）_。
    Coq 提供所有的这些特性。

    本章的前半部分介绍了 Coq 函数式编程语言中最基本的元素，
    后半部分则介绍了可被用于证明 Coq 程序的简单属性的一些基本_策略_。 *)

(* ###################################################################### *)
(** * 可枚举类型 *)

(** Coq 一个不寻常的地方就是它内置了_极小_的特性集合。比如，Coq 并未提供
    通常的原子数据类型（如布尔值、整数、字符串等等），而是提供了一种极为强大的，
    可从头定义新数据类型的机制 —— 强大到所有常见的类型都是它定义产生出的实例。

    当然，Coq 发行版同时也提供了一个内容丰富的标准库，其中定义了布尔值、数值，
    以及如列表、散列表等很多通用的数据结构。不过这些库中的定义并没有
    任何神秘的或原语中自有的地方：它们都是普普通通的用户代码。为了说明这一点，
    我们并未隐式地使用库中的数据类型，而是在整个教程中显式地重新定义了它们。

    让我们从一个非常简单的例子开始，看看这种定义机制是如何工作的。 *)

(* ###################################################################### *)
(** ** 一周里的日子 *)

(** 下面的声明告诉 Coq 我们在定义一个新的数值集合，即一个_类型_。 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

(** 该类型名为 [day], 其成员包括 [monday]、[tuesday] 等等。第二行及之后的定义可读作
    “[monday] 是一个 [day]”，“[tuesday] 是一个 [day]”，以此类推。

    在定义了 [day] 之后, 我们就可以写一些操作 day 的函数了。 *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** 注意，这里显式声明了函数的参数和返回值。像大多数函数式编程语言一样，
    如果没有显式指定类型，Coq 自己通常会通过_类型推断_得出。
    不过我们会在这里声明它们，以使其更加易读。 *)

(** 定义完函数之后，我们用一些例子来检验它。实际上，在 Coq 中可以用三种
    不同的方式进行检验。

    第一，我们可以用命令 [Compute] 来计算一个包含 [next_weekday] 的合成表达式。 *)

Compute (next_weekday friday).
   (* ==> monday : day *)
Compute (next_weekday (next_weekday saturday)).
   (* ==> tuesday : day *)

(** 我们在注释中显示了 Coq 返回的结果。不过若你手头就有电脑，不妨自己用 Coq
    解释器试一试：选一个你喜欢的 IDE（CoqIde 或 Proof General 都可以），然后
    从本书附带的 Coq 源码中载入 [Basics.v] 文件，找到上述例子，提交到 Coq，
    然后查看结果。 *)

(** 第二，我们可以用 Coq 例子的形式来记录期望的结果： *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** 该声明做了两件事：一是它作出了一个断言（即 [saturday] 之后的第二个工作日是
    [tuesday]）；二是它为该断言起名以便之后引用它。

    定义好断言后，我们还能要求 Coq 来验证它，像这样： *)

Proof. simpl. reflexivity.  Qed.

(** 一些细节问题我们暂且不谈（之后还会讲到），不过这段代码基本上可以读作
    “经过一番化简后，若等式两边的求值结果相同，该断言即可得证。” *)

(** 第三，我们可以让 Coq 从 [Definition] 中_提炼出_一个用更常规的编程语言
    （如 OCaml、Scheme、Haskell）编写的程序，它们有着高性能的编译器。
    这种能力非常有用，我们可以通过它来用主流的语言构造出经过_充分验证_的程序。
    实际上，这也是 Coq 被开发出来后最主要的使用方式之一。
    在之后的章节中我们会回到这一主题上来。 *)

(* ###################################################################### *)
(** ** 布尔值 *)

(** 用类似的方式，我们可以为布尔值定义标准类型 [bool]，它包括
    [true] 和 [false] 两个成员。 *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

(** 当然，Coq 的标准库中提供了布尔类型的默认实现以及大量有用的函数和定理。
    （有兴趣的话可参见 Coq 库文档中的 [Coq.Init.Datatypes]。）
    不过我们为了从头开始，定义了自己的布尔类型。
    我们会尽量将自己的定义和定理的名字与标准库中的保持完全一致。 *)

(** 布尔值的函数可以用同样的方式来定义： *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(** 其中后面两个演示了多参数函数定义的语法。
    以下四个“单元测试”则演示了多参数应用的语法，
    它们构成了 [orb] 函数的完整规范，即真值表： *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.

(** 我们也可以为刚定义的布尔运算引入更熟悉的语法。
    [Infix] 命令能为既有的定义来定义出新的中缀记法。 *)

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** _关于记法的说明_ ：在 [.v] 文件中，我们用方括号来界定注释中的 Coq 代码片段；
    这种约定也在 [coqdoc] 文档工具中使用，它能让代码与周围的文本从视觉上区分开来。
    在 HTML 版的文件中，这部分文本会以 [不同的字体] 显示。 *)

(** 特殊的短语 [Admitted] 和 [admit] 被用作不完整定义或证明的占位符，
    我们会在后续的例子中用它。通常，你的练习作业就是将 [Admitted] 和 [admit]
    替换为具体的定义和证明。 *)

(** **** 练习：1 星级（nandb） *)
(** 移除 [admit] 并补完以下函数的定义，然后确保下列每一个 [Example]
    中的断言都能被 Coq 验证通过。（仿照前面 [orb] 测试的模式，移除每一个
    [Admitted.] 并补充证明。） *)

(** 此函数应在两个输入之一或二者均为 [false] 时返回 [true] 。 *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  (* 请补充 *) admit.

Example test_nandb1:               (nandb true false) = true.
(* 请补充 *) Admitted.
Example test_nandb2:               (nandb false false) = true.
(* 请补充 *) Admitted.
Example test_nandb3:               (nandb false true) = true.
(* 请补充 *) Admitted.
Example test_nandb4:               (nandb true true) = false.
(* 请补充 *) Admitted.
(** [] *)

(** **** 练习: 1 星级（andb3） *)
(** 与此前相同，完成下面的 [andb3] 函数。
    此函数应在其所有输入均为 [true] 时返回 [true]，否则返回 [false]。 *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* 请补充 *) admit.

Example test_andb31:                 (andb3 true true true) = true.
(* 请补充 *) Admitted.
Example test_andb32:                 (andb3 false true true) = false.
(* 请补充 *) Admitted.
Example test_andb33:                 (andb3 true false true) = false.
(* 请补充 *) Admitted.
Example test_andb34:                 (andb3 true true false) = false.
(* 请补充 *) Admitted.
(** [] *)

(* ###################################################################### *)
(** ** 函数类型 *)

(** Coq 中的每个表达式都有类型，它描述了该表达式所计算的东西的类别。
    [Check] 命令让 Coq 显示一个表达式的类型。 *)

(** 例如，[negb true] 的类型为 [bool]。 *)

Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)

(** 像 [negb] 这样的函数其本身也是数据值，就像 [true] 和 [false] 一样。
    它们的类型被称为_函数类型_，用带箭头的类型表示。 *)

Check negb.
(* ===> negb : bool -> bool *)

(** [negb] 的类型写作 [bool -> bool]，读做“[bool] 箭头 [bool]”，
    可以理解为“给定一个 [bool] 类型的输入，该函数产生一个 [bool] 类型的输出。”
    同样，[andb] 的类型写作 [bool -> bool -> bool]，可以理解为
    “给定两个输入，都是 [bool] 类型，该函数产生一个 [bool] 类型的输出。” *)

(* ###################################################################### *)
(** ** 模块 *)

(** Coq 提供了_模块系统_来帮助组织大规模的开发。在本课程中，
    我们不怎么会用到这方面的特性，不过其中有一样非常有用：
    如果我们将一组定义放在 [Module X] 和 [End X] 标记之间，那么在文件中的
    [End] 之后，我们就可以通过像 [X.foo] 这样的名字来引用，而不必直接用
    [foo] 了。在这里，我们通过此特性在一个内部模块中引入了 [nat] 类型的定义，
    这样就不会覆盖标准库中的同名定义了，毕竟它用了点儿特别的记法技巧。 *)

Module Playground1.

(* ###################################################################### *)
(** ** 数 *)

(** 至此，我们所定义的所有类型都是“可枚举类型”：
    这些定义都是显式地列举出一个有限集合中的元素。定义类型的一种更有趣的方式是
    通过一组“归纳性规则”来描述其元素。比如，我们可以对自然数作如下定义：*)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** 此定义中的句子可以看做：
      - [O] 是一个自然数（注意这里是字母“[O]”，不是数字“[0]”）。
      - [S] 是一个构造器，取一个自然数并生成另一个 —— 也就是说，
        如果 [n] 是一个自然数，那么 [S n] 也是。

    让我们来更仔细地看一下这个定义。

    所有可归纳式定义的集合（[day]、[nat]、[bool] 等）实际上都是_表达式_的集合。
    [nat] 的定义说明了集合 [nat] 中的表达式是如何构造的。

    - 表达式 [O] 属于集合 [nat]；
    - 如果 [n] 是属于集合 [nat] 的表达式，
      那么 [S n] 也是属于集合 [nat] 的表达式；并且
    - 只有这两种方式形成的表达式才属于集合 [nat]。

    同样的规则也适用于 [day] 和 [bool] 的定义。对于它们的构造器我们使用的标记
    形式类似于 [O] 构造器，表示这些构造器都不接收任何参数。 *)

(** 以上三个条件是形成 [归纳式] 声明的主要推动力。它们隐含了表达式 [O]、
    [S O]、[S (S O)]、[ S (S (S O))] 等等都属于集合 [nat]，而像
    [true]、[andb true false]、[S (S false)] 之类的表达式则不属于 [nat]。

    我们可以编写简单的函数对如上所述的自然数进行模式匹配 —— 比如，前趋函数：*)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** 第二个分支可以看做：“如果 [n] 对于某个 [n'] 有 [S n'] 的形式，
    那么返回 [n']。” *)

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** 由于自然数这种数据形式无处不在，因此 Coq 在解析和输出它们时用了点内建的小魔术：
    普通的阿拉伯数字可看做 [S] 和 [O] 构造器定义的“一进制”自然数的另一种记法，
    Coq 默认也会将自然数输出为阿拉伯数字的形式。 *)

Check (S (S (S (S O)))).
Compute (minustwo 4).

(** 构造器 [S] 具有类型 [nat -> nat]，与函数 [minustwo] 和 [pred] 相同： *)

Check S.
Check pred.
Check minustwo.

(** 以上这些都是作用于一个数上产生另一个数的，不过它们之间有个重要区别：
    像 [pred] 和 [minustwo] 这样的函数带有 _计算规则_ —— 也就是说，
    [pred] 的定义表明 [pred 2] 可被化简为 [1] —— 然而 [S] 的定义却没有
    附带这种计算行为。尽管它感觉像是个可以作用在一个参数上的函数，
    但却完全没有 _执行_ 任何计算。 *)

(** 对于定义在数上的大部分函数来说，只有模式匹配是不够的：我们还需要递归。
    比如，想要判断一个数 [n] 是否为偶数，我们需要递归地判断 [n-2] 是否为偶数。
    为了写出这样的函数，我们可以使用关键字 [Fixpoint]。 *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** 我们可以使用类似的 [Fixpoint] 声明来定义 [odd] 函数，不过还有个更简单的
    定义能让我们做起来更容易：*)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    (oddb (S O)) = true.
Proof. simpl. reflexivity.  Qed.
Example test_oddb2:    (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity.  Qed.

(** （如果你逐步检查完这些证明，就会发现 [simpl] 其实没有效果 —— 所有工作都被
    [reflexivity] 完成了。我们不久就会更多地了解到为什么会这样。)

    当然，我们也可以用递归定义多参函数。 *)

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** 三加二得五，正如所料。 *)

Compute (plus 3 2).

(** 为得出此结论，Coq 所执行的化简步骤如下所示：*)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))] 使用第二个 [match] 子句
==> [S (S (plus (S O) (S (S O))))] 使用第二个 [match] 子句
==> [S (S (S (plus O (S (S O)))))] 使用第二个 [match] 子句
==> [S (S (S (S (S O))))]          使用第一个 [match] 子句
*)

(** 为了书写方便，如果两个或更多参数具有相同的类型，那么它们可以写在一起。
    在下面的定义中，[(n m : nat)] 的意思与 [(n : nat) (m : nat)] 相同。 *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity.  Qed.

(** 你可以在两个表达式之间添加逗号来同时匹配它们：*)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

(** 第一行里的 _ 是一个 _通配符_。在模式匹配中使用 _ 就如同写一个变量但在
    匹配的右侧不使用它。这样可以避免声明无用的变量名。 *)

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(** **** 练习: 1 星级 (factorial)  *)
(** 回想一下标准的阶乘函数：
<<
    factorial(0)  =  1
    factorial(n)  =  n * factorial(n-1)     (if n>0)
>>
    把它翻译成 Coq 语言。 *)

Fixpoint factorial (n:nat) : nat :=
(* 请补充 *) admit.

Example test_factorial1:          (factorial 3) = 6.
(* 请补充 *) Admitted.
Example test_factorial2:          (factorial 5) = (mult 10 12).
(* 请补充 *) Admitted.
(** [] *)

(** 我们可以通过引入加法、乘法和减法的 _记法_ 来让数字表达式更易读一些。 *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).

(** （[level]、[associativity] 和 [nat_scope] 标记控制了 Coq 语法分析器如何处理
    上述记法。细节无关紧要，有兴趣的读者可以参考本章末尾“进阶资料”部分中
    “关于记法的更多内容”一节。） *)

(** 注意，它们并不会改变我们之前的定义：只是让 Coq 语法分析器接受用 [x + y]
    来代替 [plus x y]， 并在 Coq 美化输出时反过来将 [plus x y] 显示为 [x + y]。 *)

(** 我们说 Coq 不包含任何内置定义时，实际上是指：
    Coq 甚至连数值的相等性测试都是用户定义的操作！*)

(** [beq_nat] 函数测试 [nat] 自然数的 [eq] 相等性，产生一个 [b] 布尔值。
    注意嵌套匹配 [match] 的使用（我们也可以使用同时匹配，与在 [minus]
    中的做法一样）。 *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** [leb] 函数测试其第一个参数是否小于或等于第二个参数，并返回一个布尔值。 *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1:             (leb 2 2) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb2:             (leb 2 4) = true.
Proof. simpl. reflexivity.  Qed.
Example test_leb3:             (leb 4 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** 练习: 2 星级 (blt_nat)  *)
(** [blt_nat] 函数测试 [nat] 自然数的 [lt] 小于性，并产生一个 [b] 布尔值。
    这次不必完全重新定义一个 [Fixpoint]，可以利用前面已经定义的函数来定义。 *)

Definition blt_nat (n m : nat) : bool :=
  (* 请补充 *) admit.

Example test_blt_nat1:             (blt_nat 2 2) = false.
(* 请补充 *) Admitted.
Example test_blt_nat2:             (blt_nat 2 4) = true.
(* 请补充 *) Admitted.
Example test_blt_nat3:             (blt_nat 4 2) = false.
(* 请补充 *) Admitted.
(** [] *)

(* ###################################################################### *)
(** * 基于化简的证明 *)

(** 至此，我们已经定义了一些数据类型和函数。让我们把问题转到如何表述和证明
    它们行为的特性上。 其实我们已经开始这样做了：前几节中的每个 [Example]
    都对几个函数在某些特定输入上的行为做出了准确的断言。对这些断言的证明都一样：
    使用 [simpl] 来化简等式两边，然后用 [reflexivity] 来检查两边是否具有相同的值。

    这类“基于化简的证明”还可以用来证明更多有趣的属性。例如，对于“ [0]
    出现在左边时是加法 [+] 的「幺元」”这一事实，我们只需读一遍 [plus] 的定义，
    即可通过观察“对于 [0 + n]，无论 [n] 值为多少都可化简为 [n]”而得到证明。 *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.  Qed.

(** （如果你同时浏览 [.v] 文件和 HTML 文件，那么大概会注意到以上语句在你的 IDE
    里和在浏览器渲染的 HTML 里不大一样，我们用保留标识符“forall”来表示全称量词
    [forall]。当 [.v] 文件转换为 HTML 后，它会变成一个倒立的“A”。） *)

(** 现在是时候提一下 [reflexivity] 了，它其实比我们所认为的更加强大。
    在前面的例子中，其实并不需要调用 [simpl] ，因为 [reflexivity]
    在检查等式两边是否相等时会自动做一些化简；加上 [simpl] 只是为了看到化简之后，
    证明结束之前的中间状态。下面是对同一定理更短的证明：*)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(** 此外，[reflexivity] 在某些方面做了比 [simpl] _更多_的化简 ——
    比如它会尝试「展开」已定义的项，将它们替换为该定义右侧的值，
    了解这一点会对以后很有帮助。产生这种差别的原因是，当自反性成立时，
    整个证明目标就完成了，我们不必再关心 [reflexivity] 化简和展开了什么；
    而当我们必须去观察和理解新产生的证明目标时，我们并不希望它盲目地展开定义，
    将证明目标留在混乱的声明中。这种情况下就要用到 [simpl] 了。 *)

(** 我们刚刚声明的定理形式及其证明与前面的例子的基本相同，它们只有一点差别。

    首先，我们使用了关键字 [Theorem] 而非 [Example]。这种差别纯粹是风格问题；
    在 Coq 中，关键字 [Example] 和 [Theorem]（以及其它一些，包括 [Lemma]、[Fact]
    和 [Remark]）都表示完全一样的东西。

    其次，我们增加了量词 [forall n:nat]，因此我们的定理讨论了_所有的_自然数 [n]。
    为了证明这种形式的定理，我们需要_假定_存在一个任意自然数 [n]，
    以此为依据进行推理。在证明中，这是用 [intros n] 来实现的，
    它将量词从证明目标移动到当前假设的「上下文」中。达到的效果就是，
    我们说「OK，假设 [n] 是任意一个自然数」，然后我们开始证明。

    关键字 [intros]、[simpl] 和 [reflexivity] 都是_策略_的例子。
    策略是一条可以用在 [Proof]（证明）和 [Qed]（证毕）之间的命令，它告诉 Coq
    如何去检查我们所做的一些断言的正确性。在本章剩余的部分和未来的课程中
    我们会见到更多的策略。

    其它类似的定理可以用相同的模式进行证明。 *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

(** 上述定理名称的后缀 [_l] 读作"在左边"。 *)

(** 跟进这些证明的每个步骤，观察上下文及证明目标的变化是非常值得的。 *)
(** 你可能要在 [reflexivity] 前面增加 [simpl] 的调用，以观察 Coq
    在检查它们相等前做的一些化简。 *)

(** 尽管对于证明一些相当普遍的事实来说，化简已经非常强大了，
    但还有很多陈述无法仅用化简来处理。比如，当 [0] 出现在 [+]
    的_右侧_时，用化简就无法证明它是「幺元」。 *)

Theorem plus_n_O : forall n, n + 0 = n.
Proof.
  intros n. simpl. (* 不起作用！ *)

(** (你能解释这为什么这样么？在 Coq 里跟踪两个证明的每一步骤，
    注意观察证明目标和上下文的变化。)

    当在证明过程中卡住时，可以用 [Abort] 命令来暂时放弃证明。 *)

Abort.

(** 在下一章里，我们会用到一种技术来证明这个目标。 *)

(* ###################################################################### *)
(** * 基于改写的证明 *)

(** 下面是一个有趣的定理： *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** 该定理并未对自然数 [n] 和 [m] 所有可能的值做全称论断，而是讨论了仅当
    [n = m] 时这一更加特定情况。箭头符号读作「蕴含」。

    与此前相同，我们需要在能够假定存在自然数 [n] 和 [m] 的基础上进行推理。
    另外我们需要假定有前提 [n = m]。[intros] 策略用来将这三条假设从证明目标
    移动到当前上下文的假设中。

    由于 [n] 和 [m] 是任意自然数，我们无法用化简来证明此定理，不过可以通过
    观察来证明它。如果我们假设了 [n = m]，那么就可以将证明目标中的
    [n] 替换成 [m] 从而获得两边表达式相同的等式。用来告诉 Coq 执行这种替换的
    策略叫做改写 [rewrite]。 *)

Proof.
  (* 将两个量词移到上下文中 *)
  intros n m.
  (* 将前提移到上下文中 *)
  intros H.
  (* 用假设改写目标 *)
  rewrite -> H.
  reflexivity.  Qed.

(** 证明的第一行将全称量词变量 [n] 和 [m] 移动到上下文中。第二行将假设
    [n = m] 移动到上下文中，并将其（随意）命名为 [H]。第三行告诉 Coq
    改写当前目标（[n + n = m + m]），把前提等式 [H] 的左边替换成右边。

    ([rewrite] 里的箭头与蕴含无关：它指示 Coq 从左往右地应用改写。
    若要从右往左改写，可以使用 [rewrite <-]。在上面的证明里试一试这种改变，
    看看 Coq 的反应有何变化。) *)

(** **** 练习: 1 星级 (plus_id_exercise)  *)
(** 删除 "[Admitted.]" 并补充完整证明。 *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  (* 请补充 *) Admitted.
(** [] *)

(** [Admitted] 命令告诉 Coq 我们想要跳过此定理的证明而将其作为已知条件，
    这在开发较长的证明时很有用。在进行一些较大的命题论证时，我们能够声明一些附加的事实。
    既然我们认为这些事实是对论证有用的，就可以用 [Admitted] 先不加怀疑地接受这些事实，
    然后继续思考大命题的论证。直到确认了该命题确实是有意义的，
    再回过头去证明刚才跳过的证明。但是要小心：每次使用 [Admitted] 或者 [admit]，
    你就为进入 Coq 这个完好、严密、形式化且封闭的世界开了一个毫无道理的后门。 *)

(** 我们还可以使用 [rewrite] 策略来运用前期已证明过的定理，而不是上下文中的现有前提。
    如果前期证明的定理的语句中包含量词变量，如前例所示，Coq 会通过匹配当前证明目标
    来尝试实例化它们。 *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

(** **** 练习: 2 星级 (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  (* 请补充 *) Admitted.
(** [] *)


(* ###################################################################### *)
(** * 利用情况分析来证明 *)

(** 当然，并非一切都能通过简单的计算和重写来证明：通常，一些未知的，假定的值
    （如任意数值、布尔值、列表等等）会阻碍化简。比如，我们如果像以前一样使用
    [simpl] 策略尝试证明下面的事实，就会被卡住。 *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl.  (* 无能为力! *)
Abort.

(** 原因在于 [beq_nat] 和 [+] 的定义都是对它们的第一个参数进行 [match] 匹配的。
    但在这里，[+] 的第一个参数是未知数 [n]，而 [beq_nat] 的第一个参数是
    复合表达式 [n + 1]，二者都不能被化简。

    为了继续进行，我们需要分别考虑 [n] 所有可能的形式。如果 [n] 是 [0]，那么
    我们可以计算 [beq_nat (n + 1) 0] 的最终结果并验证，即 [false]。
    若对于某个 [n'] 有 [n = S n']，那么，尽管我们无法确切知道 [n + 1] 得到的数字，
    但仍然可以进行计算，至少它应该以 [S] 打头。这对于计算已经足够了。同样，
    [beq_nat (n + 1) 0] 会得到 [false]。

    告诉 Coq 根据情况 [n = 0] 和 [n = S n'] 来分开考虑的策略，叫做 [destruct]。 *)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity.  Qed.

(** [destruct] 会生成_两个_子目标，这两个目标我们需要分别进行证明，
    然后才能让 Coq 接受此定理是已证明的。记法 "[as [| n']]" 叫做
    _引入模式_，用来告诉 Coq 每个子目标中引入的变量名是什么。
    通常，在方括号内是一组_名字列表的列表_，中间用 [|] 分隔。在本例中，
    列表的第一个成员是空，因为 [0] 的构造器是零元的（不包含任何参数）。
    第二个成员给出了一个名字 [n']，是因为 [S] 是一元构造器。

    第二和第三行中的 [-] 符号叫做_标号_，标明了每个生成的子目标对应的证明部分。
    （译注：此处的「标号」应理解为一个项目列表中每个_条目_前的小标记，如‣或•。）
    标号后面的代码是一个子目标的完整证明。在本例中，每个子目标都简单地使用
    [reflexivity] 完成了证明，通常 [reflexivity] 本身会执行一些化简操作。
    比如，第一段证明将 [beq_nat (S n' + 1) 0] 化简成 [false]，是通过先将
    [(S n' + 1)] 转写成 [S (n' + 1)]，接着展开 [beq_nat]，之后再化简 [match] 完成的。

    用标号来标记区分情况完全是可选的：如果标号不存在，Coq 只会简单地要求你
    依次证明每个子目标。尽管如此，使用标号仍然是一个好习惯。原因有二：
    首先，它能让一个证明的结构更加清晰易读。其次，标号能指示 Coq
    在开始验证下一个目标前确认上一个子目标已完成，防止不同子目标的证明
    搅和在一起。这一点在大型开发中尤其重要，一些证明片段会导致很耗时的
    排错过程。

    在 Coq 中并没有既严格又便捷的规则来格式化证明 —— 尤其指应在哪里断行，
    以及证明中的段落应如何缩进以显示其嵌套结构。然而，无论格式的其它方面如何布局，
    只要在多个子目标生成的地方为每行开头标上标号，那么整个证明就会有很好的可读性。

    这里也有必要提一下关于每行代码长度的建议。Coq 的初学者有时爱走极端，
    要么一行只有一个策略语句，要么把整个证明都写在一行里。更好的风格则介于两者之间。
    一个合理的习惯是给自己设定一个每行 80 字符的限制。更长的行会很难读，
    也不便于显示或打印。很多编辑器都能帮你做到。

    [destruct] 策略可用于任何归纳定义的数据类型。比如，我们接下来会用它来证明
    布尔值的取反是对合的 —— 即，取反是自身的逆运算。 *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.  Qed.

(** 注意这里的 [destruct] 没有 [as] 子句，因为此处 [destruct]
    生成的子情况均无需绑定任何变量，因此也就不必指定名字。（当然，我们也可以写上
    [as [|]] 或者 [as []]。) 实际上，我们也可以省略_任何_ [destruct] 中的 [as] 子句，
    Coq 会自动填上变量名。不过这通常是个坏习惯，因为如果任其自由决定的话，
    Coq 经常会选择一些容易令人混淆的名字。

    有时在一个子目标内调用 [destruct]，产生出更多的证明义务（Proof Obligation）
    也非常有用。这时候，我们使用不同的标号来标记目标的不同「层级」，比如： *)

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(** 这里，每一对 [reflexivity] 调用对应于紧邻其上的 [destruct] 行执行后所生成的子目标。
    除了 [-] 和 [+]，Coq 证明还可以使用 [*] 作为第三种标号。如果我们遇到一个证明
    生成了超过三层的子目标，那么可以用花括号（[{ ... }]）将每个子目标括起来： *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** 由于花括号同时标识了证明的开始和结束，因此它们可以同时用在不同的子目标层级，
    如上例所示。进一步地，花括号允许我们在一个证明中的多个层级下使用同一个标号： *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
Qed.

(** 在本章结束之前，我们谈一下最后一个约定。或许你已经注意到了，
    很多证明在引入变量之后会立即对它进行情况分析：

       intros x y. destruct y as [|y].

    这种模式很常见，Coq 为此提供了一种简写：当使用引入模式而非变量名来引入标量时，
    我们可以直接对变量进行情况分析。例如，下面就是一个比前面更短的对 [plus_1_neq_0]
    定理的证明。 *)

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.  Qed.

(** 如果没有需要命名的参数我们只需写上 [[]] 即可。 *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** 练习: 2 星级 (andb_true_elim2)  *)
(** 证明以下论断, 当使用 [destruct] 时请用标号标出情况（及子情况）。 *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* 请补充 *) Admitted.
(** [] *)

(** **** 练习: 1 星级 (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* 请补充 *) Admitted.
(** [] *)

(* ###################################################################### *)
(** * 关于记法的更多内容 (可选) *)

(** （通常，标记为可选的部分对于跟进本书其它部分的学习来说不是必须的，
    除了那些也标记为可选的部分。在初次阅读时，你可以快速浏览这些部分，
    以便在将来遇到时能够想起来这里讲了些什么。）

    回忆一下中缀加法和乘法的记法定义：*)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(** 对于 Coq 中的每个记法符号，我们可以指定它的_优先级_和_结合性_。
    优先级 [n] 用 [at level n] 来表示，这将有助于 Coq 分析复合表达式。
    结合性的设置有助于消除有相同符号出现多次的表达式的歧义。比如，
    上面这组对 [+] 和 [*] 的参数定义的表达式 [1+2*3*4] 是 [(1+((2*3)*4))] 的
    简写。Coq 使用 0 到 100 的优先级等级，同时支持_左结合_、_右结合_和_不结合_
    三种结合性。之后我们会看到更多与此相关的例子，比如在 [列表] 一章。

    每个记法符号还与_记法范围（notation scope）_相关。Coq 会尝试根据上下文来猜测
    你所指的范围，因此当你写出 [S(0*0)] 时，它猜测是 [nat_scope]；而当你
    写出笛卡尔积（元组）类型 [bool*bool] 时，它猜测是 [type_scope]。
    有时你可能不得不用百分号记法写出 [(x*y)%nat] 来帮助 Coq 确定范围，
    另外，有时 Coq 对你的反馈中也包含 [%nat] 用来指示记法所在的范围。

    记法范围同样适用与数字表示（[3]、[4]、[5] 等等），因此你有时候会看到
    [0%nat]，表示 [0]（我们在本章中使用的自然数零 [0]），而 [0%Z] 表示整数零
    （来自于标准库中的另一个部分）。 *)

(** * 不动点 [Fixpoint] 以及结构化递归 (可选) *)

(** 以下是加法定义的一个副本： *)

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus' n' m)
  end.

(** 当 Coq 查看此定义时，它会意识到 [plus'] 是「在其第一个参数上递减」。
    这意味着我们在参数 [n] 上执行了_结构化递归_。换言之，我们仅对严格减小了的
    [n] 值进行递归调用。这隐含说明了对 [plus'] 的调用最终会停止。Coq 要求每个
    [Fixpoint] 定义中的某些参数必须是「递减的」。

    这项要求是 Coq 设计的根本特性之一：尤其是，它保证了能在 Coq 中定义的
    所有函数对于所有输入都能终止。然而，由于 Coq 的「递减分析」不是非常精致，
    因此有时必须用一点不同寻常的方式来编写函数。 *)

(** **** 练习: 2 星级, 可选做 (递减)  *)
(** 为了能对此有更具体的认识，找出一种方式写出有效的 [Fixpoint] 定义
    (比如有关数字的简单函数)，在各种的输入下应当_确实_能够终止，但是 Coq
    却受限于此而拒绝接受。 *)

(* 请补充 *)
(** [] *)

(* ###################################################################### *)
(** * 更多练习 *)

(** **** 练习: 2 星级 (boolean_functions)  *)
(** 用你已经学过的策略证明以下关于布尔函数的定理。 *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  (* 请补充 *) Admitted.

(** 现在声明并证明定理 [negation_fn_applied_twice]，与上一个类似，但是
    第二个假设是说函数 [f] 有 [f x = negb x] 的性质。 *)

(* 请补充 *)
(** [] *)

(** **** 练习: 2 星级 (andb_eq_orb)  *)
(** 证明下列定理。（你有可能需要先证明一到两个辅助引理。或者，你要记住
    并非要同时引入所有假设。） *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  (* 请补充 *) Admitted.
(** [] *)

(** **** 练习: 3 星级 (binary)  *)
(** 设想一种不同的、更有效的表示自然数的方法，使用二进制，而不是一进制。
    换言之，并非说每个自然数是零或者另一个自然数的后继，我们可以说每个
    自然数：

      - 要么是零，
      - 要么是一个二进制数的两倍，
      - 要么比一个二进制数的两倍还多一。

    (a) 首先，写出对应上述二进制数类型 [bin] 的归纳定义。

    (提示：回想一下 [nat] 的定义，

         Inductive nat : Type :=
           | O : nat
           | S : nat -> nat.

    它并没有说出 [O] 和 [S] 的「含义」。它只是说「[O] 是在被称之为 [nat] 的集合中，
    而且，如果 [n] 在集合中那么 [S n] 也在集合中。」把 [O] 解释为零以及把 [S]
    定义为后继或者加一运算，是因为我们按这种方式去「使用」了 [nat] 的值而已。
    我们写出函数来计算它们，证明与之相关的东西，等等。你的 [bin] 的定义
    应该相对简单，下一步你写出的函数才会给出它的数学含义。)

    (b) 进一步地，为二进制数写出自增函数 [incr]，并且写出函数 [bin_to_nat]
        来将二进制数转换成一进制数。

    (c) 针对你写出的自增函数和二进制-一进制转换函数，写5个单元测试，
        如 [test_bin_incr1], [test_bin_incr2], 等等。注意，将一个二进制数
        先自增再转换为一进制数，应该与将其先转换成一进制后再自增获得的结果相同。
*)

(* 请补充 *)
(** [] *)

(** $Date: 2016-05-26 16:17:19 -0400 (Thu, 26 May 2016) $ *)
