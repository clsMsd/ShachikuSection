# 早期リターンの是非とエラーハンドリングについての議論

## 早期リターン(early return)とは?
```c
if (cond) {
  do_something1();
  do_something2();
  do_something3();
  /* ... */
  
  return result;
} else {
  return error;
}  
```
このような意味のコードを
```c
if (!cond) {
  return error;
}

do_something1();
do_something2();
do_something3();
/* ... */
  
return result;
```
このように書き方にするコーディングスタイルのこと。
関数の始めの方にreturn文を書くので早期リターンと呼ばれる。
return文の代わりに例外をスローすることもある。

## 早期リターンについての意見

自分がtwitter、qiitaのコメント欄、stackoverflowなどの書き込みから独自に意見調査した結果、早期リターンについての賛成派・反対派の意見をまとめると次のようになる

### 賛成派
- コードのネストが減るので可読性が上がる

### 反対派
- リソースの開放など、returnの前に行う処理がある場合に困る
- gotoと同じなので良くない
- 循環的複雑度が増えるので良くない
- ガード節が必要な時点で関数としておかしい(事前条件は呼び出し側が守る)
- 異常値のチェックはassert/requireを使うべし
- try-catchと正常系/異常系の順番が逆なので良くない
- パターンマッチの方がよい
- 型推論と相性が悪い
- そもそもreturn を書きたくない

## エラーとは何か？

関数が正しく実行されるということは、

1. 事前条件が満たされた状態で関数が呼び出され
2. 関数の実行後に事後条件が満たされている

ということ。
例えば、数値の足し算を行うについて考える
```python
def add(x, y):
   return x + y
```
この場合、事前条件は「xとyが数値であること」、事後条件は「戻り値がx + yであること」である。

このような視点で考えると、エラーというものは2種類に大別できる。

1. 事前条件が満たされない場合のエラー(以下では事前条件エラーと呼ぶ)
2. 事前条件が満たされたが事後条件が満たせない場合のエラー(以下では事後条件エラーと呼ぶ)

## 契約による設計と防御的プログラミング

上記の2種類のエラーに対して、どのように対処するのが適切だろうか？
ここでエラーの対処について2種類の考え方を紹介する。

### 契約的プログラミング
関数呼び出しを「呼び出し側が事前条件を守るならば、実装側は事後条件を守ります」という関数の実装側と呼び出し側の間での「契約」とする考え方。
まず前提として、実装側は関数毎に呼び出しの事前条件をコメント等に明記する。呼び出し側が事前条件を守らない関数呼び出しを行った場合は何が起ころうが構わないものとする。
関数は事前条件を守らない呼び出しが行われた場合、間違ったデータを返そうが、例外を生じさせようが、いきなりクラッシュしようが、コンピュータを爆発させようが構わない。
事前条件を守らない呼び出しはプログラムのバグであり、そのような関数呼び出しが無くなるように呼び出す側のコードを修正する必要がある。
実際には、開発時はデバッグを容易にするため`assert`等を使い事前条件を守らない関数呼び出しの際にプログラムをクラッシュさせる。リリース時は`assert`を取り除く。

### 防御的プログラミング
プログラムにバグは付き物であり、プログラムのすべての状態について事前条件を破った関数呼び出しが行われていないかテストすることは実質的に不可能である。また場合によっては事前条件を破った関数呼び出しが深刻な脆弱性を引き起こすこともある。
そこで、すべての関数について事前条件が守られているかどうか実行時にもチェックを行い、事前条件が守られない関数呼び出しに対しては適切なエラーハンドリングをおこなうべきであるという考え方があり、そのような考え方を防御的プログラミングという。
利点としては、プログラムが堅牢になるという点が挙げられる。欠点として、コードが非常に冗長になってしまうという点が挙げられる。例えば関数Aが関数B・関数C・関数Dを呼び出す次のようなコードがあったとする。
```python
def funcA(arg):
  # doSomething
  resultB = funcB(arg)
  resultC = funcC(arg)
  resultD = funcD(arg)
  # doSomething
  return result
  
def funcB(arg):
  # doSomething
  return result

def funcC(arg):
  # doSomething
  return result
  
def funcD(arg):
  # doSomething
  return result
```
ここで各関数の事前条件に「引数がnull(pythonではNone)でない」があった場合、防御的プログラミングに基づくコードは次のようになる。
```python
def funcA(arg):
  if arg is None:
    raise Exception
  # doSomething
  resultB = funcB(arg)
  resultC = funcC(arg)
  resultD = funcD(arg)
  # doSomething
  return result
  
def funcB(arg):
  if arg is None:
    raise Exception
  # doSomething
  return result

def funcC(arg):
  if arg is None:
    raise Exception
  # doSomething
  return result
  
def funcD(arg):
  if arg is None:
    raise Exception
  # doSomething
  return result
```
これは単にコードの可読性が低下するだけでなく、実行時の速度低下という弊害も生じさせる。

### 現実的な解決策

#### 静的な型チェック
静的型付け言語が行うコンパイル時の型チェックは、関数呼び出しが事前条件(の一部)を満たしているかどうかを引数の型により調べているといえる。
コンパイルが通るということは、それだけでプログラムがいかなる状態になりどのようなコードパスを通ろうとも、不正な型の引数による関数呼び出しが100%起こらないということをコンパイラが保証してくれるということであり、事前条件のチェックの仕組みとしては最良の方法である。
しかし、型によるチェックだけでは関数の事前条件のうちのごく一部が満たされているかを調べることしかできないケースがほとんどである。例えば、intに変換可能な文字列・100より小さい自然数・JSON形式の文字列… といった複雑な引数の事前条件を型によって表現することは普通の言語では不可能である。

#### カプセル化
適切にカプセル化を施すことで事前条件のチェックを少なくすることができる。上の例では、`funcB``funcC``funcD`が`funcA`以外から呼び出されることが無いならば、それらの関数をモジュール内のプライベートな関数とすれば引数のnullチェックは省略できる。

## 再び早期リターンについて考える

以上の考察から、一般に関数を実行する際の処理の流れは次のようになるといえる。
0. (関数が呼び出される)
1. 事前条件が満たされているかのチェック
2. メインの処理の実行
3. 事後条件が満たされているかのチェック
4. (戻り値を返して関数が終了する)

つまり、原理的にエラーのチェックは事前条件と事後条件で2箇所に存在することがわかる。
早期リターンと`try..catch`文で正常系、異常系の処理が逆になるのは、早期リターンは主に事前条件のチェックのために行われ、例外処理は事後条件のチェック(と事後条件エラーのエラーハンドリング)のために行われるからである。
そのように考えると、早期リターンと`try..catch`文の関係が逆になっているのはむしろ自然なことと言える。
また、早期リターンを「処理が不必要と分かった時点でその後処理を打ち切る」という広い意味で捉えると、HaskellのMaybeモナドやRustのtry!マクロなどは構文としては早期リターンではないがやっていることは早期リターンそのものである。

## 呼び出し元にエラーを通知する方法

関数の実行時にエラーが発生した場合、それを関数の呼び出し元に通知する方法には大きく分けて例外を使う方法と戻り値を使う方法の2種類がある。

### 例外を使う
エラーハンドリングに例外を使う利点は、プログラムが誤った状態のまま処理を進行させるのを防ぐことができるという点である。
例外を使う欠点は、制御フローが分かりにくくなる、意図しない例外までcatchしてしまう、マルチスレッドの処理と相性が悪い、例外処理自体が重い処理である、等がある。
例外はその名前の通り本当に例外的な状況にのみ使用し、準正常系の処理には例外を使ってはならないという意見もある。

#### 例外の落とし穴
標準入力から整数を受け取ってその階乗を表示するという簡単なプログラムを考える。
入力として負の整数を受け取った場合は正の整数を入力するように画面にメッセージを表示して再度入力を求めるようにする。

```python
def print_factorial():
   while True:
      n = int(input())
      try:
         result = factorial(n)
         print(result)
         return
      except:
         print("Please input positive integer")

def factrial(n):
   if n < 0:
      raise Exception("Invalid input: input number must be positive")
   if n == 0:
      return 1
   else:
      return n * fact(n - 1)
```

例外を使う場合は
- 適切な例外クラスをスローする(基底の例外クラスをそのままスローするようなことは避ける)
- try...catchで囲む範囲は最小限にする
- catchする例外の種類は最小限にする

べきである。

### 戻り値を使う
エラーハンドリングに戻り値を使う利点は例外の欠点の逆で、制御フローが分かりやすくなる、意図しないエラーをcatchしてしまうことが無い、マルチスレッドの処理と相性が良い、戻り値を見るだけなので処理が軽い、等がある。
欠点も例外の利点の逆で、エラーを無視することが容易になってしまうのでプログラムが誤った状態のまま処理が進行してしまうおそれがあるという点がある。
ただし、言語によっては関数の戻り値を無視するとコンパイルエラーになるというものもあるので、そのような言語は戻り値を使ったエラーハンドリングと相性が良いといえる(そもそもそのような言語では初めから戻り値を使ってエラーハンドリングを行うように設計されていて、例外機構を持たないということも多い)。

エラーハンドリングに戻り値を使う場合、関数の戻り値として次のようなものがよく使われる。
1. nullを返す
  基本的に避けるべき。
  NullPointerExceptionの温床になるし、「正常値としてのnull」と  
「異常値としてのnull」が混ざってしまうケースが多い。
  例えばDBに接続してある条件で検索を行い条件に合致したレコードを返す関数があった場合、nullが帰ってきた場合に「データベースの接続に失敗した(異常値としてのnull)」のか、「条件に合致するレコードが存在しなかった(正常値としてのnull)」なのかが分からない。
  ただし、nullチェックが強制される言語で、明らかにnullが異常値だと分かる関数については使っても問題ないと考えられる。
  例えばswiftではStringをIntに変換する際に`let a: Int? = Int("3")`のように書くが、この場合`a`にアクセスする前にnilチェックが強制され、また戻り値がnilなら異常値であるということが明確なので、エラー時にnilを返しても問題ない。
1. 真偽値を返す
  上と同様の理由で避けるべきである。
  例えばDBに接続してある条件に合致するレコードが存在するかどうかを調べる関数があった場合、falseが帰ってきた場合に「データベースの接続に失敗した(異常値としてのfalse)」のか、「条件に合致するレコードが存在しなかった(正常値としてのfalse)」なのかが分からない。
1. enumを返す
  一番簡単な方法。
  手続きが成功したかどうかを表すのには使えるが、手続きが成功した結果関数として何かの値を返すという用途には使えない。
```csharp
enum loginResult {
    Success,
    NetworkFailure,
    UserNotFound,
}
```
1. classを返す
  手続きの成否とともに何らかの値を返したいときに使える。
```csharp
class Result<T> {
    public bool isSuccess;
    public ErrorType? errorType;
    public T value
}
```
  このようなクラスを作る。関数の実装側は正常時には`isSuccess`に`true`を、`value`に関数から返したい値を代入してインスタンスを返す。異常時には`isSuccess`に`false`を、`errorType`にエラーの理由に該当する列挙型を代入してインスタンスを返す。必要ならばエラーコードやエラーメッセージ等をもたせても良い。
関数の呼び出し側は、`isSuccess`で関数の成功・失敗を判断してから適切な処理を行う。
異常値と正常値を分けることができるが、`isSuccess`が`false`のときに`value`にアクセスしないという決まりはプログラマ側が自主的に守らなくてはならない。

1. 多値を返す
  エラーが起きるおそれのある関数について、1番目の戻り値には正常値を、2番目の戻り値にはErrorを表すオブジェクトを返すように決めておく。goや(戻り値ではなく引数だが)node.jsの非同期処理などで主に使われている。
```go
// goでよくあるコード
file, err := os.Open("hoge.txt")
if err != nil {
    log.Fatal(err)
}
// doSomething
```
classを返すよりも簡単であるが、classを返す場合と同様`err`が`nil`で無いときに1番目の戻り値にアクセスしないという決まりはプログラマ側が自主的に守らなくてはならない。

1. Result(Either)型を返す
  A型又はB型をとりうるような値を扱える型として、Either型というものがある。
```swift
enum Result<T> {
    case Success(T)
    case Failure(Error)
}
```
  考え方としてはclassを返すのと同じだが、Result型の場合は`Failure`時に`Success`の値にアクセスしないことをコンパイラが保証してくれる。

## 言語別雑感

### C
例外無い、クラスも無い、多値どころか配列も返せないと無い無い尽くしの言語なので、エラーの場合は基本的に整数のエラーコードやNULLポインタを返す。
```c
// C言語でファイルアクセス時によくあるコード
FILE *fp;
fp = fopen("hoge.txt", "w");
if (fp == NULL) {
    fprintf(stderr, "ファイルをオープンできませんでした\n");
    return 1;
}
// doSomething
```
これは早期リターンそのものである。
また、コーディング規約で早期リターンや`goto`が使えない場合に、`do...while`文を使って次のように書くこともあるらしい。
```c
do {
  if (!cond) break;
  // do something
} while(0);

// リソースの開放など
return result;
```
ただ、個人的にはここまでするなら`goto`でも良いのでは？と思う。

### CSharp
C#には代数的データ型(直和型)が存在しないのでResult型を作ることは出来ない…(C#はまともでは無かった…😭)
しかしインターフェースとクラスを使えば似たようなことは実現できる。

```csharp
interface IResult<T> {
  bool isSuccess { get; }
}

class Failure<T>: IResult<T> {
  public bool isSuccess { get; } = false;
  public string message;
  public Failure(string messsage) {
    this.message = message;
  }
}

class Success<T>: IResult<T> {
  public bool isSuccess { get; } = false;
  public T value { get; }
  public Success(T value) {
    this.value = value;
  }
}
```
このようにFailureクラスとSuccessクラスを作っておく。
失敗するおそれのある関数はIResult型を返すようにすれば良い。
```csharp
IResult<int> SafeDivide(int x, int y) {
  if (y == 0) return new Error<int>("Zero Division Error.")
  
  return new Success<int>(x / y);
}
```
呼び出し側ではSuccessクラスかFailureクラスにキャストする。
```csharp
var result = SafeDivide(6, 2);

// if文の中でパターンマッチ
if (result is Success<int> succ) {
    Console.WriteLine(succ.value);
}
else if (result is Error<int> err) {
    Console.WriteLine(err.message); 
}
// このようにも書ける
Console.WriteLine((result as Success<int>)?.value);
```
ただし、Result型と比べると

- IResultインターフェースを勝手に継承した別クラスを作られる可能性がある
- 網羅性のチェックができないのでエラーハンドリングを強制できない

等の欠点がある。

さらにC#では戻り値を無視しても特にワーニングなどが出ないので、例外を使った方が良さそうである(C#はまともでは無かった…😭)

### Swift
例外もResult型(Either型)もどちらもある。
基本的にどちらを使っても良い？

`guard`という早期リターン専用の文が存在するので早期リターンを推奨している雰囲気がある。
早期リターンする場合にはアンラップ後の変数に別名をつけなくてはならないところがつらい。
```swift
// 早期リターン使わない場合
if let someValue = someValue {
  doSomething(someValue)
} 

// 早期リターン使う場合
guard let nonNilSomeValue = someValue {
  return
}
doSomething(nonNilSomeValue)

// 又はこう
if someValue == nil {
  return
}
doSomething(someValue!) // Forced Unwrapping が必要
```
ただし、関数の引数の場合は早期リターンでもアンラップ後の変数に同名を付けることができる。
```swift
func add(a: Int?, b: Int?) -> Int? {    
   guard let a = a, let b = b else { return nil }
   return a + b
}
```

### Ruby, Python, PHPなどの動的型付け言語
やめよう

## まとめ

### 早期リターンについて
- 事前条件チェックの最良の方法は型によるチェック
  - 静的型付け言語を使おう
  - ただし、型チェックですべての問題が解決できるわけではない
- 事前条件のチェックに早期リターンを使う
  → 積極的に行うべし
- それ以外にも早期リターンを使う
  → 状況に応じて。ただしelse禁止はやり過ぎでは？

### エラーハンドリングについて
- エラーが発生したら、回復可能なエラーなら回復を試み、回復不可能なエラーなら処理を停止する(クラッシュしてよいプログラムならログを吐いてクラッシュさせる。クラッシュするとまずいプログラムならエラー画面を出すなどする)。死ぬはずのプログラムを無理に延命しても無意味どころか有害である。
- 呼び出し元の関数にエラーを通知する方法には例外を使う方法と戻り値を使う方法がある。
  どちらを使っても良いが、同一プロジェクト内ではどちらかの方法に統一する。
- 例外を使う場合
  - try節で囲む範囲は最小限にする
  - try節でcatchする例外は最小限にする
  - 言語組み込みの例外クラスは直接スローせず、例外クラスを継承した独自の例外クラスを作ってそれをスローするようにする
  - 間違っても、キャッチした例外を無視して何事も無かったかのように処理を継続するようなことはしてはならない
- 戻り値を使う場合
  - 戻り値を無視してもワーニングやコンパイルエラーを出さない言語ではよくない
  - エラーとしてnullやfalse等の値を返すのはやめて、独自定義したResultクラスを返すようにする
  - Result型(Either型)が使える言語ならそれを使う


## 参考資料
- https://softwareengineering.stackexchange.com/questions/18454/should-i-return-from-a-function-early-or-use-an-if-statement
- https://blogs.msdn.microsoft.com/nakama/2008/12/29/net-part-1/
- https://qiita.com/Kokudori/items/2e4bd32abf7abea3186f
- https://www.slideshare.net/t_wada/exception-design-by-contract
