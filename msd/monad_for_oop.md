# オブジェクト指向プログラマのためのモナド入門

## はじめに
Haskellについて紹介した際に、「Haskellでは副作用をモナドという型クラスの値で表現している」とか何とか言っていたが、
実際Haskellを使いこなす上でモナドの理解は必須である。
(たまに「実際にHaskellを使う分にはモナドのことを分かってなくても大丈夫」だとか言う人がいるが、
これはHaskell人口を増やそうとするHaskell使いたちの巧妙な罠であるので信じてはいけない)。
また、実はHaskell以外の普通の言語であってもモナドやモナドっぽいものは多々ある。  
(配列、SwiftのOptinal、JSのPromiseなど)

また、モナドの秘めた力には未だに謎も多く、今回紹介するのはモナドの特徴のほんの一部である。
(実際Haskellを使う上で「モナドとは何か」が分かるのというのはほんの入口に入ったところで、  
実際の開発では「どのようなモナドがあるのか」「それらのモナドをどのように使うのか」が重要になる)

なお、基本的にサンプルコードはC#で書いてあるが、文脈から明らかな場合にジェネリクスの型引数を省略するなどしている箇所が
あったりするのでそのへんは雰囲気で察して欲しい。  

## ジェネリクス
モナドの説明をする前に下準備として、以前エラーハンドリングについて説明したときに使った`Result`型に再登場してもらおう。  

```csharp
class Result<T> {
   public bool isSuccess; // 失敗か成功かを表すフラグ
   public T value;        // 成功時の値
   public string msg;     // 失敗時に失敗の原因を表すメッセージ
                          // 必要に応じてエラーの種別を表すエラーコードなどを追加で持たせてもよいが、ここではそうしない

   private Result(T value, bool isSuccess, string msg) {
      this.value = value;
      this.isSuccess = isSuccess;
      this.msg = msg;
   }

   public static Result<T> Success(T value) {
      return new Result<T>(value, true, ""); 
   }

   public static Result<T> Failure(string msg) {
      // default は型を引数としてとり、その型のデフォルト値(例えばintなら0, boolならfalse, 参照型ならnull)を返す関数
      return new Result<T>(default(T), false, msg); 
   }
}
```

`isSuccess`が`false`のときに`value`を読み込まないという決まりはコンパイラでチェックできないので  
プログラマが自主的に守るように気をつけなければならないが、ここでは妥協してそれはそれでよいものとする。  

```csharp
Result<int> safeDiv(int a, int b) {
   if (b == 0) {
      return Result<int>.Failure("Zero Divide Errir");
   } else {
      return Result<int>.Success(a / b);
   }
}
```

## Result、藻などになる？
世の中モナドというと「箱」だとか「文脈を持った値」だとか「自己関手の圏におけるモノイド対象」だとか  
まるで他人に理解させる気がない説明が氾濫している(個人の感想です)が、  
モナドとは、一言でいうと「ある特別な条件を満たすジェネリッククラス」のことである。  

こう説明されると、当然「ある特別な条件」とは何だ？という疑問が湧くことになるが、  
ここでは「ある特別な条件」の説明に入る前に、先程書いた`Result<T>`クラスについてもう少し考えてみよう。

### Result<T>クラスの問題
今、次のようなコードがあったとする。  

```csharp
int addOne(int x) => x + 1;
int multTwo(int x) => x * 2;
int divideThreeBy(int x) => 3 / x;

var a = 12;

Print(divideThreeBy(addOne(multTwo(divideThreeBy(a)))));
```

`divideThreeBy`は引数が0だと例外を投げるので、この戻り値を`Result`型に置き換えてみよう。  

```csharp
int addOne(int x) => x + 1;
int multTwo(int x) => x * 2;
Result<int> divideThreeBy_safe(int x) => 
   x != 0 ? Result<int>.Success(3 / x) : Result<int>.Failure("Zero Divede Error");

var a = 12;

var b = divideThreeBy_safe(12);
if (b.isSuccess) {
   var c = divideThreeBy_safe(addOne(multTwo(b.value)));
   if (c.isSuccess) {
      Pinrt(c.value);
   } else {
      Print(c.msg);
   }
} else {
   Print(b.msg);
}
```

`divideThreeBy`の戻り値を引数として使っている後続の処理で`Result`が`Success`か`Failure`かによって  
処理を分岐させる必要が出てきた。  

こんなコード書くことは無いと思うかもしれないが、例えば1,2,3の3つのAPIがあり、  
API1で取得した値を使ってAPI2を呼び出し、API2で取得した値を使ってAPI3を呼び出すような  
Web開発でよくありそうな処理は次のようなコードになってしまう。

```csharp
// 普通C#ではAPIコールなどの時間のかかる処理はasync/awaitを使うが、本質的ではないのでここでは省略
var result1 = callAPI01(someValue);

if (result1.isSuccess) {
   var result2 = callAPI02(result1.value);
   
   if (result2.isSuccess) {
      var result3 = callAPI03(result3.value);

      if (result3.isSuccess) {
         Console.WriteLine(result3.value);
      } else {
         Console.WriteLine(result3.msg);
      }
   } else {
      Console.WriteLine(result2.msg);
   }
} else {
   Console.WriteLine(result1.msg);
}
```

この問題の解決策の1つは、今まで`int`を引数にとっていた他のすべて関数の`Result<int>`型の引数をとる  
バージョンを作ることである。  

```csharp
int addOne(int x) => x + 1;
Result<int> addOne_safe(Result<int> x) =>
   x.isSuccess ? Result<int>.Success(addOne(x)) : Result<int>.Failure(x.msg);

int multTwo(int x) => x * 2;
Result<int> multTwo_safe(Result<int> x) =>
   x.isSuccess ? Result<int>.Success(multTwo(x)) : Result<int>.Failure(x.msg);

Result<int> divideThreeBy_safe(int x) => 
   x != 0 ? Result<int>.Success(3 / x) : Result<int>.Failure("Zero Divede Error");

Result<int> divideThreeBy_safe_safe(Result<int> x) => 
   x.isSuccess && x.value != 0 ? divideThreeBy_safe(x.value) : Result<int>.Failure(x.msg);

void Print_safe(Result<int> x) =>
   x.isSuccess ? Print(x.value) : Print(x.msg);

var a = 12;
Print_safe(divideThreeBy_safe_safe(addOne_safe(multTwo_safe(divideThreeBy_safe(a)))));
```

これでスッキリ書けるようになった…  
が、当然これではすべての関数について普通の型の引数をとるものと`Result`型の引数をとるものの  
2つのバージョンを用意する必要があり、とても実用的ではない。  

しかし、ここで普通の関数と`Result`型の関数を見比べてみると、`Result`型の関数はすべて  
「引数が`Success`ならば普通の関数を実行しその戻り値を`Success`でラップしてから返す。  
引数が`Failure`なら`msg`を取り出して`Failure`でラップして返す。」  
ということしかしていない。  
つまり、普通の型の関数があれば`Result`型の関数は自動的に生成できるのである。  

要するに、`f: T -> U`という型の関数`f`があったときに、次の3つの関数をいい感じに作ってくれる仕組み(高階関数)があると便利である。  
1. `T -> Result<U>`: 入力が普通のクラス、出力がジェネリッククラス
1. `Result<T> -> Result<U>`: 入力も出力もジェネリッククラス
1. `Result<T> -> U`: 入力がジェネリッククラス、出力が普通のクラス

ちなみにHaskellでは 1. 2. 3. のような関数を作る高階関数のことをそれぞれ、
`return`, `fmap`, `bind` と呼ぶので、以下でもそれを踏襲することにする。
(厳密にいうと`bind`だけは実際の定義が上の定義と違う(後で述べる))

まず1つめの` T -> Reuslt<U>`という関数(`return`)だが、これは引数に`f`を適用したあと`Result<U>.Success`でラップすればよい。  

```csharp
Result<U> Return(Func<T, U> f, T a) => Result<U>.Success(f(a));
```

## ファンクター
次に`Result<T> -> Result<U>`型の関数(`fmap`)を作る高階関数について考えてみよう。  
これは上で述べたように、
「引数が`Success`ならば普通の関数を実行しその戻り値を`Success`でラップしてから返す。
引数が`Failure`なら`msg`を取り出して`Failure`でラップして返す。」
という関数を作ればよい。  

```csharp
Func<Result<T>, Result<U>> Fmap<T, U>(Func<T, U> f) {
   return (Result<T> x) => {
      if (x.isSuccess) {
         return Result<U>.Success(f(x.value));
      } else {
         return Result<U>.Failure(x.msg);
      }
   };
}

class Result<T> {
   public bool isSuccess;
   public T value;       
   public string msg;
   ...
   // インスタンスメソッド版 
   public Result<U> Fmap(Func<T, U> f) {
      if (this.isSuccess) {
         return Result<U>.Success(f(this.value));
      } else {
         return Result<U>.Failure(this.msg);
      }
   }
}
```

### ファンクター則
`fmap`の実装は上でよいのだが、ここで別のバージョンとして次のような`fmap`を考えてみよう。

```csharp
Func<Result<T>, Result<U>> Fmap<T, U>(Func<T, U> f) {
   return (Result<T> x) => {
      if (typeof(U).ToString() == "System.Int32") {
         return Result<U>.Success(3); // fの戻り値がint型のときだけはなぜか Success(3) を返す
      }

      if (x.isSuccess) {
         return Result<U>.Success(f(x.value));
      } else {
         return Result<U>.Failure(x.msg);
      }
   };
}
```

これでも型はあっている(`T -> U`の関数を引数にとり、`Result<T> -> Result<U>`の関数を返している)  
のでコンパイルは通るが、これは我々が欲しい`Fmap`ではないだろう。  
重要なことは、`T -> U`という型の関数があった時に*いい感じの*`Result<T> -> Result<U>`という型の関数が作れると便利なのであって、
単純に型が`Result<T> -> Result<U>`の関数ならば何でも良いという訳ではないことである。  

ではこの*いい感じの*関数というものは具体的にどんな性質をもつものだろうか？
結論から言うとこれは次の2つの条件をみたすものとなる。  

1. 何もしない関数`id_T: T -> T`と`id_Res: Result<T> -> Result<U>`に対して、`Fmap<T, U>(id_T) == id_Res`  
例)
```csharp
int id_int(int x) => x;
Result<int> id_res(Result<int> x) => x;

var anyValue = Result<int>.Success(12); 
Assert(Fmap(id_int)(anyValue) == id_Res(anyValue)); // これがどんな値に対しても成り立つ
```

1. `f: T -> U`と`g: U -> V`という関数があった場合、`Fmap(f) >> Fmap(g) == Fmap(f >> g)` (`>>`は関数合成)
```csharp
int f(int x) => x + 1;
int g(int x) => 2 * x;

var anyValue = Result<int>.Success(12);

Assert(Fmap(g)(Fmap(f)(anyValue)) == Fmap((int x) => g(f(x)))(anyValue))
```

上で書いた「int型のときだけはなぜか Success(3) を返すようにするFmap」がこの条件を満たさないのは明らかである。  

この2つの条件を*ファンクター則*といい、ファンクター則を満たすようなFmapが実装されているジェネリッククラス(1階の型コンストラクタ)
のことをファンクターという。    

HaskellのFunctorの定義
```haskell
class Functor f where
   fmap :: (a -> b) -> f a -> f b 
```

ちなみにこれらの条件はコンパイラではチェックしてくれないので、ファンクターを作るプログラマがこの条件を満たすように
気をつけなければならない。  

fmapという関数の名前からして察している人もいるかもしれないが、配列はファンクターであり、
配列のfmapはmapに対応する。  

## モナド
最後に`Result<T> → U`という型の関数だが、これは*いい感じの*関数として作ることができない。  
というのも、引数として受け取った`Result`型が`Failure`だった場合、通常の型として返す値が無いからである。  
(そもそも`Result`型を作った動機が`int`などのプリミティブな型に処理の成功/失敗等の付加的な情報を付加することにあったので、
プリミティブな型だけでそういった情報を伝えることができるなら`Result`型を作る意味がない)
要するに、一度`Result`型で*汚れてしまった*値からもとのプリミティブな値を取り出すことは
(`Failure`であった場合のことを全く無視するなどしないと)できないのである。  

```csharp
int addOne(int x) => x + 1;
int addOne_safe(Result<int> x) {
   if (x.isSuccess) {
      return addOne(x.value);
   } else {
      // return ??? ここで何を返すべきか? 
      return 42; // 型を合わせるために無関係なint型の値を返すだけならできるが、今求めているものはそういうものではない
   }
}
```

`Result<T> -> U`型の関数は作れないが、`Result<Result<T>> -> Result<U>`型の関数を作る関数(`bind`)は*いい感じ*につくることができる。  

```csharp
Func<Func<T, Result<U>>, Result<U>> Bind<T, U>(Result<T> a) {
   return (Func<T, Result<U>> f) => {
      if (a.isSuccess) {
         return f(a.value);
      } else {
         return Result<U>.Failure(a.msg);
      }
   };
}

class Result<T> {
   public bool isSuccess;
   public T value;   
   public string msg;
   ...
   // インスタンスメソッド版
   public Result<U> Bind(Func<T, Result<U>> f) {
      if (this.isSuccess) {
         return f(this.value);
      } else {
         return Result<U>.Failure(this.msg);
      }
   }
}
```

before
```csharp
var result1 = callAPI01(someValue);

if (result1.isSuccess) {
   var result2 = callAPI02(result1.value);
   
   if (result2.isSuccess) {
      var result3 = callAPI03(result3.value);

      if (result3.isSuccess) {
         Console.WriteLine(result3.value);
      } else {
         Console.WriteLine(result3.msg);
      }
   } else {
      Console.WriteLine(result2.msg);
   }
} else {
   Console.WriteLine(result1.msg);
}
```

after
```csharp
var result = callAPI01(someValue)
            .Bind(callAPI02)
            .Bind(callAPI03);

if (result.isSuccess) {
   Console.WriteLine(result.value);
} else {
   Console.WriteLine(result.msg);
}
```

```csharp
int addOne(int x) => x + 1;
Result<int> addOne_safe(Result<int> x) =>
   x.isSuccess ? Result<int>.Success(addOne(x)) : Result<int>.Failure(x.msg);

int multTwo(int x) => x * 2;
Result<int> multTwo_safe(Result<int> x) =>
   x.isSuccess ? Result<int>.Success(multTwo(x)) : Result<int>.Failure(x.msg);

Result<int> divideThreeBy_safe(int x) => 
   x != 0 ? Result<int>.Success(3 / x) : Result<int>.Failure("Zero Divede Error");

Result<int> divideThreeBy_safe_safe(Result<int> x) => 
   x.isSuccess ? divideThreeBy_safe(x.value) : Result<int>.Failure(x.msg);

void Print_safe(Result<int> x) =>
   x.isSuccess ? Print(x.value) : Print(x.msg);

var a = 12;
Print_safe(divideThreeBy_safe_safe(addOne_safe(multTwo_safe(divideThreeBy_safe(a)))));
```

```csharp
int addOne(int x) => x + 1;
int multTwo(int x) => x * 2;
Result<int> divideThreeBy_safe(int x) => 
   x != 0 ? Result<int>.Success(3 / x) : Result<int>.Failure("Zero Divede Error");

var a = 12;
var result = divideThreeBy_safe(a)
            .Fmap(multTwo)
            .Fmap(addOne)
            .Bind(divideThreeBy_safe);

Print(result);
```


### モナド則
fmapのときに型以外に満たすべき条件があったように、bindにも次のような満たすべき条件がある。  
(aは普通の値、xはResult型の値)

1. `Bind(Return(a))(f) == f(a)`
1. `Bind(x)(Return) == x` 
1. `Bind(Bind(x)(f))(g) == Bind(x)((a) => Bind(f(a))(g))`

HaskellのMonadの定義
```haskell
class Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
  -- bind :: (a -> m b) -> m a -> m b
  return :: a -> m a
```

ファンクターと同様に、モナド則を満たすような`bind`(と`return`)が実装されているジェネリッククラスのことをモナドという。  

最初に述べたように配列はモナドでもあり、配列における`bind`は`flatMap`に相当する。  
