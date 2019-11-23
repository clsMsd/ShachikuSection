# 動的言語C#

## はじめに
一般的にC#は静的型付けのコンパイル言語に分類される。  
しかし、C#のプログラムでは実行時にも型情報は保存され、ダウンキャストなどの危険な操作を行う場合には実行時の型チェックが行われる  
(これはJavaも同じである。またC++でもdynamic_castを使えば同じことができる)。  
つまり C# は動的型付け言語でもあるといえる。  

(余談だが、世間の動的/静的型付けの分類は不十分であり、  
本当は 純粋動的型/純粋静的型/静的・動的併用型/型なし の4分類にするべきではと筆者は常日頃思っている。
まあこういうふうに分類を細かくやり始めると"Pythonは静的型チェックもできるけどどうする?"とか、  
"C++は動的に型チェックしたりしなかったりするけどどうする?"とか、
"C言語でも構造体にタグを持たせて自前で型チェックするコードを書けば動的に型チェックできるけどどうする?"  
とか言い始めてきりが無くなりそうであるが...)

(静的な型チェックを行わないという意味での)動的型付けは百害あって一理あるかないかという代物であるということは今日ではもはや世間の常識になっているが、  
一方で静的な型チェックが行えない入出力を扱うような場合に、高速なプロトタイピングのために意図的に静的型チェックを省略しダックタイプを行うことが有用なケースもある。

## リフレクション
一般的に Java/C# のような静的型付け言語での動的な機能といったら真っ先に上がるのがリフレクションであろう。  

### インスタンスの型を調べる
C# では全ての型の基底クラスである objectクラスに `GetType`メソッドがあり、  
全てのオブジェクトで型情報をこのメソッドで取得することができる。

```csharp
Console.WriteLine(1.GetType());     //=> System.Int32
Console.WriteLine(true.GetType());  //=> System.Boolean
Console.WriteLine("foo".GetType()); //=> System.String
```

他のクラスを継承している場合、オブジェクトの一番具体的な型が帰ってくる
```csharp
class Base {}
class Derived: Base {}

class Program {
   static void Main() {
      Base obj;
      if (new Random().NextDouble() > 0.5) {
         obj = new Base();
      } else {
         obj = new Derived();
      }

      Console.WriteLine(obj.GetType()); //=> Base or Derived
   }
} 
```

### 安全なキャスト
`typeof` を使うことで型名から静的に型情報(Typeオブジェクト)を取得することができる。  
`GetType`メソッドと組み合わせることで、安全なダウンキャストを行うことができる。

```csharp
class Base {}
class Derived: Base {}

class Program {
   static void Main() {
      Base obj;
      if (new Random().NextDouble() > 0.5) {
         obj = new Base();
      } else {
         obj = new Derived();
      }

      if (obj.GetType() == typeof(Derived)) {
         obj = (Derived)obj;
      }
   }
}
```

#### as演算子 と is演算子
C# には安全にダウンキャストを行うための as演算子と is演算子がある。   
```csharp
class Base {}
class Derived: Base {}

class Program {
   static void Main() {
      Base obj;
      if (new Random().NextDouble() > 0.5) {
         obj = new Base();
      } else {
         obj = new Derived();
      }
      
      var derived = obj as Derived; // キャストできない場合は null (swiftの as? に近い)
      if (derived != null) {
         Console.WriteLine("Derived");
      }

      if (obj is Derived derived2) { // キャストできる場合にはキャストしてderived2に代入
         Console.WriteLine("Derived");
      }
   }
}
```

### 文字列でフィールドにアクセス
```csharp
class Rect {
   public int width;
   public int height;
   public Rect(int width, int height) {
      this.width = width;
      this.height = height;
   }

   public int GetArea() {
      return this.width * this.height;
   }
}

var rect = new Rect(3, 4);
// Type Rect_t = Type.GetType("Rect");
Type Rect_t = typeof(Rect);

Rect_t.GetFiled("width").GetValue(rect);
```

## dynamic型
リフレクションを使えば文字列からオブジェクトのメンバにアクセスするなど動的型付け言語っぽいことができるが、  
dynamic型を使うとより動的型付け言語っぽいこと(ダックタイピング)ができる。  

```csharp
dynamic a = 1;
Console.WriteLine(a + 2); //=> 3

a = "foo";
Console.WriteLine(a); //=> foo 

a.bar(); //=> 実行時エラー
```

これを使えば JSON文字列をパースしたものをサクッと扱うということもできる。
```csharp
using System;
using Newtonsoft.Json;

class Program {
   static void Main(string[] args) {
      var json = "{ \"aaa\": 42 }";
      var obj = JsonConvert.DeserializeObject<dynamic>(json);

      Console.WriteLine(obj.aaa);
   }
}
```

プロダクションで使用するコードでは使わない方がよいが、プロトタイピングなどのために  
とりあえずサクッと動くものが作りたいという場合には便利である。  

## 式木 (Expression Trees)
関数を動的に生成する機能。  
普通、コンパイルを行ってネイティブコードを出力する言語では
ラムダ式などで関数を生成しているように見えても、関数の実体は実行時ではなくコンパイル時に生成される。

```javascript
for (let a = 0; i < 10; i++) {
   // forループが回るごとに新しい関数オブジェクトが生成されて、それが add に代入される 
   // (といっても実際の動作は処理系に依存するが)
   const add = (a, b) => a + b
}
```
```csharp
for (var a = 0; i < 10; i++) {
   // 関数の実体はコンパイル時に1つだけ生成され、実行時にはforループが回るごとに関数への参照が add に代入される  
   // (ローカル変数をキャプチャする場合はもう少し複雑になるが、関数の実体が1つだけしか生成されないということは変わらない)
   Func<int, int, int> add = (int a, int b) => a + b;
}
```

ほとんどの場合はこれで困ることは無いのだが、インタプリタのようなものを作ることを考えたときに、  
動的に関数を生成できたほうが便利であるということもある。  

C# では、実行時に動的に関数を生成する機能として 式木(Expression Tree)というものがある。  
```csharp
using System;
using System.Linq.Expressions;

class Program {
   static void main() {
      var x = Expression.Parameter(typeof(int), "x");
      var expr = Expression.Lambda<Func<int, int>>(
         Expression.Add(x, Expression.Constant(5)), x
      );

      var add = expr.Compile();
      Console.WriteLine(add(1));
   }
}
```
要するに C# のプログラム中で動的に C# の構文木を組み立ててコード生成・実行を行うことができる。  

## Roslyn for Scripting
.NET Core, .NET Framework で使われているC#コンパイラ(Roslyn)は C# で書かれており、  
その機能はライブラリとしても提供されている。  
これを使うと動的型付けでよくある Eval のようなことを C# で行うことができる。  

前回の発表で C/C++ のプログラムに組み込める Lua という言語を紹介したが、  
これを使うと C# のメインプログラムの中で C# のソースコードを動的に読みこんで実行するということができるので、  
プログラムのうち頻繁に変更が必要な部分をC#で、あまり変更が必要でない部分をC#で記述することで、効率的に開発を行うことができる(?)。  

パッケージの追加
```
$ dotnet add package Microsoft.CodeAnalysis.CSharp.Scripting --version 3.2.1
```

Evalのようなもの
```csharp
using System;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Scripting;

class Program {
   static async Task Main(string[] args) {
      var code = "Console.WriteLine(\"Hello Roslyn for Scripting\");";

      await CSharpScript.RunAsync(code);
   }
}
```

RELP
```csharp
using System;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Scripting;

class Program {
   static async Task Main(string[] args) {
      while (true) {
         var input = Console.ReadLine();
         var result = await CSharpScript.EvaluateAsync(input);
         Console.WriteLine(result);
      }   
   }
}
```

### スクリプト実行
.NET Framework / mono の場合は `csi` コマンドで C# インタプリタ を起動することができる。  
.NET Core の場合は公式には提供されていないものの、有志により作られた dotnet-script というツールがあり、
`csi` コマンドと同じように使用できる上、一部拡張機能も追加されている。  

dotnet-scriptのインストール
```bash
$ dotnet tool install -g dotnet-script

$ dotnet script # REPLが起動する
```

普通のC#では関数や変数はクラスの中にしか定義できないが、スクリプト実行ではトップレベルに関数や変数を宣言することができる。  
またスクリプト実行といっても内部的にはコンパイルして実行しているので、型チェックも行われる。
```csharp
var a = 1;

int add(int a, int b) {
   return a + b;
}

Console.WriteLine(add(a, 1));

class Foo { public int foo = 42; }

var f = new Foo();
Console.WriteLine(f.foo);

if (false) {
   add("foo", "bar"); //=> コンパイルエラー
}
```

スクリプトから他のスクリプトやdllファイルを読み込むということもできる
```csharp
// Lib1.csx
int Add(int a, int b) {
   return a + b;
}
```

```csharp
#load "Lib1.csx"
#r "Lib2.dll"

Console.WriteLine(Add(1, 2))
```

他のスクリプトファイルを `#load` すると、他のスクリプトでトップレベルに定義されている変数などが  
読み込んだ側のスクリプトのトップレベルにぶちこまれるので注意が必要である。  
(スクリプト言語によくあるようなimportした他のモジュールに別名を付けるような機能は残念ながら無い)  
```csharp
// Lib.csx
var a = 1;
```

```csharp
#load "Lib.csx"

var a = 1; // コンパイルエラー
```

公式の csiコマンドでは nuget(.NETのパッケージマネージャー)のパッケージを使うことはできないが、  
dotnet-scriptの場合は拡張機能で nugetのパッケージを読み込むこともできる。  
```csharp
#r "Microsoft.CodeAnalysis.CSharp.Scripting, 3.2.1"
using System;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Scripting;

while (true) {
   var input = Console.ReadLine();
   var result = await CSharpScript.EvaluateAsync(input);
   Console.WriteLine(result);
}   
```

#### 利用例1. プロトタイピング
新しい言語やライブラリを使った開発を行う場合は、小さなサンプルプログラムを書きながら動作を確かめて開発を進めるということが多いと思う。  
そのような場合に、サンプルプログラムをC#スクリプトで書いて動作の確認ができたら本体のプログラムにコピペするという方法で効率的に開発ができる。  

#### 利用例2. 簡易CLIツール
複数の小さな機能をまとめて大きなプログラムを作る場合に、本体の大きなプログラムとは別に  
個々の機能が呼び出せると便利な場合がある。  
例えばある作業のためにAPI A・API B・API Cを叩くツールがあった場合に、  
最終的な成果物のプログラムでは1コマンドでは全APIを叩くがそれとは別に  
個々のAPIを叩く機能があると便利である。  
このような場合、コマンドライン引数で動作を変えるようにするのが一般的なやり方ではあるが、  
コマンドライン引数のパースやそれによる分岐などを実装するのが面倒であるし、  
最終的な成果物のプログラムでは個々のAPIを叩く機能は隠したいということもある。  

そのような場合、C#スクリプトを使えばメインのプログラムをC#で記述して、完成品のdllから一部のクラス、関数を直に呼び出すということができるので便利である。  

```csharp
public class BlobManager {
   public static async Task CreateAsset(string assetName, string fileName) {
   var config = GetConfig("appsettings.json");
   var client = await CreateMediaServicesClientAsync(config);
   client.LongRunningOperationRetryTimeout = 3;

   var asset = await client.Assets.GetAsync(config.ResourceGroup, config.AccountName, assetName);

   if (asset != null) {
      WriteLine($"Asset {asset} already exists.");
      return;
   }

   asset = await client.Assets.CreateOrUpdateAsync(config.ResourceGroup, config.AccountName, assetName, new Asset());
   var response = await client.Assets.ListContainerSasAsync(
      config.ResourceGroup, config.AccountName, assetName,
      permissions: AssetContainerPermission.ReadWrite,
      expiryTime: DateTime.UtcNow.AddHours(4).ToUniversalTime()
   );

   var sasURI = new Uri(response.AssetContainerSasUrls.First());
   var container = new CloudBlobContainer(sasURI);
   }
}

class Program {
   static async Task Main() {
      await BlobManager.CreateAsset("foo", "bar");

      // そのあといろいろ処理
   }
}
```

```csharp
#r "App.dll"

var assetName = "foo";
var fileName = "bar";
await BlobManager.CreateAsset(assetName, fileName);
```

これももちろんただのC#なので、コマンドに与える引数を変数で定義したり、文字列の中で変数展開したりが普通にできる。  
Bashの文字列中の変数展開がいつまで経っても覚えられない人にお勧め。  

```bash
a="pwd"
echo a    #=> a
echo $a   #=> pwd
echo "$a" #=> pwd
echo '$a' #=> $a
echo `$a` #=> (カレントディレクトリのパス)
```

#### 利用例3. テスト
カバレッジやパフォーマンスなどの詳細なレポートが必要な場合はテスティングフレームワークが必要だが、  
そのような高度な機能が必要でない場合はdllを読み込んでテストするスクリプトがあれば十分なことも多いだろう。  

.NETの開発ではテスティングフレームワークとして xUnit.net を使うのが一般的だが、そこまで高機能なフレームワークを使う必要がない場合、
C#スクリプトでdllファイルを読み込み、テスト対象の関数を直接実行するということができる。  

```csharp
public class Program {
   public static int Add(int a, int b) => a + b;
}
```
```csharp
#r "app.dll"
using System.Diagnostics;

Debug.Assert(Program.Add(1, 2) == 3);
```

ただし、この方法は publicなクラスの publicなメソッドしかテストできないので  
privateなメソッドのテストがしたい場合はリフレクションを使って無理やりアクセスする必要がある。  

#### 利用例4. 設定ファイル
変更可能な設定はソースコードにそのまま書くのではなく外部のテキストファイルにJSONやXMLのようなフォーマットで記述して  
それをプログラムから読み込んで使うのが一般的である。  
しかし、JSONはコメントが書けないとかXMLは書くのが面倒とかいろいろ問題があるし、  
基本的に設定ファイルでは変数や関数を定義できないので不便である。

Cocoapods や Chef など一部のプログラムは設定ファイルをスクリプト言語(Ruby)で記述するようにしている。  
この場合、スクリプト言語の機能がそのまま使えるので、変数や関数を定義したり条件分岐して設定を変えるといったことが簡単にできる。  
しかし、多くの場合このようなDSLとしてのスクリプト言語は動的型付け言語が使われるので型チェックが行われないし、  
プログラム本体と別の言語を使っている場合、設定を記述ためだけにその言語を習得するというのは大変である。　　

そこで、C#スクリプトで設定を記述すれば
- プログラム本体もC#で書けばいいのでわざわざ別言語を習得する必要がない
- 変数や関数を定義したり条件分岐して設定を変えるといったことが簡単にできる
- 実行前に型チェックを行うので、実際にプログラムを実行する前に設定の書き方が間違っていないかチェックできる
と良い事ずくめである。  

ただし、設定ファイルをスクリプト言語で書くということは危険も伴う。  
無限ループするようなプログラムを書けば設定ファイルを読み込んだだけでプログラムがハングアップしてしまうし、  
そこまでではなくても複雑なループや条件分岐が入り混じった設定ファイルは可読性の観点からも問題である。  
設定ファイルをスクリプト言語で書く際にはそのような点への注意が必要である。  

まずはアプリで使う設定を表す型を定義する。  
```csharp
// AppConfig.cs
public enum AccountType {
   Premium, Normal, Guest
}

public class AppConfig {
   public string accountName { get; }
   public string accountPassword { get; }
   public AccountType accountType { get; }

   public AppConfig(
      string accountName,
      string accountPassword,
      AccountType accountType
   ) {
      this.accountName = accountName;
      this.accountPassword = accountPassword;
      this.accountType = accountType;
   }
}
```

スクリプト側では型定義を利用するには、型定義があるcsファイルをそのまま読み込む方法とコンパイル後のdllファイルを読み込む2つの方法がある。  
dllファイルを読み込む方法では、csファイルの型定義を変更してもコンパイルされるまで変更が反映されないという問題がある。  
csファイルを読み込む方法では、C#スクリプトの制限として名前空間を利用することができないので、型定義をグローバル名前空間で行う必要がある。  
```csharp
// config.csx

#r "App.dll"
// or
#r "AppConfig.cs"

// C# のプログラムなので、csファイルで定義されている型が使える。
// コンストラクタの引数が間違っているとコンパイルエラーになる。
// エディタが対応していれば補完も効く。
var conf = new AppConfig(
   accountName: "masuda",
   accountPassword: "password",
   accountType: AccountType.Guest
);

conf
```

設定ファイルを読み込む側では、次のように書く。  
```csharp
// Program.cs
using System;
using System.IO;
using System.Text;

using Microsoft.CodeAnalysis.Scripting;
using Microsoft.CodeAnalysis.CSharp.Scripting;

class Program {
   static void Main() {
      var configStr = File.ReadAllText("./config.csx", Encoding.UTF8);
      // CSharpScript.EvaluateAsync でコードを読み込んだ場合、#r や #load ディレクティブで探索するファイルのパスを指定する必要がある
      var opts = ScriptOptions.Default
         .WithMetadataResolver(ScriptMetadataResolver.Default.WithBaseDirectory(Environment.CurrentDirectory))
         .WithSourceResolver(ScriptSourceResolver.Default.WithBaseDirectory(Environment.CurrentDirectory));

      var config = CSharpScript.EvaluateAsync<AppConfig>(configStr, opts).GetAwaiter().GetResult();

      Console.WriteLine(config.accoutName);
      Console.WriteLine(config.accoutPassword);
   }
}
```
このようにすれば設定を型付きで読み込むことができ、型が間違っている場合は読み込んだ時点でエラーとなる。  

プログラムの実行は行わずに、設定ファイルの型チェックだけをしてみよう。  
`config.csx` をスクリプト実行してみる。  
```bash
$ dotnet script config.csx
error CS0029: 型 'AppConfig' を 'int' に暗黙的に変換できません
```
型エラーが起きる。  
スクリプト実行した場合はスクリプトで最後に評価された値がスクリプト全体の戻り値(?)になるが、この戻り値の型は void 又は int である必要があるらしい
(良くわからない制約だが`Main`の戻り値が void か int である必要があるのと同じだろうか)。  

この問題の対処法がいくつかあるが、1つはプリプロセッサを使うことである。  
スクリプト側では `LOAD_FROM_MAIN_PROGRAM` がdefineされている場合にのみ config を返すようにする。  
```csharp
// config.csx

#r "App.dll"
// or
#load "AppConfig.cs"

var conf = new AppConfig(
   accountName: "masuda",
   accountPassword: "password",
);

#if LOAD_FROM_MAIN_PROGRAM
conf
#endif
```

本体のプログラムから設定ファイルをロードするときには、スクリプトの先頭で `LOAD_FROM_MAIN_PROGRAM` をdefineするようにする。  
```csharp
// Program.cs
using System;
using System.IO;
using System.Text;

using Microsoft.CodeAnalysis.Scripting;
using Microsoft.CodeAnalysis.CSharp.Scripting;

class Program {
   static void Main() {
      var configStr = "#define LOAD_FROM_MAIN_PROGRAM\n" + File.ReadAllText("./config.csx", Encoding.UTF8);
      var opts = ScriptOptions.Default
         .WithMetadataResolver(ScriptMetadataResolver.Default.WithBaseDirectory(Environment.CurrentDirectory))
         .WithSourceResolver(ScriptSourceResolver.Default.WithBaseDirectory(Environment.CurrentDirectory));

      var config = CSharpScript.EvaluateAsync<AppConfig>(configStr, opts).GetAwaiter().GetResult();

      Console.WriteLine(config.AccoutName);
      Console.WriteLine(config.AccoutPassword);
   }
}
```

もう一つの対処法は、設定ファイルを実行することで型チェックをするという発想を諦めて  
設定ファイルのチェックを行う別のスクリプトを用意することである。  

設定ファイルの型チェック用スクリプト
```csharp
// config_checker.csx
#r "Microsoft.CodeAnalysis.CSharp.Scripting, 3.2.1"

using System;
using System.IO;
using System.Text;

using Microsoft.CodeAnalysis.Scripting;
using Microsoft.CodeAnalysis.CSharp.Scripting;

var configStr = File.ReadAllText("./config.csx", Encoding.UTF8);
var opts = ScriptOptions.Default
   .WithMetadataResolver(ScriptMetadataResolver.Default.WithBaseDirectory(Environment.CurrentDirectory))
   .WithSourceResolver(ScriptSourceResolver.Default.WithBaseDirectory(Environment.CurrentDirectory));

var config = await CSharpScript.EvaluateAsync<AppConfig>(configStr, opts);
```
設定ファイルのチェックを行う際は、このスクリプトを実行する。  
この方法の場合、単なる型チェックだけでなく設定の値のチェックを行ってもよいだろう。  

```csharp
// config_checker.csx
#r "Microsoft.CodeAnalysis.CSharp.Scripting, 3.2.1"

using System;
using System.IO;
using System.Text;

using Microsoft.CodeAnalysis.Scripting;
using Microsoft.CodeAnalysis.CSharp.Scripting;

var configStr = File.ReadAllText("./config.csx", Encoding.UTF8);
var opts = ScriptOptions.Default
   .WithMetadataResolver(ScriptMetadataResolver.Default.WithBaseDirectory(Environment.CurrentDirectory))
   .WithSourceResolver(ScriptSourceResolver.Default.WithBaseDirectory(Environment.CurrentDirectory));

var config = await CSharpScript.EvaluateAsync<AppConfig>(configStr, opts);

if (config.accountPassword.Length <= 6) {
   Console.WriteLine("accountPassword length must be longer than 6.");
   throw new Exception("Invalid Config Error");
}
```

あるいは、設定ファイルのチェックは本体のプログラムに書いて、チェックを行う関数だけをスクリプト実行するというのでよい
(こうすると、設定ファイルのチェックを本体のプログラムとスクリプトで共有できる)。  

本体のプログラム
```csharp
// Program.cs
using System;
using System.IO;
using System.Text;

using Microsoft.CodeAnalysis.Scripting;
using Microsoft.CodeAnalysis.CSharp.Scripting;

public class Program {
   public static async Task<AppConfig> LoadConfig(string filePath) {
      var configStr = File.ReadAllText(filePath, Encoding.UTF8);
      var opts = ScriptOptions.Default
         .WithMetadataResolver(ScriptMetadataResolver.Default.WithBaseDirectory(Environment.CurrentDirectory))
         .WithSourceResolver(ScriptSourceResolver.Default.WithBaseDirectory(Environment.CurrentDirectory));

      return await CSharpScript.EvaluateAsync<AppConfig>(configStr, opts);
   }

   public static void ConfigCheck(AppConfig config) {
      if (config.accountPassword <= 6) {
         Console.WriteLine("accountPassword length must be longer than 6.");
         throw new Exception("Invalid Config Error");
      }
   }

   static void Main() {
      var config = LoadConfig("./config.csx").GetAwaiter().GetResult();
      ConfigCheck(config);
      
      Console.WriteLine(config.AccoutName);
      Console.WriteLine(config.AccoutPassword);
   }
}
```

設定ファイルの型チェック用スクリプト
```csharp
// config_checker.csx
#r "App.dll"

var config = Program.LoadConfig("config.csx");
Program.ConfigCheck(config);
```

## まとめ
C# は便利なのでどんどん使おう。  

## 参考資料
[https://ufcpp.net/study/csharp/sp3_expression.html]
