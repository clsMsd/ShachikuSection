# .NET6入門

## 環境構築
https://dotnet.microsoft.com/en-us/download の指示に従ってインストールする。
### Windows
公式からインストーラーをダウンロードしてインストール。

### Linux(Ubuntu)

debファイルを落としてaptでインストールする。

```
wget https://packages.microsoft.com/config/ubuntu/20.04/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
sudo dpkg -i packages-microsoft-prod.deb
rm packages-microsoft-prod.deb
sudo apt-get update; \
  sudo apt-get install -y apt-transport-https && \
  sudo apt-get update && \
  sudo apt-get install -y dotnet-sdk-6.0
```

インストールスクリプトが用意されているのでそちらを使ってもよい。

### Mac
インストーラーをダウンロードして普通にインストールする。

homebrewを使っている人はそちらでもOK。
```
brew install caskroom/cask/
brew cask install dotnet-sdk
```

インストールが終わると`dotnet`コマンド(dotnet CLI)が使えるようになる

後々使うので `dotnet tool install -g dotnet-script` でスクリプト実行用のツールをインストールしておくとよい(monoでもよい)。

エディタは何を使ってよいが、VSCodeがおすすめ。
C#というそのものズバリな名前のMS製拡張機能があり、C#向け補完機能が使える。


## dotnet cliの主なコマンド
- `dotnet new` 新規プロジェクトの作成
- `dotnet build` プログラムのビルド
- `dotnet run` プログラムのビルド + 実行
- `dotnet tool install パッケージ名` パッケージをグローバルにインストールする
- `dotnet tool uninstall パッケージ名` パッケージを削除する
- `dotnet add package パッケージ名` パッケージをプロジェクトに追加する
- `dotnet remove package パッケージ名` パッケージをプロジェクトから削除する

## Hello World
`dotnet new console` コマンドで新しいコンソールアプリのプロジェクトを作ることができる。  
これでHello Worldが作れる… というか、プロジェクトを作成した時点で気を利かせて Hello World 

## 実際の開発
もう少し実用的なプログラムの開発を通して、実際の .NET による開発の様子がどのようなものか見てみよう。 
今回はサンプルとして電卓を作ってみる。

今回は電卓のコア機能は汎用的なライブラリとして作り、それをコンソールアプリ、GUIアプリ、Webアプリなど様々な形式で利用するというシチュエーションを想定して開発を進める。
.NETでは複数のプロジェクトをまとめて管理するために、ソリューションファイルというものを使用する。
`dotnet new sln` で新しいソリューションファイルを作成し、`dotnet sln add ソリューションに追加するプロジェクトファイルのパス`でプロジェクトをソリューションに追加することができる。

```bash
$ mkdir Calculator
$ cd Calculator
$ dotnet new sln # 新しいソリューションの作成
$ dotnet new classlib --name=Calculator.Core # クラスライブラリの作成
$ dotnet sln add ./Calculator.Core/Calculator.Core.csproj # プロジェクトをソリューションに追加
$ git init
$ dotnet new gitignore # .gitignoreを自動生成してくれる
$ cd ./Calculator.Core
```

### コア機能となるライブラリの作成
オラオラっと電卓を書く。
```csharp
namespace Calculator.Core;

using System;
using System.Collections.Generic;

public enum Symbol {
  Plus, Minus, Aste, Slash, LPar, RPar
}
public abstract record Token {}
public sealed record NumToken(int val): Token {};
public sealed record SymToken(Symbol sym): Token {
  public static SymToken Plus = new SymToken(Symbol.Plus);
  public static SymToken Minus = new SymToken(Symbol.Minus);
  public static SymToken Aste = new SymToken(Symbol.Aste);
  public static SymToken Slash = new SymToken(Symbol.Slash);
  public static SymToken LPar = new SymToken(Symbol.LPar);
  public static SymToken RPar = new SymToken(Symbol.RPar);
};

public class Lexer {
  public static List<Token> Tokenize(string input) {
    var pos = 0;
    var tokens = new List<Token>();

    while (pos < input.Length) {
      var head = () => input[pos];

      if (char.IsWhiteSpace(head())) {
        pos++;
      }
      else if (char.IsNumber(head())) {
        var val = 0;
        do {
          val += val * 10 + int.Parse(head().ToString());
          pos++;
        } while (pos < input.Length && char.IsNumber(head()));

        tokens.Add(new NumToken(val));
      }
      else {
        var sym = head() switch {
          '+' => Symbol.Plus,
          '-' => Symbol.Plus,
          '*' => Symbol.Plus,
          '/' => Symbol.Plus,
          '(' => Symbol.Plus,
          ')' => Symbol.Plus,
          _ => throw new Exception($"Invalid input: {head()}")
        };

        tokens.Add(new SymToken(sym));
        pos++;
      }
    }

    return tokens;
  }
}

public enum Op { Add, Sub, Mult, Div }
public abstract record AST {}
public sealed record Node(AST left, AST right, Op op): AST {};
public sealed record Leaf(int val): AST {};

public class Parser {
  private int pos;
  private List<Token> tokens;
  private Token head() => tokens[pos];
  private bool match(Token tk) {
    if (pos >= tokens.Count) {
      return false;
    }

    if (head() == tk) {
      pos++;
      return true;
    } else {
      return false;
    }
  }
  public Parser(List<Token> tokens) {
    this.tokens = tokens;
    this.pos = 0;
  }

  /*
  expr = term | term + term | term - term
  term = factor | factor * factor | factor / factor
  factor = num | ( expr )
  */
  public AST Parse() {
    return expr();
  }

  private AST expr() {
    var node = term();
    while(true) {
      if (match(SymToken.Plus)) {
        node = new Node(left: node, right: term(), op: Op.Add);
      }
      else if (match(SymToken.Minus)) {
        node = new Node(left: node, right: term(), op: Op.Sub);
      }
      else {
        return node;
      }
    }
  }

  private AST term() {
    var node = factor();
    while(true) {
      if (match(SymToken.Aste)) {
        node = new Node(left: node, right: term(), op: Op.Mult);
      }
      else if (match(SymToken.Slash)) {
        node = new Node(left: node, right: term(), op: Op.Div);
      }
      else {
        return node;
      }
    }
  }

  private AST factor() {
    var token = head();
    if (token is NumToken tk) {
      pos++;
      return new Leaf(tk.val);
    }
    else if (match(SymToken.LPar)) {
      var e = expr();
      if (match(SymToken.RPar)) {
        return e;
      }
    }
    throw new Exception($"Invalid Token: {head()}");
  }
}

public class Calculator
{
  public int Exec(AST ast) {
    if (ast is Node node) {
      return node.op switch {
        Op.Add => Exec(node.left) + Exec(node.right),
        Op.Sub => Exec(node.left) - Exec(node.right),
        Op.Mult => Exec(node.left) * Exec(node.right),
        Op.Div => Exec(node.left) / Exec(node.right),
        _ => throw new Exception("Unreachable"),
      };
    }
    else if (ast is Leaf leaf) {
      return leaf.val;
    }

    throw new Exception("Unreachable");
  }
}
```

### コンソールアプリの作成

次にコンソールアプリを作る。
```bash
$ cd ..
$ dotnet new console --name=Calculator.ConsoleApp # コンソールアプリのプロジェクトの作成
$ dotnet sln add ./Calculator.ConsoleApp/Calculator.ConsoleApp.csproj
$ cd ../Calculator.ConsoleApp
$ dotnet add reference ../Calculator.Core.csproj
```

内部は先程作ったライブラリを呼び出すだけの簡単なもの
```csharp
using System;
using Calculator.Core;

namespace Calculator.ConsoleApp;
public class Program {
  public static void Main() {
    while (true)
    {
      var input = Console.ReadLine();

      var tokens = Lexer.Tokenize(input);
      var ast = new Parser(tokens).Parse();
      var result = Calculator.Core.Calculator.Exec(ast);

      Console.WriteLine(result);
    }
  }
}
```

`dotnet run` でプログラムを実行できる。
```bash
$ dotnet run # プログラムの実行
```

また、ソリューションファイルがあるディレクトリで `dotnet build` を実行すると、ソリューションに含まれているすべてのプロジェクトをビルドできる。
```bash
$ cd ..
$ dotnet build # Calculator.Core と Calculator.ConsoleApp の両方がビルドされる
```

### テストの作成

次にテストを作成する
```bash
$ cd ..
$ dotnet new xunit --name=Calculator.Test # ユニットテストのプロジェクトの作成
$ dotnet sln add ./Calculator.Test/Calculator.Test.csproj 
$ cd ../Calculator.Test
$ dotnet add reference ../Calculator.Core.csproj
```

```csharp
using Xunit;
using System.Collections.Generic;
using Calculator.Core;

namespace Calculator.Test;

public class UnitTest1
{
    [Fact]
    public void LexerTest()
    {
        Assert.Equal(
            Lexer.Tokenize("1")[0],
            new NumToken(1)
        );
        Assert.Equal(
            Lexer.Tokenize("123")[0],
            new NumToken(123)
        );
    }

    [Fact]
    public void ParserTest()
    {
        var ast = new Parser(new List<Token>() {
            new NumToken(1), 
            new SymToken(Symbol.Plus),
            new NumToken(2)
        }).Parse();

        Assert.Equal(
            (ast as Node).left,
            new Leaf(1)
        );
        Assert.Equal(
            (ast as Node).right,
            new Leaf(2)
        );
        Assert.Equal(
            (ast as Node).op,
            Op.Add
        );
    }
}
```

`dotnet test` でテストを実行できる。
