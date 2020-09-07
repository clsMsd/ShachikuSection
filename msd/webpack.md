# Webpack入門

## Webpackとは？
> webpack is a module bundler. Its main purpose is to bundle JavaScript files for usage in a browser,  
> yet it is also capable of transforming, bundling, or packaging just about any resource or asset.  
> ([https://github.com/webpack/webpack] より引用)

## Webpackの無いJavaScript開発
Webpackが何をするかを説明する前に、Webpackがなかった頃のWeb開発がどのようなものだったかを説明する。  

### ES5 時代
ES5 時代の昔のJavaScriptにはモジュールの概念が無く、  
スクリプトを複数ファイルに分割したい場合は、htmlから分割したファイルをそれぞれ読み込んで実行するだけだった。  

```html
<!-- index.html -->
<html>
   <head></head>
   <body>
      <div id="app"></div>
      <script src="foo.js"></script>
      <script src="bar.js"></script>
   </body>
</html>
```

このため依存関係があるファイルの読み込む順番を間違えないように気をつける必要があった。  
名前空間のような概念もなく、スクリプトを実行するとその中で定義されている変数や関数はグローバルスコープに直接ぶち撒けられるという動作をしていた。  
当然変数名が衝突するとヤバいことになるので、開発者はスクリプト全体を匿名関数でくくってそれを即実行する(即時関数)という工夫をしていた。  

古のJavaScriptの書き方
```javascript
// スクリプト全体を即時関数で囲む
(function () {
   console.log("foo start");

   var hoge = 3; // 関数内のローカル変数になるので外から参照される心配がなく、名前衝突の問題もない
   console.log(hoge); 

   // 外部から参照したい変数や関数は、window のメンバに生やす
   window.foo = "foooooo";
   window.add = function (a, b) {
      return a + b;
   }
})();
```

### CommonJS と AMD
やがてC10K問題対策などでサーバーサイドJavaScriptが注目され始めた。    
ブラウザ外のJavaScript実行環境の仕様としてCommonJSというものが策定された。  
このCommonJSでモジュール機能の仕様も策定され、主にNode.jsで使われるようになった  
(`module.exports`と`require`でやるアレ)。  

これはあくまでブラウザ外の実行環境の話なので、ブラウザのネイティブの機能としてこのようなモジュール機能が実装されるわけではない。  
が、ブラウザでもCommonJSと同様なモジュールが使いたいという需要があり、
Browserify、AMD、RequireJS といったツールやフレームワークが使われるようになった。  

- Browserify: Webpackの進化前。ビルド時に静的にモジュールの依存関係を解決する。  
- AMD: Asynchronous Module Definitionの略。ブラウザでJavaScriptのモジュールを扱うための仕様。  
  その名のとおりモジュールを非同期で読み込む。  
  モジュールの定義側は独自構文を使う必要があったが利用者側はCommonJSと同じように`require`でモジュールを読み込むことができる。  
- RequireJS: AMDの実装の一つ。  

### ES modules
このままではアカンやろと皆思ったのか、ES2015(ES6)ではついにJavaScript(ECMAScript)の標準仕様にモジュール機能が盛り込まれることとなった。  

```javascript
// lib.js
export default function() {
   console.log("lib.js");
}

// app.js
import Lib from "./lib.js";
Lib();
```

これですべての問題は解決した… ということはなかった。  
主な問題点として以下のようなものがある(あった)。  
- モジュールが同期的に読み込まれるので遅い  
  (スクリプトの実行中に制御が`import`の行に到達した時点でリクエストが発生し、別のスクリプトをロードして実行を始める  
  (ただし`import`文は実行時にホスティングされるので、`import`の前に何かが実行されることはない)。  
  読み込んだスクリプトが更に別のスクリプトを`import`していた場合などを考えるとヤバヤバなことが容易に理解できるだろう)
- ES2015 の規格制定時点ではまだブラウザネイティブの機能としてまだサポートされていなかった(それはそう)。
  さらに IE11対応 のことを考えると...
- モジュールの方も CommonJS形式で書いていたものを ES modules形式に書き直す必要がある
- `npm install` したパッケージをどうやって参照する？(`node_modules`を丸ごとサーバーにアップする？？？)

### そして Webpack へ...
- 依存関係を静的に解決して単一のjsファイルにしてくれる
   - js以外にCSSや画像ファイルなどをバンドルすることもできる
      - 画像はbase64でエンコードするので、サイズが大きいと逆に遅くなる。  
        小さくてたくさんあるアイコンなどの画像を1ファイルにまとめるという場合は速くなる。  
   - 逆に複数のファイルに分割することもできる(Code Splitting)
- CommonJS形式, ES moduel形式のどちらでも使える
- `import`で指定したパッケージを`node_modules`から探してきて一緒にバンドルしてくれる
- バンドルの際に`import`したけど使ってないモジュールなどを削除してくれる
- バンドルの際にローダーやプラグインでいろいろなタスクを実行することができる
   - babelでES2015→ES5のトランスパイルとか
   - tscでTypeScript->JavaScriptのトランスパイルとか
   - babelでJSXのトランスパイルとか
   - Vueの単一ファイルコンポーネントのトランスパイルとか
   - Sassのコンパイルとか
- バンドルの際にコードのminifyや難読化もできる
- ファイルの変更を検知した自動的ビルドや開発用サーバーなどの便利機能も入ってる

### 余談: CommonJSとESModuleの違い
ここまでの説明を見ると、  
「CommonJS形式のモジュールがサーバーでもブラウザでもそこそこ普及していたんだから、それをJavaScriptの正式な仕様に取り込めばええでんがな」  
と思うかもしれない。  
しかし、世の中そう単純なものではない。  
CommonJS形式とESModule形式には単純な書き方の違いというレベルではない本質的な違いがある。  

CommonJS形式のモジュールは `require`という *関数* を使ってロードするので、  
原理的に依存関係を静的に解決できない場合がある。  

```javascript
var src = Math.random() > 0.5 ? "./foo.js" : "./bar.js";

var Lib = require(src); // foo.js と bar.js のどちらがロードされるかは実行時にならないと分からない

if (Math.random() > 0.5) {
   var Foo = require("./foo.js"); // そもそもモジュールのロードが必要かどうかさえ実行時にならないと分からない
   Foo.foo();
}
```

CommonJSがなぜこのような仕様になったかは分からない(調べるのが面倒なので)が、考えられる理由としては次のようなことが挙げられる
- CommonJSはあくまでJavaScriptを書く上での共通の仕様であって、JavaScriptのスーパーセットとなる別言語ではない  
  したがってJavaScriptに勝手に新しい文法を追加することはできない  
  (そもそもnode.jsはchromeのV8エンジンを使っているので、JavaScriptから文法レベルで変わってしまうとV8にパッチを当てる必要がある)
- そもそもサーバーで動作する前提なので、スクリプトを動的にロードしてもそこまで時間がかからない  
  (JITコンパイルのことなどを考えるとまた違ってくるかもしれないが、リモートにあるスクリプトをhttpで読み込んでくる時間を考えたら誤差のようなもの)  

一方で、ESModuleでは`import`は予約語になっておりトップレベルにしか書くことができず、`from`以降の文字列([ModuleSpecifier](https://www.ecma-international.org/ecma-262/10.0/index.html#prod-ModuleSpecifier)という)は  
文字列リテラルでなければならないと定められているので、必ず依存関係を静的に解決できるようになっている。  
(モジュールを動的にロードしたい場合は`import`関数を使う)

正しいimport
```javascript
import Foo from "./foo.js"; // import するモジュールは文字列リテラルでしか指定できない
```

間違ったimport
```javascript
const bar = "./bar.js";
import Bar from bar; // 実行時エラー (ModuleSpecifierが文字列リテラルでない)

if (Math.random() > 0.5) {
   import Foo from "./foo.js"; // 実行時エラー (トップレベルでないところでimportしている)
}
```

これはJavaScriptの言語仕様そのものとして取り入れられるからこそ実現される特徴である。  

## 環境構築
```
$ mkdir sample
$ cd sample
$ npm init
$ npm install --save-dev webpack webpack-cli
```

## とりあえず動かす
webpackはデフォルトでは実行中のディレクティから `webpack.config.js` というファイルを探してきて、  
そこに書かれている設定をもとにビルドを行う。  

たとえば、次のような構成のプロジェクトがあったとする。  

ディレクトリ
```
sample
├─ node_modules
├─ app.js 
├─ lib.js 
├─ package.json
└─ webpack.config.js
```

lib.js
```javascript
export function foo() {
   console.log("foo");
}
```

app.js
```javascript
import { foo } from "./lib";

foo();
```

webpack.config.js
```javascript
module.exports = {
   mode: "development",
   entry: "./app.js",
   output: {
      filename: "bundle.js",
   }
}
```

この状態で、`webpack`コマンドを実行すると、プロジェクトのディレクティに`dist`というディレクティが作られ  
その中にビルド結果である `bundle.js` が出力される。  
なお、普通このようなツールはグローバルにインストールせずプロジェクトの`node_modules` 以下にインストールした方がよい。  

```bash
$ ./node_modules/.bin/webpack
Hash: ce4574710a97d87648e1
Version: webpack 4.42.0
Time: 107ms
Built at: 03/18/2020 4:52:37 PM
    Asset       Size  Chunks             Chunk Names
bundle.js  970 bytes       0  [emitted]  main
Entrypoint main = bundle.js
[0] ./app.js + 1 modules 90 bytes {0} [built]
    | ./app.js 41 bytes [built]
    | ./lib.js 49 bytes [built]
$ node ./dist/bundle.js
foo
```

さらに、ビルド時にはwebpackコマンドをそのまま実行するのではなく、npm script経由でビルドすることが多いのでそうしよう。  
(ビルドにどのツールを使うかに関係なく`npm run build`を実行すればビルドできるという状態の方が分かりやすい)

package.json 
```json
{
   ...
   "scripts": {
      ...
      "build": "webpack"
   }
}
```

これで`npm run build` と打てばビルドできるようになる。  

## webpack.config.js 
- mode
- entry
- output
- resolve
- module
   - rules
- plugins
- optimization

### mode
`development`か`production`を指定する(デフォルトでは`production`)  
`production`の場合はなんかいろいろな最適化が勝手に有効になるらしい。

### entry
エントリーポイントを指定する。  

### output
出力されるビルド結果のファイルの設定を行う。  

### module
loaderの設定を行う。  

## 例. React
例として create-react-app 無しで Reactアプリをビルド・実行してみよう。  

まずは必要なパッケージをインストールして、ソースとビルド成果物を入れるディレクティを作っておく。  
```
$ npm install --save react react-dom
$ npm install --save-dev webpack webpack-cli babel babel-loader @babel/core @babel/preset-env @babel/preset-react
$ mkdir src dist
```

Reactアプリを書く。  

src/app.jsx
```javascript 
import React from 'react';
import { render } from 'react-dom';

const App = () => (<p>Hello React and Webpack!</p>);

render(<App/>, document.getElementById('app'));
```

babelの設定を書く。  

.babelrc
```
{
  "presets": [
    "@babel/preset-env", "@babel/preset-react"
  ]
}
```

webpackの設定を書く。  

webpack.config.js
```javascript
const path = require("path");

const src = path.resolve(__dirname, "src");
const dist = path.resolve(__dirname, "dist");

module.exports = {
    mode: "development",
    entry: path.join(src, "/app.jsx"),
    output: {
        path: dist,
        filename: "bundle.js",
    },
    module: {
        rules: [
            {
                test: /\.jsx$/,
                exclude: /node_modules/,
                loader: "babel-loader"
            }
        ],
    },
    resolve: {
        extensions: [".js", ".jsx"]
    }
}
```

package.jsonを編集しておく(略)。  

これでビルドが通るはずなので、`npm run build`を実行する。  

```bash
$ npm run build

> reactwp@1.0.0 build C:\sandbox\reactwp
> webpack

Hash: adf43237507fe6822b12
Version: webpack 4.42.0
Time: 1694ms
Built at: 2020/03/18 17:34:52
    Asset     Size  Chunks             Chunk Names
bundle.js  976 KiB    main  [emitted]  main
Entrypoint main = bundle.js
[./src/app.jsx] 192 bytes {main} [built]
    + 11 hidden modules
```

ビルドが成功すると、`dist/bundle.js` が出力される。  

`dist`以下に`bundle.js`を読み込んで実行するhtmlをおいて、ブラウザからそのhtmlを開いてみよう。  

dist/index.html
```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>React Test</title>
  </head>
  <body>
    <div id="app"></div>
    <script src="bundle.js"></script>
  </body>
</html>
```

画面に Hello React and Webpack! と表示されるはずである。  

さらに、htmlのバンドルとサーバーの起動までをwebpackで行うようにしてみよう。  

パッケージをインストールする。  
```bash
$ npm install --save-dev webpack-dev-server html-webpack-plugin
```

`src`以下に`index.html`を置く。

```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>React Test</title>
  </head>
  <body>
    <div id="app"></div>
    <!-- スクリプトの読み込みはwebpackでバンドルする際に勝手に作られるので消しておく -->
  </body>
</html>
```

webpack.config.jsを書き換える。
```javascript

const path = require("path");
const HtmlWebpackPlugin = require("html-webpack-plugin");

const src = path.resolve(__dirname, "src");
const dist = path.resolve(__dirname, "dist");

module.exports = {
    mode: "development",
    entry: path.join(src, "app.jsx"),
    output: {
        path: dist,
        filename: "bundle.js",
    },
    module: {
        rules: [
            {
                test: /\.jsx$/,
                exclude: /node_modules/,
                loader: "babel-loader"
            }
        ],
    },
    resolve: {
        extensions: [".js", ".jsx"]
    },
    plugins: [
        new HtmlWebpackPlugin({
            template: path.join(src, "index.html")
        })
    ]
}
```

package.jsonを書き換える。

```json
{
   ...
   "scripts": {
      ...
      "build": "webpack",
      "serve": "webpack-dev-server"
  },
}
```

これで `npm run serve` を実行するとサーバーが起動する。  

## 参考資料
webpack.config.js 最小設定 [https://qiita.com/mizchi/items/2e614d184fe2577f8256]
Babelとwebpackを使ってES6でReactを動かすまでのチュートリアル [https://qiita.com/akirakudo/items/77c3cd49e2bf39da79dd]
