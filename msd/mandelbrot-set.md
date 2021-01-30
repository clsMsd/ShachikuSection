# マンデルブロ集合とフラクタル

## マンデルブロ集合とは？
マンデルブロ集合とは、複素平面上の以下の画像(の黒い部分の図形)のような集合である。  
<img src="https://upload.wikimedia.org/wikipedia/commons/2/21/Mandel_zoom_00_mandelbrot_set.jpg" />

マンデルブロ集合は  
複素平面上の原点に対して z → z^2 + c (z, c: 複素数) という変換
(以下ではこの変換をMB変換と呼ぶ。一般的な名称ではないので注意)を無限回繰り返した際に、  
原点が無限遠点に発散しないような c の集合である  
(黒以外の部分は収束の速さの違いによって色分けされていることが多い)。

例えば、c = 0　の場合これは単位円盤(|z| <= 1 を満たす点の集合)であることが直ぐに分かる。  

逆に c を固定して変換の初期値を動かした場合に、変換を無限界繰り返した際に
無限遠点に発散しないような z の集合を充填ジュリア集合という。  

マンデルブロ集合の一部を拡大してみると、集合の一部に集合全体と似たような図形が現れることがよくある。  
(ちなみにgoogleでマンデルブロ集合で検索するとマンデルブロ集合を自由に拡大/縮小できる)。  
このように、ある図形が一部にその図形全体と相似な部分を持つとき、そのような図形を *フラクタル* と呼ぶ  
(これはあくまで直感的な説明であって、数学的に厳密な定義はもっと複雑である)。  
フラクタルの例としては、コッホ雪片 や シェルピンスキーのギャスケット などが有名である。  

マンデルブロ集合はフラクタル図形の中でも特異的であり、様々な面白い特徴を持っている。  
先程マンデルブロ集合を拡大すると集合全体と似たような図形が現れると書いたが、実はマンデルブロ集合には全体と全く同じ形の部分は存在せず、似たような形をしている部分はすべて微妙に異なった形をしていることが知られている。  
また、マンデルブロ集合を拡大すると集合本体から切り離された「飛び地」のようなものが見つかることがあるが、  
実はマンデルブロ集合は単連結であることが証明されている
(つまり、飛び地のように見える部分も必ずどこか目に見えないようなめっっちゃ細い領域で本体とつながっている）。  

## マンデルブロ集合を描画する
demo: https://masudas.github.io/mandelbrot-set-playground/

これくらいのアプリなら素のJavaScriptで書いて雑にhtmlを読み込むというやり方でもいいのだが、  
折角なので今時のweb開発らしくTypeScript + Webpackでやっていく。

### 環境構築
プロジェクトのディレクトリを作ってもろもろの依存関係をインストールする。

```bash
$ mkdir mandelbrot-set-playground
$ cd mandelbrot-set-playground
$ npm init
$ npm install typescript webpack webpack-cli webpack-dev-server ts-loader html-webpack-plugin html-loader ejs-plain-loader
$ ./node_modules/.bin/tsc --init
$ mkdir src
```

/src以下にとりあえず仮の `app.ts`と`index.ejs` を置く。

/src/app.ts
```typescript
console.log("Hello World")
```

/src/index.ejs (後々のためにejs形式にしておく)
```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>Mandelbort Set Playground</title>
  </head>
  <body>
    <div id="app"></div>
  </body>
</html>
```

おらおらっとWebpackの設定を書く
```javascript
const path = require("path");
const HtmlWebpackPlugin = require("html-webpack-plugin");

const src = path.resolve(__dirname, "src");
const dist = path.resolve(__dirname, "dist");

module.exports = {
  mode: "development",
  entry: path.join(src, "app.ts"),
  output: {
    path: dist,
    filename: "bundle.js",
  },
  module: {
    rules: [
      {
        test: /\.ts$/,
        exclude: /node_modules/,
        loader: "ts-loader"
      },
      {
        test: /\.ejs$/,
        exclude: /node_modules/,
        use: [
          'html-loader',
          "ejs-plain-loader",
        ]
      }
    ],
  },
  resolve: {
    extensions: [".js", ".ts"]
  },
  plugins: [
    new HtmlWebpackPlugin({
      template: path.join(src, "index.ejs")
    }),
  ]
}
```

package.jsonも書き換える (`start`, `build`, `serve` を追加)
```json
{
  ...
  "scripts": {
    "test": "echo \"Error: no test specified\" && exit 1",
    "start": "npm run serve",
    "build": "webpack",
    "serve": "webpack-cli serve --mode development"
  },
  ...
}
```

`npm run build`で正常にビルドできること、`npm start`でサーバーが立ち上がり、consoleに`Hello World`と出力されることを確認する。

### アフィン変換

まずマンデルブロ集合を描画する前に、座標変換の仕組みを作ることにする。
普通数学で使う座標系はy軸が上向き(上方向に進むとyの値が増える)がcanvasの座標系ではy軸が下向き(下方向に進むのyの値が増える)なので、そのままでは図形の上下が反転してしまう
(ただしマンデルブロ集合は上下対称なので今回はこれは問題にならない)。
またマンデルブロ集合はxの値が -2 ~ +1 程度の範囲に分布しているが、これをcanvasに直接持っていくとマンデルブロ集合全体でも数ピクセル程度しか描画されないことになるので、canvasの大きさに合わせて適度に拡大する必要がある。

2次元の座標変換というと2x2行列を使った線形変換を思い浮かべる人が多いかもしれないが、線形変換では原点の移動ができない。
そこで、原点の移動のために1次元増やした次のような 3x3の行列を使った座標変換がよく使われる
(このような線形変換 + 原点の移動の変換のことをアフィン変換という)。  

()
ただし、
(x, y): 変換前の座標
(X, Y): 変換後の座標

行列の掛け算を知らないという今時の高校生のために展開して書くと次のようになる。  
X = ax + by + c  
Y = dx + ey + f  

これで一般の変換が定義できたので、今回使うパラメータについて考える。  
まず今回変換前・変換後ともにx座標とy座標は直交で回転もしないので b = d = 0 であることが分かる。  
また、xとyで長さの比率(アスペクト比)も変えないので |a| = |e|, y軸が反転することを考えると e = -a である。  
以上から上の式をまとめると次のようになる。  

X =  ax + c  
Y = -ay + f  

あとは残りのパラメータだが、cとfがゼロだと 複素平面の原点=キャンバスの原点 となる。
キャンバスの原点は左上なので、このままでは第一象限しかキャンバスに映らない。  
とりあえず 複素平面の原点=キャンバスの中心になって欲しいので、キャンバスの幅と高さ(今回は両方800pxにする)の半分だけxとyをずらせば良い。

c = 0.5 * キャンバスの幅 = 400  
f = 0.5 * キャンバスの高さ = 400  

あとは全体の拡大率のaだが、とりあえず 400倍としておく(これで複素平面上の[-1, 1]の区間がCanvasいっぱいになる)。  

#### class による実装

```typescript
type Point = { x: number, y: number }

class AffineTransformer {
  constructor(
    private matrix: [[number, number, number], [number, number, number]]
  ) {}

  transform({ x: _x, y: _y }: Point): Point {
    const [[a, b, c], [d, e, f]] = this.matrix;
    return { x: a * _x + b * _y + c, y: d * _x + e * _y + f }
  }
}

const canvasTF = new AffineTransformer([[400, 0, 400], [0, -400, 400]])
```

#### 高階関数による実装

```typescript
type Point = { x: number, y: number }

const createAffineTransform = (matrix: [[number, number, number], [number, number, number]]) => ({ x: _x, y: _y }:Point): Point => {
  const [[a, b, c], [d, e, f]] = matrix;
  return { x: a * _x + b * _y + c, y: d * _x + e * _y + f }
}

const canvasTF = createAffineTransform([[400, 0, 400], [0, -400, 400]])
```

#### オブジェクト指向と高階関数
アフィン変換という同じ機能についてクラスによる実装と高階関数による実装の両方
オブジェクトというのはメソッドだけに着目すると関数の集まりといえる。  
コンストラクタはオブジェクトを作る関数なので、つまり関数(の集まり)を返す関数、すなわち高階関数であると考えることもできる。  
例えば、今回作った`AffineTransformer`クラスは`transform`という一つのメソッドだけを持つクラスなので、  
`AffineTransformer`クラスのコンストラクタは変換の指定に必要なパラメータを受け取って具体的な変換を行う関数を返す高階関数であるといえる。   
(実際Javaのラムダ式は無名クラスを使って実装されているとかなんとか聞いたことがあるが、詳細は知らないので気になる人は各自で調べて栗)  

関数がファーストクラスオブジェクトでない言語が主流だった時代においてオブジェクト指向が持て囃されたのは、  
オブジェクト指向言語が実質的に関数をファーストクラスオブジェクトとして扱える言語だったからというのは大きな理由だったのだろう  
(オブジェクトを受け取る・返す関数は実質的に関数を受け取る・返す関数であるとも言える)。  

なので関数をファーストクラスオブジェクトとして扱うことができ、ラムダ式などで無名関数を簡単に扱えるな言語が主流になった現代では  
オブジェクト指向のありがたみが薄れてしまっているというのも無理のない話である  
(それでもオブジェクト指向の利点はいろいろあると思うのだがその話はまた今度で…)。  

### MB変換の実装

```typescript
class Complex {
  constructor(
    public re: number,
    public im: number
  ) {}

  add(rhs: Complex): Complex { return new Complex(this.re + rhs.re, this.im + rhs.im) }
  mult(rhs: Complex): Complex { return new Complex(this.re * rhs.re - this.im * rhs.im, this.re * rhs.im + this.im * rhs.re) }
  sqrd(): Complex { return this.mult(this) } 
  abs(): number { return this.re * this.re + this.im * this.im }
  toPoint(): Point { return ({ x: this.re, y: this.im }) }
}

const MBtrasnform = (z: Complex, c: Complex): Complex => z.sqrd().add(c)

const isInnerMBSet = (c: Complex): boolean => {
  const LOOP_MAX = 300
  let z = new Complex(0, 0)
  for (let i = 0; i < LOOP_MAX; i++) {
    z = MBtransform(z, c)
    if (z.abs() > 2) { return false }
  }
  return true
}
```

### canvasの描画
あとは各座標についてマンデルブロ集合に含まれるかどうかの判定を行えばよいのだが、ここままでは困ったことになる。  
今回キャンバスの大きさは幅800pxなので描画できる範囲は 0 <= x <= 800 なのだが、これが複素平面上でどの範囲に対応するかが分からない。  
これを計算するために、先程作った複素平面からキャンバスへの変換に対応する`逆変換`を求める。  
3x3の逆行列ならオラオラっと求めてもよいのだが、今回は楽をしてWolfram Aplphaに頼ることにする。  
https://www.wolframalpha.com/input/?i=inv+%7B%7Ba%2C+b%2C+c%7D%2C+%7Bd%2C+e%2C+f%7D%2C+%7B0%2C+0%2C+1%7D%7D&lang=ja

クラスの場合、変換を表すオブジェクトに追加で逆変換を表すメソッドをもたせれば良い。
```typescript
class AffineTransformer {
  constructor(
    private matrix: [[number, number, number], [number, number, number]]
  ) {}

  transform({ x: _x, y: _y }: Point): Point {
    const [[a, b, c], [d, e, f]] = this.matrix;
    return { x: a * _x + b * _y + c, y: d * _x + e * _y + f }
  }
  inverse({ x: _x, y: _y }: Point): Point {
    const [[a, b, c], [d, e, f]] = this.matrix;
    const det = a * e - b * d
    return { x: (e*_x - b*_y - c*e + b*f)/det, y: (-d*_x + a*_y + c*d - a*f)/det }
  }
}
```

高階関数の場合、指定された行列に対する逆変換を求める高階関数を作る。
```typescript
const createAffineTransform = (matrix: [[number, number, number], [number, number, number]]) => ({ x: _x, y: _y }:Point): Point => {
  const [[a, b, c], [d, e, f]] = matrix;
  return { x: a * _x + b * _y + c, y: d * _x + e * _y + f }
}
const createInverseAffineTransform = (matrix: [[number, number, number], [number, number, number]]) => ({ x: _x, y: _y }:Point): Point => {
  const [[a, b, c], [d, e, f]] = matrix;
  const det = a * e - b * d
  return { x: (e*_x - b*_y - c*e + b*f)/det, y: (-d*_x + a*_y + c*d - a*f)/det }
}

const canvasTransform = createAffineTransform([[400, 0, 400], [0, -400, 400]])
const inverseCanvasTransform = createInverseAffineTransform([[400, 0, 400], [0, -400, 400]])
```

ただし、これだと変換と逆変換の対応が分かりづらいので、変換と逆変換を1つのオブジェクトに持たせてもよい。  
```typescript
const createAffineTransform = (matrix: [[number, number, number], [number, number, number]]): {
  transform: (p: Point) => Point,
  inverse: (p: Point) => Point,
} => {
  const [[a, b, c], [d, e, f]] = matrix;
  const det = a * e - b * d;
  return {
    transform: ({ x: _x, y: _y }: Point) => ({ x: a * _x + b * _y + c, y: d * _x + e * _y + f }),
    inverse: ({ x: _x, y: _y }: Point) => ({ x: (e*_x - b*_y - c*e + b*f)/det, y: (-d*_x + a*_y + c*d - a*f)/det }),
  }
}

const canvasTF = createAffineTransform([[400, 0, 400], [0, -400, 400]])
```
こうすると殆ど実質的にオブジェクト指向では？という感じになる。

あとは実際にマンデルブロ集合を描画する関数を作る。
```typescript
const renderMB = (context: CanvasRenderingContext2D, expansionRate: number) => {
  const CanvasWidth = context.canvas.width
  const CanvasHeight = context.canvas.height
  const canvasTF = createAffineTransform([[expansionRate, 0, CanvasWidth/2], [0, -expansionRate, CanvasHeight/2]])

  const { x: edge_x1, y: edge_y1 } = canvasTF.inverse({ x: 0, y: 0 })
  const { x: edge_x2, y: edge_y2 } = canvasTF.inverse({ x: CanvasWidth, y: CanvasHeight })

  // 座標変換の結果、符号が反転する場合のための対応
  const max_x = Math.max(edge_x1, edge_x2)
  const max_y = Math.max(edge_y1, edge_y2)
  const min_x = Math.min(edge_x1, edge_x2)
  const min_y = Math.min(edge_y1, edge_y2)

  const delta_x = (max_x - min_x) / CanvasWidth
  const delta_y = (max_y - min_y) / CanvasHeight

  for (let x = min_x; x < max_x; x += delta_x) {    
    for (let y = min_y; y < max_y; y += delta_y) {
      if (isInnerMBSet(new Complex(x, y))) {
        const { x: _x, y: _y } = canvasTF.transform({ x, y })
        context.fillRect(_x, _y, 1, 1)
      }
    }
  }
}

function main() {
  const CanvasWidth = 800
  const CanvasHeight = 800
  const canvas = document.createElement("canvas")
  canvas.width = CanvasWidth
  canvas.height = CanvasHeight

  document.getElementById("app").appendChild(canvas)

  renderMB(canvas.getContext())
} 

main();
```
ここではJavaScriptでCanvasを生成した。

### TypeScriptとejs
後々の拡張のために、`index.ejs`でcanvasを作るようにする。  
その際にhtml(ejs)とTypeScriptで値の共有ができると便利である  
(canvasの`id`や幅、高さなど。特にid名を共有できれば`getElementById`の引数を間違えてnullが返ってくるなどの事故が無くなるので嬉しい)。  
こういうときはwebpackでビルドする際に各ファイルに値を注入するというやり方が一般的  
(環境変数の埋め込みなど)なのだが、今回は少し困ったことがある。  

Webpackで値を注入するとTypeScriptからは型が付かないので、`declare`で予め変数を宣言しておくか、  
型は無いものとして諦めるかということになるが、前者の方法は定数の二重管理が発生するし、  
後者の方法ではそもそもID名のタイプミスなどを避けるためにエディタの補完が使える嬉しいという話なのに、  
まさにエディタで補完したいところで型が無くて補完が使えないとなったら残念極まりない。  

Webpackからindex.ejsとapp.tsに値を注入する図
```
webpack -> index.ejs
        └> app.ts 
```

定数を定義するJavaScriptのファイルを用意して、Webpackは`CommonJS`形式のモジュールしか対応していない  
(なんか上手いことすれば`ESmodule`形式でもいけるかもしれないが少なくとも自分が試した範囲では駄目だった)。  
一方でTypeScriptでモジュールを読み込む場合は`ESModule`形式で読み込みたい  
(TypeScriptで`CommonJS`形式を使うこともできなくはないが美しくない)。  
しかし単一のファイルで`CommonJS`と`ESModule`の両方の形式に対応することはできない。  

定数を定義するJavaScriptのファイル(constants.js)をwebpackとapp.tsの両方で読み込む図
```
constants.js -> webpack -> index.ejs
             └> app.ts 
```

そこで、TypeScriptのresolveJsonModuleという機能を使う。  
これはJsonファイルをモジュールとして読み込むTypeScriptの機能である。
この機能を使うためには、tsconfig.jsonに`resolveJsonModule: true`の行を加える必要がある。  

constants.json
```json
{
  "Canvas": {
    "ID": "canvas-area",
    "Width": 1200,
    "Height": 800
  }
}
```

app.ts
```typescript
import Constants from "./constants.json"

...

function main() {
  const expansionRate = 400
  const canvas = document.getElementById(Constants.Canvas.ID) as any

  renderMB(canvas.getContext("2d") as CanvasRenderingContext2D, expansionRate)
}

main();
```

これでJsonファイルを読み込んでオブジェクトとして使うことができる(しかもちゃんと型が付く)。  
ejsの方は、普通に`require`で読み込めばよい。

```ejs
<%
const Constants = require("./constants.json")
const { Canvas } = Constants
%>
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>Mandelbort Set Playground</title>
  </head>
  <body>
    <div id="app">
      <canvas
        id="<%= Canvas.ID %>"
        width="<%= Canvas.Width %>"
        height="<%= Canvas.Height %>">
      </canvas>
    </div>
  </body>
</html>
```

### 拡大・縮小・移動機能の実装
好きなところを拡大縮小できるように、機能を追加しよう。

```html
<%
const Constants = require("./constants.json")
const { Canvas, Inputs } = Constants
%>
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
    <title>Mandelbort Set Playground</title>
  </head>
  <body>
    <div id="app">
      <canvas
        id="<%= Canvas.ID %>"
        width="<%= Canvas.Width %>"
        height="<%= Canvas.Height %>">
      </canvas>
      <br/>
      中心のx座標:<input id="<%= Inputs.CenterX.ID %>" type="number" value="0">
      中心のy座標:<input id="<%= Inputs.CenterY.ID %>" type="number" value="0">
      拡大率:<input id="<%= Inputs.ExpansionRate.ID %>" type="number" value="400">
      <button onclick="onClickReload()">更新</button>
    </div>
  </body>
</html>
```

```typescript
const renderMB = (context: CanvasRenderingContext2D, centerPoint: Point, expansionRate: number) => {
  const CanvasWidth = context.canvas.width
  const CanvasHeight = context.canvas.height
  context.clearRect(0, 0, CanvasWidth, CanvasWidth);

  const canvasTF = new AffineTransformer(
    [[expansionRate, 0, CanvasWidth/2 - expansionRate * centerPoint.x], [0, -expansionRate, CanvasHeight/2 + expansionRate* centerPoint.y]]
  )

  const { x: edge_x1, y: edge_y1 } = canvasTF.inverse({ x: 0, y: 0 })
  const { x: edge_x2, y: edge_y2 } = canvasTF.inverse({ x: CanvasWidth, y: CanvasHeight })

  const max_x = Math.max(edge_x1, edge_x2)
  const max_y = Math.max(edge_y1, edge_y2)
  const min_x = Math.min(edge_x1, edge_x2)
  const min_y = Math.min(edge_y1, edge_y2)

  const delta_x = (max_x - min_x) / CanvasWidth
  const delta_y = (max_y - min_y) / CanvasHeight

  for (let x = min_x; x < max_x; x += delta_x) {    
    for (let y = min_y; y < max_y; y += delta_y) {
      if (isInnerMBSet(new Complex(x, y))) {
        const { x: _x, y: _y } = canvasTF.transform({ x, y })
        context.fillRect(_x, _y, 1, 1)
      }
    }
  }
}


function onClickReload() {
  const center_x = Number.parseInt((document.getElementById(Constants.Inputs.CenterX.ID) as HTMLInputElement).value)
  const center_y = Number.parseInt((document.getElementById(Constants.Inputs.CenterY.ID) as HTMLInputElement).value)
  const expansionRate = Number.parseInt((document.getElementById(Constants.Inputs.ExpansionRate.ID) as HTMLInputElement).value)

  const canvas = document.getElementById(Constants.Canvas.ID) as any

  renderMB(canvas.getContext("2d") as CanvasRenderingContext2D, { x: center_x, y: center_y }, expansionRate)
}

function main() {
  document.getElementById(Constants.Inputs.Reload.ID)!.onclick = onClickReload

  const expansionRate = 400
  const canvas = document.getElementById(Constants.Canvas.ID) as any

  renderMB(canvas.getContext("2d") as CanvasRenderingContext2D, { x: 0, y: 0 }, expansionRate)
}
```

### Github Page にデプロイする
```
$ npm install gh-pages
```

package.json
```
"deploy": "npm run build; gh-pages -d dist"
```

## 参考資料
- Dimensions 6章 https://www.youtube.com/watch?v=lmoAmV1eckg
- Dimensions 第5章，第6章: 複素数 http://www.dimensions-math.org/Dim_CH5_JP.htm
