# マンデルブロ集合 つづき

前回はTypeScriptでマンデルブロ集合描画プログラムを作ったが、  
最近のイケてるWeb開発者はwasmを使うらしいので、やっていく。  

## 1. Rust + wasm

### 下準備
ツールチェインをインストールしてプロジェクトを作る。

```bash
$ rustup self update
$ rustup update
$ cargo install wasm-pack
$ cargo install cargo-generate
$ npm init rust-webpack mandelbrot-set-playground-wasm
```

正常にプロジェクトが生成できれば、`npm build`でビルドが、`npm start`でサーバーが起動するはずなので、  
問題が無いか確認する。  

次にCargo.toml(Rust版のpackage.jsonのようなもの)を編集して必要なcrateを使えるようにする。  
Cargo.tomlの `[dependencies.web-sys]` のセクションを編集
```toml
[dependencies.web-sys]
version = "0.3.22"
features = [
    "console",
    "CanvasRenderingContext2d",
    "Document",
    "Element",
    "HtmlCanvasElement",
    "Window",
]

[dependencies.js-sys]
version = "0.3.47"
default-features = false 

[dependencies.num-complex]
version = "0.3"
default-features = false 
```

### 作ってみる
/src/lib.rs の `main_js` がエントリーポイントになるので、オラオラっと処理を書いていく。

```rust
use std::f64;
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys;
use num_complex;

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    // This provides better error messages in debug mode.
    // It's disabled in release mode so it doesn't bloat up the file size.
    #[cfg(debug_assertions)]
    console_error_panic_hook::set_once();

    print("start");

    // Your code goes here!
    let document = web_sys::window().unwrap().document().unwrap();
    let canv = document.get_element_by_id("canvas").unwrap().dyn_into::<web_sys::HtmlCanvasElement>().unwrap();
    let context = canv
        .get_context("2d")
        .unwrap()
        .unwrap()
        .dyn_into::<web_sys::CanvasRenderingContext2d>()
        .unwrap();

    let begin = js_sys::Date::now();

    render_mbset(context, 400.);

    let end = js_sys::Date::now();

    print(format!("render complete: {}", end - begin).as_str());

    Ok(())
}

fn print(s: &str) {
    web_sys::console::log_1(&JsValue::from_str(s))
}

type c64 = num_complex::Complex<f64>;

struct Point {
    x: f64, y: f64
}

impl Point {
    fn to_c64(&self) -> c64 {
        c64::new(self.x, self.y)
    }
}

struct AffineTransformer {
    a: f64, b: f64, c: f64,
    d: f64, e: f64, f: f64
}

impl AffineTransformer {
    fn transform(&self, p: Point) -> Point {
        Point {
            x: self.a * p.x + self.b * p.y + self.c,
            y: self.d * p.x + self.e * p.y + self.f
        }
    }
    fn inverse(&self, p: Point) -> Point {
        let det = self.a * self.e - self.b * self.d;
        Point {
            x: (self.e * p.x - self.b * p.y - self.c * self.e + self.b * self.f) / det,
            y: (-self.d * p.x + self.a * p.y + self.c * self.d - self.a * self.f) / det,
        }
    }
}

pub fn mb_transform(z: c64, c: c64) -> c64 { z * z + c }
fn is_inner_mbset(c: c64) -> bool {
    const LOOP_MAX: u32 = 1000;
    let mut z = c64::new(0., 0.);
    for _ in 1..LOOP_MAX {
        z = mb_transform(z, c);
        if z.norm_sqr() > 2. { return false }
    }
    return true
}

fn render_mbset(ctx: web_sys::CanvasRenderingContext2d, expansion_rate: f64) {
    let canv_width = ctx.canvas().unwrap().width();
    let canv_height = ctx.canvas().unwrap().height();

    ctx.clear_rect(0., 0., canv_width as f64, canv_height as f64);

    let canv_tf = AffineTransformer {
        a: expansion_rate, b: 0., c: canv_width as f64 / 2.,
        d: 0., e: -expansion_rate, f: canv_height as f64 / 2.
    };

    for canv_x in 0..canv_width {
        for canv_y in 0..canv_height {
            let z = canv_tf.inverse(Point { x: canv_x as f64, y: canv_y as f64 });
            if is_inner_mbset(z.to_c64()) {
                ctx.fill_rect(canv_x as f64, canv_y as f64, 1., 1.);
            }
        }
    }
}
```

/static/index.html にもCanvasを足しておく。
```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="UTF-8">
    <title>My Rust + Webpack project!</title>
  </head>
  <body>
    <canvas id="canvas" width="800" height="800"></canvas>
    <script src="index.js"></script>
  </body>
</html>
```

これで実行してみると、マンデルブロ集合が描画されるまで *75秒* もかかった。  
前回作ったTypeScript製やつの最終版で測ったら表示されるまで2秒ちょっとだったので、ざっと40倍も遅い:sob:  

### 高速化？してみる
多分Rust側で`canvas.fillRect`メソッドを呼びまくってるのが問題だと推測し、  
Canvasの操作はJavaScript(TypeScript)側でやることにしてRust側は純粋に計算だけをするようにする。  

#### TypeScriptを使うための下準備
コードを書き始める前にTypeScriptが使えるようにするための準備をする。  

```bash
$ npm install typescript ts-loader
```

webpack.config.jsを書き換える
```javascript
const path = require("path");
const CopyPlugin = require("copy-webpack-plugin");
const WasmPackPlugin = require("@wasm-tool/wasm-pack-plugin");

const dist = path.resolve(__dirname, "dist");

module.exports = {
  mode: "production",
  entry: {
    index: "./js/index.ts"
  },
  output: {
    path: dist,
    filename: "[name].js"
  },
  devServer: {
    contentBase: dist,
  },
  module: {
    rules: [
      {
        test: /\.ts$/,
        exclude: /node_modules/,
        loader: "ts-loader"
      },
    ],
  },
  resolve: {
    extensions: [".js", ".ts"]
  },
  plugins: [
    new CopyPlugin([
      path.resolve(__dirname, "static")
    ]),

    new WasmPackPlugin({
      crateDirectory: __dirname,
    }),
  ]
}
```

tscofig.jsonもちょっと書き換える。
```json
{
  "compilerOptions": {
    ...
    "target": "ES2020", 
    "module": "es2020", // ここがcommonjsだとダメっぽい
    ...
  }
}
```

これでビルドが通るか確認する。

### TypeScript
Rust側で公開した関数の型定義は /pkg/index.d.ts に出力されるので、  
これを読み込めばRustの関数をTypeScript側でも型付きで使うことができる。  

```rust
#[wasm_bindgen]
pub fn get_pixel_array(ctx: web_sys::CanvasRenderingContext2d, expansion_rate: f64) -> js_sys::Array {
    let canv_width = ctx.canvas().unwrap().width();
    let canv_height = ctx.canvas().unwrap().height();

    let canv_tf = AffineTransformer {
        a: expansion_rate, b: 0., c: canv_width as f64 / 2.,
        d: 0., e: -expansion_rate, f: canv_height as f64 / 2.
    };

    let begin = js_sys::Date::now();
    let arr = js_sys::Array::new_with_length(canv_width * canv_height);
    for canv_x in 0..canv_width {
        for canv_y in 0..canv_height {
            let z = canv_tf.inverse(Point { x: canv_x as f64, y: canv_y as f64 });
            
            if is_inner_mbset(z.to_c64()) {
                arr.set(canv_width * canv_y + canv_x, JsValue::TRUE);
            } else {
                arr.set(canv_width * canv_y + canv_x, JsValue::FALSE);
            }
        }
    }
    let end = js_sys::Date::now();
    print(format!("calcuration complete: {}", end - begin).as_str());

    return arr
}
```

/pkg/index.d.ts に出力される型定義
```typescript
/* tslint:disable */
/* eslint-disable */
/**
*/
export function main_js(): void;
/**
* @param {CanvasRenderingContext2D} ctx
* @param {number} expansion_rate
* @returns {Array<any>}
*/
export function get_pixel_array(ctx: CanvasRenderingContext2D, expansion_rate: number): Array<any>;
```

```typescript
import * as Mod from "../pkg/index";

import("../pkg/index.js")
.then(main)
.catch(console.error);

function main(mod: typeof Mod) {
    const begin = Date.now()
    const canv = document.getElementById("canvas") as HTMLCanvasElement;
    const ctx = canv.getContext("2d")!;
    const canv_width = canv.width;
    const canv_height = canv.height;
    const arr = mod.get_pixel_array(ctx, 400);

    console.log("t1: ", Date.now() - begin)
    arr.forEach((e, i) => {
        if (e) {
            const y = Math.trunc(i / canv_width);
            const x = i - canv_width * y;

            ctx!.fillRect(x, y, 1, 1);
        }
    });
    console.log("t2: ", Date.now() - begin)
}
```

これを実行すると、相変わらず70秒ほどかかる :sob:  
計測すると分かるがRust側の計算で70秒程度の計算時間のほぼ全てを消費している。  

### 種明かし（？）
こんなに遅いのは何か変だし、コードを変えたのに相変わらず 70秒程度という同じ計算時間がかかっているのが変だなと思い
pythonでこんな感じのコードを書いて/dist以下のディレクトリを直接ホストする
(`.wasm`ファイルはMIMEタイプを指定を正しくしないと動かないので)。

```python
# -*- coding: utf-8 -*-
#test on python 3.4 ,python of lower version  has different module organization.
import http.server
from http.server import HTTPServer, BaseHTTPRequestHandler
import socketserver

PORT = 8081

Handler = http.server.SimpleHTTPRequestHandler

Handler.extensions_map = {
    '.manifest': 'text/cache-manifest',
	'.html': 'text/html',
    '.png': 'image/png',
	'.jpg': 'image/jpg',
	'.svg':	'image/svg+xml',
	'.css':	'text/css',
	'.js':	'application/x-javascript',
    '.wasm': 'application/wasm',
	'': 'application/octet-stream', # Default
}

httpd = socketserver.TCPServer(("", PORT), Handler)

print("serving at port", PORT)
httpd.serve_forever()
```

これで localhost:8081 を開くと 1 ~ 2秒程度でマンデルブロ集合が描画された。
どうやら webpack-dev-server のホットリロード機能が悪さをしていてサーバーがタイムアウトするまで
処理が始まらなかったっぽい。


## 2. C# + Blazor

### 下準備
dotnet CLI があればテンプレートがインストール済みなので普通にプロジェクトを作ればよい。  
BlazorでCanvasを扱うラッパーライブラリとして Excubo.Blazor.Canvas というのがあったので今回はそれを使う。  
```bash
$ dotnet new blazorwasm --name=mandelbrot-set-playground-blazor
$ cd mandelbrot-set-playground-blazor
$ dotnet add package Excubo.Blazor.Canvas
$ dotnet run
```

### やっていく
```csharp
using System.Numerics;

struct Point {
    public double x;
    public double y;
    public Complex ToComplex() => new Complex(this.x, this.y);
}

struct AffineTransformer {
    private double a;
    private double b;
    private double c;
    private double d;
    private double e;
    private double f;

    public AffineTransformer(double a, double b, double c, double d, double e, double f) {
        this.a = a; this.b = b; this.c = c; this.d = d; this.e = e; this.f = f;
    }
    private double det => a * e - b * d;
    public Point Transform(Point p) => new Point {
        x = a * p.x + b * p.y + c,
        y = d * p.x + e * p.y + f
    };
    public Point Inverse(Point p) => new Point {
        x = (e * p.x - b * p.y - c * e + b * f) / det,
        y = (-d *p.x + a * p.y + c * d - a * f) / det
    };
}

static class Lib {
    public static Complex MbTransform(Complex z, Complex c) => z * z + c;
    public static bool IsInnerMBSet(Complex c) {
        const int LOOP_MAX = 1000;
        var z = new Complex(0, 0);

        for (var i = 0; i < LOOP_MAX; i++) {
            z = MbTransform(z, c);
            if (z.Magnitude > 2) return false;
        }

        return true;
    }
}
```

```csharp
@page "/"
@using Excubo.Blazor.Canvas

<h1>Hello, world!</h1>

<Canvas @ref="helper_canvas" width="200px" height="200px" />

@code {
    const int canv_width = 200;
    const int canv_height = 200;
    private Canvas helper_canvas;
    protected override async Task OnAfterRenderAsync(bool first_render)
    {
        if (!first_render) return;

        var expansionRate = 100;

        var begin = DateTime.Now;
        await using (var ctx = await helper_canvas.GetContext2DAsync())
        {
            var canvTf = new AffineTransformer(
                a: expansionRate,
                b: 0,
                c: canv_width / 2,
                d: 0,
                e: - expansionRate,
                f: canv_height / 2
            );

            for (var canv_x = 0; canv_x < canv_width; canv_x++) {
                for (var canv_y = 0; canv_y < canv_width; canv_y++) {
                    var z = canvTf.Inverse(new Point { x = canv_x, y = canv_y });
                    if (Lib.IsInnerMBSet(z.ToComplex())) {
                       await ctx.FillRectAsync(canv_x, canv_y, 1, 1);
                    }
                }
            }
        }
        var end = DateTime.Now;

        Console.WriteLine(end.Subtract(begin).TotalMilliseconds);
    }
}
```

遅すぎるのでCanvasの大きさを 200x200 にしているのだが、それでも表示されるまで20秒~30秒ほどかかる。  
単純計算でTypeScriptの250倍程度遅い。  
BlazorはC#をwasmにコンパイルしているのではなくて、wasmでC#のランタイムを実装しているので  
原理的にwasmよりも速くはならないし、WebAPIを叩く場合のオーバーヘッドはwasmと同様にある。  
C#でWeb開発ができるという以外にメリットが無いので、既に ASP.NET で構築済みのサイトをSPA化するとか  
そういう場合のユースケースに限られる気がする。  

## 全体通しての感想
今回は Canvas のメソッドをめっちゃ叩きまくるというかなり極端なユースケースだったので、  
これをもってwasmが使い物にならない、と結論付けることはできない。  
しかし、現状のWeb開発のデファクトスタンダードである TypeScript + node.js系ツールチェイン のエコシステムを捨ててまで  
wasmを使う理由があるのかというとかなり疑問に感じる。  
特にRustはよくGC無しのメモリ管理が長所として挙げられるが、Webフロントエンドにおいては言語ランタイムにGCが無くても  
DOMのGCがあるので、GCレスに拘ることにどれだけ価値があるのかが疑問である。  
Webフロントエンドにおけるwasmのユースケースとしては、TypeScriptを置き換えるものというよりは、  
基本的には普通にTypeScriptで開発してプロファイリングして分かったボトルネック部分を必要に応じてwasmで書き直して高速化するという  
TypeScript を補助するような用途が現実的ではないかと思う。  
また、個人的にwasmが輝くのはWebフロントエンドではなくて、むしろBetterJVMとしてのポータブルな軽量言語ランタイムとしての用途ではないかと
勝手に思っている。
とりあえず、後10年くらいはTypeScriptの天下が続くのかなあと思った(小並感)。

### (おまけ)Rustを使ってみた感想
- Rustの命名規則は基本的にスネークケースなのだが、普段はキャメルケースを使っているのでスネークケースだと指が辛い
- numberに慣れきった身としては数値の変換が面倒...
- `unwrap`をタイプするのが面倒(swiftやTSのように`!`だけで済ませられるようにしてくれ...(マクロと被るので無理))
- スコープ演算子(`::`)がキモい(個人の感想です)
- 演算子オーバーロードがあるのは助かる

## 参考資料
- RustのWebAssembly で canvas に描画する [https://qiita.com/tiohsa/items/caa923e4efb689e1250b]
