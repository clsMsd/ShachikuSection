# Lit入門

## Litとは？
> Lit is a simple library for building fast, lightweight web components.
> (Cited from https://lit.dev/docs/)

軽量WebComponentライブラリ。  
以前紹介したように，ライブラリの力を頼らずにWebComponentだけでWebアプリを作るのは色々と辛い。  
そこでLitを使うことで便利にWebComponentを使いつつWebアプリを作ることができる。  

これまでの流れ:  

GoogleがpolymerというレガシーブラウザでWebComponentを使うためのPolyfillを作る  
↓  
polymer projectの一環として，lit-htmlとlit-elementというライブラリが作られる  
↓  
2021年4月に polymer, lit-html, lit-element を統合したライブラリとして Lit がリリースされる  
(ただし，まだRC版)  

今までの lit-html，lit-element と違うこと強調する場合は Lit2，あるいはLit v2 という表記を使うこともある。  
ただしメジャーバージョンは上がっているが非互換な変更はあまりないらしい。  

### 特徴
- Custom Elements:  
  Lit製のコンポーネントはCustomElementに変換される
- Scoped styles:  
  ShadowDOMによりコンポーネントの外にStyleが漏れない
- Reactive properties:  
  Reactiveなプロパティが宣言でき，プロパティが更新されたら自動的にコンポーネントを再描画してくれる  
  (ちなみに仮想DOMは使っていない)
- Declarative templates:  
  タグ付きテンプレートリテラルで宣言的にコンポーネントを記述することができる

## やってみる
いつものようにプロジェクトのディレクトリを作って npm でインストールする。  
```bash
$ mkdir lit-sample
$ cd lit-sample
$ npm init
$ npm install lit webpack webpack-cli webpack-dev-server typescript ts-loader html-webpack-plugin
```

`tsconfig.json` と `webpack.config.js` を作成する。  
tsconfig.json
```json
{
  "compilerOptions": {
    "target": "ES2015",  // WebComponentを使うにはES2015以降が必須
    "module": "commonjs", 
    "strict": true,
    "esModuleInterop": true,
    "experimentalDecorators": true, // decoratorを使う場合はこの設定も必須
    "skipLibCheck": true,
    "forceConsistentCasingInFileNames": true
  }
}
```

webpack.config.js
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
    rules: [{
      test: /\.ts$/,
      exclude: /node_modules/,
      loader: "ts-loader"
    }],
  },
  resolve: {
    extensions: [".js", ".ts"]
  },
  plugins: [
    new HtmlWebpackPlugin({
      template: path.join(src, "index.html")
    })
  ]
}
```
Litは純粋なJavaScriptのライブラリなので ReactのJSXやVueのSFCと違ってビルド時にソースコードを変換するような仕組みが必要ない。  
(ただしdecoratorを使う場合はbabelかTypeScriptが必要になる)  

### Hello World
とりあえず公式のサンプルを動かしてみる。  

app.ts
```typescript
import {html, css, LitElement, render} from 'lit';
import {customElement, property} from 'lit/decorators.js';

@customElement('simple-greeting')
export class SimpleGreeting extends LitElement {
  static styles = css`p { color: blue }`;

  @property()
  name = 'Somebody';

  render() {
    return html`<p>Hello, ${this.name}!</p>`;
  }
}

render(html`<simple-greeting></simple-greeting>`, document.getElementById("app")!)

// ↓のように直にCustomElementを追加しても良い
// document.getElementById("app")!
//   .appendChild(document.createElement("simple-greeting"))
```
index.html
```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
  </head>
  <body>
    <div id="app"></div>
  </body>
</html>
```

前述したようにLitのコンポーネントはCustomElementsとして定義されるので，  
下のようにhtmlに直にCustomElementsを書いてもよい。  

index.html
```html
<!DOCTYPE html>
<html>
  <head>
    <meta charset="utf-8">
  </head>
  <body>
    <simple-greeting></simple-greeting>
  </body>
</html>
```

### カウンター
```typescript
import {html, css, LitElement,} from 'lit';
import {customElement, property} from 'lit/decorators.js';

@customElement('app-root')
export class AppRoot extends LitElement {
  render() {
    return html`
      <div>
        <p>Hello, Lit!</p>
        <counter-></counter->
      </div>
    `;
  }
}

@customElement('counter-')
class Counter extends LitElement {
  @property({ type: Number }) count = 0

  increment() { this.count++ } 
  decrement() { this.count-- }

  render () {
    return html`
      <div>
        <p>count: ${this.count}</p>
        <button @click="${this.increment}">+</button>
        <button @click="${this.decrement}">-</button>
      </div>
    `
  }
}


render(html`<app-root></app-root>`, document.getElementById("app")!)
```

devtoolを開いてみれば分かるが，`count`が変化してもコンポーネント全体が再描画されることは無く，  
`count`に依存している箇所だけが再描画される。  

何度も言うようにコンポーネントはCustomElementとして定義されるので，必然的にグローバルに公開されることになる。  
(一応実験的機能としてScoped CustomElementRegistryというものがあるらしいが，未調査)
  
  
状態を持たないコンポーネントなら単なる関数として書けるので，ファイルスコープにとどめることができる。  
```typescript
import {html, css, LitElement,} from 'lit';
import {customElement, property} from 'lit/decorators.js';

@customElement('app-root')
export class AppRoot extends LitElement {
  render() {
    return html`
      <div>
        <p>Hello, Lit!</p>
        <counter-></counter->
      </div>
    `;
  }
}

const CountIndicator = (count: number) => html`<div>count: ${count}</div>`

@customElement('counter-')
class Counter extends LitElement {
  @property({ type: Number }) count = 0

  increment() { this.count++ } 
  decrement() { this.count-- }

  render () {
    return html`
      <div>
        ${CountIndicator(this.count)}
        <button @click="${this.increment}">+</button>
        <button @click="${this.decrement}">-</button>
      </div>
    `
  }
}

render(html`<app-root></app-root>`, document.getElementById("app")!)
```

### ライフサイクルフック
`LitElement`クラスは`HTMLElement`クラスを継承しているため，`connectedCallback()`, `disconnectedCallback()`, `attributeChangedCallback()`等の  
ライフサイクルメソッドがそのまま使える他，プロパティが変化した際などに呼ばれる追加のメソッドが用意されている。  

## 感想
- Webpackのloaderやpluginが必要ないというのはありがたい。だが...(↓へ続く)
- decorator を使いまくっているのには不安がある
  - Web標準技術使ってますよアピールをしまくっているのにそこは非標準の書き方をするのかよ！と思った
  - decoratorを使うと必然的にBabelかTypeScriptが必須になるので↑の利点が損なわれるのでは？という気持ちもある
  - 一応decoratorを使わない書き方もできるので気になる人はdecoratorを使わない方が良いだろう
- Reactと比べるとエディタのサポートが貧弱なのは辛い
  - 特にhtmlテンプレート中で補完が効かないのが辛い
  - コメントアウトも自分で書いたり消したりしないといけないので辛い
- コンポーネント名を必ずハイフンで区切らないといけないのは辛い…と思っていたのだが，1単語のコンポーネントの場合は名前の末尾にハイフンを付ければ良いということが分かった
  (例えば`counter`だったら`counter-`とすればよい)。
  逆に名前の先頭にハイフンを付けるのは許されない。
- 問答無用でコンポーネントがグローバルに公開されてしまう(ファイルスコープのコンポーネントが作れない)のは辛そう
- 一応TypeScript対応しているが色々と型チェックが働かないところがあるのが辛い  
  (そもそもCustomElement(というかhtml)に型が無いので仕方ないかもしれないが)
- というか何でもかんでもCustomElementにするということ自体どうなのか？という気がする
  (ライブラリとして外部に公開するコンポーネントならCustomElementにする価値はあるかもしれないが，そうでないコンポーネントまでCustomElement化する意味は無いのでは？と思う)
- Hooksを推奨してclassを亡き者にしたがっている最近のReactに付いていけないという人には良いかもしれない
