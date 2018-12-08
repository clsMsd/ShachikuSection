# React

## Reactとは？

https://github.com/facebook/react/

Webの歴史
1. ネットワーク上で文書を閲覧・共有するためにwwwが生まれる。  
webサーバーはリクエストに応じてあらかじめ用意されたhtmlを返す。
2. wwwの普及とともにいろいろなwebサービスが生まれる。  
webサーバーはリクエストに応じて動的にhtmlを生成して返す。  
3. htmlとjavascriptの高機能化により、ブラウザ上で高度なアプリが動かせるようになる。  
webサーバーはhtmlやjsなどの静的なリソースを返すとともに、APIを公開し動的に生成されたjsonなどの形式のデータを返す。  
  
3のタイプのwebページをSingle Page Applicationという(SPA)。  
ReactはSPAをつくるためのライブラリ。  
SPAをつくるためのjsのライブラリはいろいろある(あった)  
Angular  
Backbone.js  
Knockout.js  
Riot.js  
Ember.js  
Mithril.js  
jQuery  
などなど。  
  
最近ではもっぱらReactとVueの2強である。

## 環境構築

node.jsはインストール済みであるとする。
適当なディレクトリで以下のコマンドを叩く

```
npx create-react-app tssample --scripts-version=react-scripts-ts # tssampleディレクトリが生成される
cd tssample
```

`create-react-app`というのはreactの開発でよく使うwebpackやbabel等のライブラリをひとまとめでインストールして環境構築をしてくれるコマンドである。
コマンド実行時に`--scripts-version=react-scripts-ts`を指定するとtypescript向けに環境構築してくれる。

## Hello World
tssampleディレクトリに移動して、`npm start`を実行してみよう。
3000番ポートに開発サーバーが起動するので、ブラウザで`localhost:3000`を開くと以下のような画面が表示される。

public/index.html
```html
<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1, shrink-to-fit=no">
    <meta name="theme-color" content="#000000">
    <!--
      manifest.json provides metadata used when your web app is added to the
      homescreen on Android. See https://developers.google.com/web/fundamentals/engage-and-retain/web-app-manifest/
    -->
    <link rel="manifest" href="%PUBLIC_URL%/manifest.json">
    <link rel="shortcut icon" href="%PUBLIC_URL%/favicon.ico">
    <!--
      Notice the use of %PUBLIC_URL% in the tags above.
      It will be replaced with the URL of the `public` folder during the build.
      Only files inside the `public` folder can be referenced from the HTML.

      Unlike "/favicon.ico" or "favicon.ico", "%PUBLIC_URL%/favicon.ico" will
      work correctly both with client-side routing and a non-root public URL.
      Learn how to configure a non-root public URL by running `npm run build`.
    -->
    <title>React App</title>
  </head>
  <body>
    <noscript>
      You need to enable JavaScript to run this app.
    </noscript>
    <div id="root"></div>
    <!--
      This HTML file is a template.
      If you open it directly in the browser, you will see an empty page.

      You can add webfonts, meta tags, or analytics to this file.
      The build step will place the bundled scripts into the <body> tag.

      To begin the development, run `npm start` or `yarn start`.
      To create a production bundle, use `npm run build` or `yarn build`.
    -->
  </body>
</html>
```

src/index.tsx
```typescript
import * as React from 'react';
import * as ReactDOM from 'react-dom';
import App from './App';
import './index.css';
import registerServiceWorker from './registerServiceWorker';

ReactDOM.render(
  <App />,
  document.getElementById('root') as HTMLElement
);
registerServiceWorker();
```

`ReactDOM.render`は、htmlの指定された箇所にDOMツリーを埋め込むという処理をする。
今回の場合は、public/index.htmlの`<div id="root"></div>`に`<App />`コンポーネントを埋め込むという処理を行っている。
public/index.htmlとsrc/index.tsxを次のように書き換えてみよう。

public/index.html
```html
<!DOCTYPE html>
<html lang="en">
  ... 略 ...
  <body>
    <noscript>
      You need to enable JavaScript to run this app.
    </noscript>
    <div id="root"></div>
    <!--
      This HTML file is a template.
      If you open it directly in the browser, you will see an empty page.

      You can add webfonts, meta tags, or analytics to this file.
      The build step will place the bundled scripts into the <body> tag.

      To begin the development, run `npm start` or `yarn start`.
      To create a production bundle, use `npm run build` or `yarn build`.
    -->
    <div id="myroot"></div>
  </body>
</html>
```

src/index.tsx
```typescript
import * as React from 'react';
import * as ReactDOM from 'react-dom';
import App from './App';
import './index.css';
import registerServiceWorker from './registerServiceWorker';

ReactDOM.render(
  <App />,
  document.getElementById('root') as HTMLElement
);
ReactDOM.render(
  <h1>Hello World</h1>,
  document.getElementById('myroot') as HTMLElement
);
registerServiceWorker();
```

`ReactDOM.render`の第一引数に渡しているものはJSXと呼ばれるもので、出力するDOM(コンポーネント)を指定するものである。
普通のhtmlで使えるタグは普通に使える他、`<App />`のように自分で新たなコンポーネントを定義して使うこともできる。
基本的にはhtmlと同じ書き方ができるが
- htmlで定義済みのタグは小文字、ユーザー独自定義のタグは先頭を大文字にする
- attribute名がハイフン区切りでなくCamelCase
- htmlのclassはclassNameと書く
という細かい違いがあるので注意。
JSX中にJavaScriptのコード(式)を埋め込むにはコードを`{}`で囲む。JSX中に埋め込まれたJavaScriptのコードは最終的に値になるので、文を埋め込むことはできない。

```jsx
<h1>Hello World</h1> {/* htmlで定義済みタグは先頭を小文字にする */}

<CustomLabel>Hello World</CustomLabel> {/* ユーザー定義のタグは先頭を大文字にする */}

<h1 fontSize="15px">Hello World<</h1> {/* attribute は CamelCase で書く */}

<h1 className="title">Hello World<</h1> {/* class を指定する時は className と書く */}

<span>I'm {person.name}, {person.age} old. </span> {/* jsのコードを埋め込む時は {} でくくる  */}

<div>
    { isUserPremium ? <PremiumIcon /> : <NormalIcon /> }
</div> {/* 埋め込んだjsのコードの中でjsxを使うこともできる */}
```

## コンポーネント

自分でコンポーネントを定義してみよう。
コンポーネントは状態を持つものと持たないものの2つに大別され、前者はStateful ComponentとかClass　Componentとか言われる。
後者はStateless ComponentとかFunctional Componentとか言われる。

### Class Component
まずはClass Componentを定義してみよう。

src/counter.tsx
```typescript
import * as React from "react";

interface IState {
    count: number
}

class Counter extends React.Component<null, IState> {
    constructor(null) {
        super(null)
        this.state = {
            count: 0
        }
    }

    public render() {
        return (
            <div>
                count: {this.state.count}
            </div>
        )
    }
}

export default Counter;
```

`React.Component<{}, IState>`は第一引数に`props`の型を(後で説明する)、第二引数に`state`の型をとる。
stateとはReactのコンポーネントで状態を保持するプロパティである。コンポーネントに何か状態をもたせるときは必ずstateの下にぶらさげる。
これでコンポーネントを定義できた。
app.tsxを書き換えて、今作ったコンポーネントを表示してみよう

src/app.tsx
```typescript
import * as React from 'react';
import './App.css';
import Counter from './counter.tsx';

import logo from './logo.svg';

class App extends React.Component {
  public render() {
    return (
      <div className="App">
        <header className="App-header">
          <img src={logo} className="App-logo" alt="logo" />
          <h1 className="App-title">Welcome to React</h1>
        </header>
        <p className="App-intro">
          To get started, edit <code>src/App.tsx</code> and save to reload.
        </p>
        <Counter/> {/* ここに追加した */}
      </div>
    );
  }
}

export default App;
```

次にCounterの状態を更新してみよう。
コンポーネントの状態を更新するときは`setState`メソッドに新しいstateオブジェクトを渡して実行する。
`setState`メソッドを実行すると、更新された状態に応じて自動的にコンポーネントが再描画される。

src/counter.tsx
```typescript
import * as React from "react";

interface IState {
    count: number
}

class Counter extends React.Component<{}, IState> {
    constructor(props: {}) {
        super(props)
        this.state = {
            count: 0
        }
    }

    public render() {
        return (
            <div>
                <button onClick={() => this.setState({ count: this.state.count + 1 })}>+</button>
                <button onClick={() => this.setState({ count: this.state.count - 1 })}>-</button> 
                count: {this.state.count}
            </div>
        )
    }
}

export default Counter;
```

コンポーネントの状態管理にstateプロパティを使うのはこの再描画が理由で、state以外に勝手にプロパティを定義して状態をもたせても、
そのプロパティが更新された際にコンポーネントが再描画されない。
stateプロパティも、単純に新しい状態を代入しても再描画されないので、必ず`setState`メソッドを呼び出して新しいstateをセットする必要がある。

NG例
```typescript
class Counter extends React.Component<{}, IState> {
    private count2: number

    constructor(props: {}) {
        super(props)
        this.state = {
            count: 0
        }
        this.count2 = 0
    }

    public render() {
        return (
            <div>
                <button onClick={() => { this.state.count++; this.count2++; }>+</button>
                <button onClick={() => { this.state.count--; this.count2--; }>-</button> 
                <p>count: {this.state.count}</p>   {/* 更新しても再描画されない */}
                <p>count2: {this.state.count2}</p> {/* 更新しても再描画されない */} 
            </div>
        )
    }
}
```

次にコンポーネントを利用する側(今回の場合はApp.tsx)からコンポーネントに値を渡してみよう。
このような用途には`props`を使う。

src/counter.tsx
```typescript
import * as React from "react";

interface IProps {
    initialValue: number
}

interface IState {
    count: number
}

class Counter extends React.Component<IProps, IState> {
    constructor(props: IProps) {
        super(props)
        this.state = {
            count: props.initialValue
        }
    }

    public render() {
        return (
            <div>
                <button onClick={() => this.Inc()}>+</button>
                <button onClick={() => this.Dec()}>-</button> 
                count: {this.state.count}
            </div>
        )
    }

    // メソッドに分けた
    private Inc() {
        this.setState({ count: this.state.count + 1  })
    }

    private Dec() {
        this.setState({ count: this.state.count - 1 })
    }
}

export default Counter;
```

コンポーネントを利用する側では、JSXタグのattributeとして`props`を渡す。
下のコードでは、`Counter`のpropsの`initialValue`として1が渡されている。

src/app.tsx
```typescript
class App extends React.Component {
  public render() {
    return (
      <div className="App">
        <header className="App-header">
          <img src={logo} className="App-logo" alt="logo" />
          <h1 className="App-title">Welcome to React</h1>
        </header>
        <p className="App-intro">
          To get started, edit <code>src/App.tsx</code> and save to reload.
        </p>
        <Counter initialValue={1}/>
      </div>
    );
  }
}
```

### Functional Component
次にFunctional Componentを定義してみよう。
Stateを持たないコンポーネントはpropsを受け取りJSXを返す関数として書くことができる。

```typescript
import * as React from "react";

interface CustomLabelProps {
    text: string
}

const CustomLabel = (props: CustomLabelProps) => (
    <div style={{
        margin: "12px", border: "solid 2px #000000",
        width: "200px", fontSize: "18px",
    }}>
        {props.text}
    </div>
)
```

ES2015の分割代入を使うとこんな感じで短く書けるので、こう書くことが多い。
```typescript
const CustomLabel = ({ text }: CustomLabelProps) => (
    <div style={{
        margin: "12px", border: "solid 2px #000000",
        width: "200px", fontSize: "18px",
    }}>
        {text}
    </div>
)
```

コンポーネントを使う側では、Class Component と同じようにタグのattributeとしてpropsを渡す。
```typescript
<CustomLabel text="Hello World" />
```

タグの中身(子ノード)を渡したい時は、
- Propsの型にReactNode型の`children`を追加する
- 関数の型に`React.StatelessComponent`を指定する
- Propsの型を定義するときに`React.Props`を継承する
のどれかをすればよい

つまり、こうするか
```typescript
interface CustomLabelProps {
    fontSize: number
    children: React.ReactNode
}
const CustomLabel = ({ fontSize, children }: CustomLabelProps) => (
    <div style={{
        margin: "12px", border: "solid 2px #000000",
        width: "200px", fontSize: fontSize,
    }}>
        {children}
    </div>
)
```

こうするか
```typescript
interface CustomLabelProps {
    fontSize: number,
}
const CustomLabel: React.StatelessComponent<CustomLabelProps> = ({ fontSize, children }) => (
    <div style={{
        margin: "12px", border: "solid 2px #000000",
        width: "200px", fontSize: fontSize,
    }}>
        {children}
    </div>
)
```

こうする
```typescript
interface CustomLabelProps extends React.Props<{}>  {
    fontSize: number,
}
const CustomLabel = ({ fontSize, children }: CustomLabelProps) => (
    <div style={{
        margin: "12px", border: "solid 2px #000000",
        width: "200px", fontSize: fontSize,
    }}>
        {children}
    </div>
)
```

コンポーネントを使う側では、普通のタグのように中にタグを重ねることができる。
```typescript
<CustomLabel fontSize={12}>Hello World</CustomLabel>
<CustomLabel fontSize={12}>
    <p>Hoge</p>
    <p>Fuga</p>
    <p>Piyo</p>
</CustomLabel>
```

ちなみにClass構文でもStateを持たなければStateless Componentなので、Class ComponentでStateless Componentを書くこともできるが、
完全な無駄なのでStateless ComponentはFunctional Componentで書くことが強く推奨されている。

## High Order Components
(あとで書く)
