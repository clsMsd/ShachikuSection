# Redux

## Reduxとは?
> Redux is a predictable state container for JavaScript apps.  
 It helps you write applications that behave consistently, run in different environments (client, server, and native), and are easy to test.  
 On top of that, it provides a great developer experience, such as live code editing combined with a time traveling debugger.  
 (cited from https://github.com/reduxjs/redux)

Reactと一緒によく使われる状態管理のフレームワーク。  
もともと、ReactではFacebookによりFluxという単方向データフローのアーキテクチャが提唱されていた。
FluxはもともとMVCやMVVMなどと同じようなアプリのアーキテクチャであって、具体的なフレームワークやライブラリを伴うものではなかった。
ReduxはFluxを具体的に実装したフレームワークの一つである(が、微妙にオリジナルのFluxと異なる部分もあるらしい)。

Fluxの概念図
<img src="https://raw.githubusercontent.com/facebook/flux/master/docs/img/flux-diagram-white-background.png">

ReduxはReactと共に使われることが多いが、Reactとは独立した存在であり、React抜きでも使うことはできる。

## Reduxの存在意義

Reactでは基本的にコンポーネントに状態をもたせる。iOSで例えるとViewControllerに状態とロジックをすべてもたせてるような感じである。
コンポーネントの状態がそのコンポーネント内に閉じていて、他のコンポーネントに影響を及ぼさない間は問題ないが、
親子関係・兄弟関係のコンポーネントの間で状態を共有する、子コンポーネントから親コンポーネントの状態を変更する、
又はその逆、といった操作が必要になると途端にコードが複雑化する。

例えば、Reactの説明の際に作ったカウンターを改造して、一つの画面に3つのカウンターがあり、それらのカウンターの合計値を表示するようなアプリを作ってみよう。
普通に作ろうとするとこんな感じになる。

```typescript
class RootCounter extends React.Component<{}, {total : number}>{
    constructor(props: {}) {
        super(props)
        this.state = {
            count: 0
        }
    }

    render() {
        return (
            <div>
                <p>total: {this.state.total}</p>
                <Counter />
                <Counter />
                <Counter />
            </div>
        )
    }
}
```

ここで、RootCounterから子コンポーネントであるCounterのstateを取得する必要がある。
しかし、Reactではコンポーネントのstateを外から取得することは(基本的に)できない。
そこで、Counterに持たせているstateをRootCounterに移す必要がある。
(参考: https://reactjs.org/docs/lifting-state-up.html)

```typescript
const Counter = ({ count, increment, decrement }: any) => (
    <div>
        <button onClick={() => increment()}>+</button>
        <button onClick={() => decrement()}>-</button>
        <p>count: {count}</p>
    </div>
)

class RootCounter extends React.Component<any, any> {
    constructor(props: {}) {
        super(props)
        this.state = {
            count1: 0
            count2: 0
            count3: 0
        }
    }

    render() {
        return (
            <div>
                <p>total: {this.state.count1 + this.state.count2 + this.state.count3}</p>
                <Counter count={count1}
                         increment={() => this.setState({count1: this.state.count1 + 1 })}
                         decrement={() => this.setState({count1: this.state.count1 - 1 })}/>
                <Counter count={count2}
                         increment={() => this.setState({count1: this.state.count2 + 1 })}
                         decrement={() => this.setState({count1: this.state.count2 - 1 })}/>
                <Counter count={count3}
                         increment={() => this.setState({count1: this.state.count3 + 1 })}
                         decrement={() => this.setState({count1: this.state.count3 - 1 })}/>
            </div>
        )
    }
}
```
このように、Reactでコンポーネント間でstateの共有・更新を行うには、まずstateを共通の親コンポーネントに移し、そこからpropsを経由してstateやstateを更新するコールバック関数を渡す必要がある。
props経由による状態の受け渡し、状態の更新は俗に「propsのバケツリレー」と呼ばれ、Reactが忌避される一因となっている、気がする。
例えばアプリの中でプレミアムユーザーか否かで表示を変える必要があるコンポーネントがあったとすると、このままだとRootのコンポーネントにプレミアムユーザーか否かを判断するstateを持たせ、
表示を変えるコンポーネントまでコンポーネントツリーの上から下にpropsを渡し続ける必要がある。

Reduxを使うと、このようなpropsのバケツリレーを減らすことができる。

Reduxの概念図
<img src="https://camo.qiitausercontent.com/ba6631bf8265a1de7c29b992027337079ae00783/68747470733a2f2f71696974612d696d6167652d73746f72652e73332e616d617a6f6e6177732e636f6d2f302f33363831332f37343032633766342d613762322d643461322d653330642d6434616235383136343837632e706e67">

Reduxではアプリの状態は
- Storeというシングルトンオブジェクトが管理し
- Actionを発行する以外で変更できず
- 状態の変更は (古い状態) + Action => (新しい状態) という関数を通して行う
という原則がある
(参考: https://redux.js.org/introduction/threeprinciples)

## インストール
```
npm i --save-dev redux react-redux @types/redux @types/react-redux
```

## 作ってみる
Reduxで簡単なカウンターを作ってみよう。

```typescript:src/redux/action.tsx
export type ActionType = "INCREMENT" | "DECREMENT" | "RESET"

export interface Action {
    type: ActionType
    payload?: {
        num: number
    }
}

export function increment(num: number): Action {
    return {
        type: "INCREMENT",
        payload: { num }
    }
}

export function decrement(num: number): Action {
    return {
        type: "DECREMENT",
        payload: { num }
    }
}

export function reset(): Action {
    return {
        type: "RESET"
    }
}
```

```typescript:src/redux/reducer.tsx
import { Action } from "./action";

export interface IStoreState {
    count: number
}

const initialState: IStoreState = { count: 0 }

const reducer = (state: IStoreState = initialState, action: Action): IStoreState => {
    switch(action.type) {
        case "INCREMENT":
            return { count: state.count + 1 }
        case "DECREMENT":
            return { count: state.count - 1 }
        case "RESET":
            return initialState
    }
    return initialState
}

export default reducer
```

```typescript:src/index.tsx
import * as React from 'react';
import * as ReactDOM from 'react-dom';
import App from './App';
import './index.css';
import registerServiceWorker from './registerServiceWorker';

import { createStore　} from "redux"
import { Provider } from "react-redux"
import reducer from "./redux/reducer"

const store = createStore(reducer)

ReactDOM.render(
  <Provider store={store}>
    <App />
  </Provider>,
  document.getElementById('root') as HTMLElement
);
registerServiceWorker();
```

```typescript:src/Counter.tsx
import * as React from "react";
import { connect } from "react-redux"
import { Action, increment, decrement, reset } from "./redux/action"
import { IStoreState } from './redux/reducer';

interface ICounterProps {
    count: number
    increment: (num: number) => Action,
    decrement: (num: number) => Action,
    reset: () => Action
}

const Counter = ({ count, increment, decrement, reset }: ICounterProps) => (
    <div>
        <button onClick={() => increment(1)}>+</button>
        <button onClick={() => decrement(1)}>-</button>
        <button onClick={() => reset()}>RESET</button>
        <p>count: {count}</p>
    </div>
)

export default connect(
    (state: IStoreState) => ({ count: state.count }),
    (dispatch: Dispatch<Action>) => ({
        increment: (num: number) => dispatch(increment(num)),
        decrement: (num: number) => dispatch(decrement(num)),
        reset: () => dispatch(reset()),
    })
)(Counter)
```

`connect`の第一引数にはstoreのstateをpropsに変換する関数を、第二引数にはActionCreaterをdispatchでラップしてpropsに変換する関数を渡す。
第二引数の方は省略して次のようにも書ける。

```typescript
export default connect(
    (state: IStoreState) => ({ count: state.count }),
    { increment, decrement, reset })
)(Counter)
```

`connect`に渡す引数の書き方はめちゃくちゃ種類があるので注意しよう。
https://qiita.com/MegaBlackLabel/items/df868e734d199071b883
https://blog.benestudio.co/5-ways-to-connect-redux-actions-3f56af4009c8
