# Redux

## Reduxの存在意義

Reactではコンポーネントに状態をもたせる。
コンポーネントの状態がそのコンポーネント内に閉じていて、他のコンポーネントに影響を及ぼさない間は問題ないが、
親子関係・兄弟関係のコンポーネントの間で状態を共有する、子コンポーネントから親コンポーネントの状態を変更する、
又はその逆、といった操作が必要になると途端にコードが複雑化する。

## インストール
```
npm i --save-dev redux react-redux @types/redux @types/react-redux
```

## Hello World
Reduxで簡単なカウンターを作ってみよう。
まず、

src/redux/action.tsx
```typescript
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

ser/redux/reducer.tsx
```typescript
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

src/index.tsx
```typescript
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

src/Counter.tsx
```typescript
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

`connect`に渡す引数の書き方はめちゃくちゃ種類があるので注意しよう。
https://qiita.com/MegaBlackLabel/items/df868e734d199071b883
https://blog.benestudio.co/5-ways-to-connect-redux-actions-3f56af4009c8

## 所感

Reduxを使うとStoreとComponentのどちらにどれくらい状態を持たせるべきかという悩みが生まれる。
個人の意見としては、Viewのみに関わる状態以外はガンガンStoreに持たせてよいと思う。

