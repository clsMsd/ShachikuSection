# GLSL

3次元コンピュータグラフィックスの描画処理を記述するためのGLSL(OpenGL Shading Language)について紹介する。

> シェーダーは、C と同様の構文を持つ特別な OpenGL シェーディング言語である GLSL (OpenGL Shading Language) を使用します。 GLSL はグラフィックスパイプラインによって直接実行されます。 シェーダーには、頂点 (バーテックス) シェーダーとフラグメント (ピクセル) シェーダーの2種類があります。 頂点シェーダーは、形状の位置を 3D 描画座標に変換します。 フラグメントシェーダーは、形状の色やその他の属性のレンダリングを計算します。
> 
> GLSL シェーダー, https://developer.mozilla.org/ja/docs/Games/Techniques/3D_on_the_web/GLSL_Shaders

グラフィックスが画面上に表示されるまでの処理をレンダリングパイプラインと呼び、頂点の処理とフラグメントの処理から構成される。
GLSLによって頂点処理とフラグメント処理をプログラムすることで様々なグラフィックス表現を描画することができる。

また、GLSLで書かれたプログラムはGPUによって処理され、高速に描画処理が計算される。

> ![](https://mdn.mozillademos.org/files/13334/mdn-games-3d-rendering-pipeline.png)
> 
> レンダリングパイプライン, https://developer.mozilla.org/ja/docs/Games/Techniques/3D_on_the_web/Basic_theory#rendering_pipeline

GLSLをオンラインに編集・実行できる環境がGLSL Sandboxというサイトで提供されている。
このサイトではフラグメントシェーダーをリアルタイムで編集・実行することができる。

- GLSL Sandbox, http://glslsandbox.com/

試しに次のGLSLプログラムをエディタに貼り付けると真っ白な画面が描画される。

```glsl
void main( void ) {
	gl_FragColor = vec4(1.0, 1.0, 1.0, 0.0);
}
```

フラグメントシェーダーの`main`処理はスクリーン上の各ピクセルごとに呼び出されそのピクセルの色を決定する。
`gl_FragColor`はGLSLの組み込み変数で、RGBAの値を持つ4次元ベクトルを設定することで色が与えられる。

RGBAはそれぞれ`0.0`から`1.0`までの値をとり、上の例ではすべて`1.0`を設定したためすべてのピクセルが白に設定された。

次の例ではX軸方向に色がグラデーションする。

```glsl
#ifdef GL_ES
precision mediump float;
#endif

#extension GL_OES_standard_derivatives : enable

uniform vec2 resolution;

void main( void ) {
	float p = gl_FragCoord.x / resolution.x;

	gl_FragColor = vec4( vec3(p), 1.0 );
}
```

`gl_FragCoord`もGLSLの組み込み変数で、`main`が呼び出されるときのピクセルの座標が格納されている。
値は`0`からスクリーンの幅までをとる。

また、`resolution`は外部から設定されるパラメータが格納されていて、スクリーンのサイズが設定されている。
`gl_FragCoord.x / resolution.x`によってX軸位置を`0.0`から`1.0`までの範囲に変換している。


最後の例はGLSLでライフゲームを作成する。
この例は以下のサンプルを参考にした。

http://glslsandbox.com/e#207.3

```glsl
#ifdef GL_ES
precision mediump float;
#endif

#extension GL_OES_standard_derivatives : enable

uniform vec2 mouse;
uniform vec2 resolution;
uniform sampler2D backbuffer;

vec4 live = vec4(0.0, 1.0, 0.0, 1.0);
vec4 dead = vec4(0.0, 0.0, 0.0, 1.0);

void main( void ) {
	vec2 position = ( gl_FragCoord.xy / resolution.xy );
	vec2 pixel = 1.0/resolution;

	if (length(position-mouse) < 0.01) {
		gl_FragColor = live;
	} else {
		float sum = 0.;
		sum += texture2D(backbuffer, position + pixel * vec2(-1.0, -1.0)).g;
		sum += texture2D(backbuffer, position + pixel * vec2(-1.0,  0.0)).g;
		sum += texture2D(backbuffer, position + pixel * vec2(-1.0,  1.0)).g;
		sum += texture2D(backbuffer, position + pixel * vec2( 1.0, -1.0)).g;
		sum += texture2D(backbuffer, position + pixel * vec2( 1.0,  0.0)).g;
		sum += texture2D(backbuffer, position + pixel * vec2( 1.0,  1.0)).g;
		sum += texture2D(backbuffer, position + pixel * vec2( 0.0, -1.0)).g;
		sum += texture2D(backbuffer, position + pixel * vec2( 0.0,  1.0)).g;
		float me = texture2D(backbuffer, position).g;

		if ((me == 1.0 && (sum == 2.0 || sum == 3.0)) || 
		    (me != 1.0 && sum == 3.0)) {
			gl_FragColor = live;
		} else {
			gl_FragColor = dead;
		}
	}
}
```

# 参考
- GLSL シェーダー - MDN, https://developer.mozilla.org/ja/docs/Games/Techniques/3D_on_the_web/GLSL_Shaders
- [連載]やってみれば超簡単！ WebGL と GLSL で始める、はじめてのシェーダコーディング - Qiita, https://qiita.com/doxas/items/b8221e92a2bfdc6fc211
- GLSL Sandbox, http://glslsandbox.com/
