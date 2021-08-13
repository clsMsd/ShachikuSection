# WebGL GPGPU

WebGLはGPUを使って画面に描画するグラフィックを計算して表示することができるが、グラフィックの計算以外にも汎用的な計算をすることができる。

> ![](https://mdn.mozillademos.org/files/13334/mdn-games-3d-rendering-pipeline.png)
> 
> レンダリングパイプライン, https://developer.mozilla.org/ja/docs/Games/Techniques/3D_on_the_web/Basic_theory#rendering_pipeline

## Texture を使った方法

WebGLで画像を描画するためにはTextureが使われる。
通常、画像データを２次元の配列とみなして１ピクセルごとに色の情報`vec4(r, g, b, a)`がTextureに格納される。
Textureはシェーダに入力されて、シェーダが各ピクセルの情報を読みながら加工したりして描画される。

しかし、１ピクセルごとに格納されるデータは単なる数値であり、色以外に任意の４次元ベクトルの値を格納することができる。
そして、そのTextureをシェーダ側で加工することで汎用的な計算をすることができる。

例えば、あるデータ列を受け取ってすべての要素を２倍にするシェーダは以下のように書ける。
`srcTex`からデータを受け取り`outColor`に計算結果を出力している。

Fragment Shader :
```glsl
#version 300 es
precision highp float;

uniform sampler2D srcTex;

out vec4 outColor;

void main(void){
    ivec2 texelCoord = ivec2(gl_FragCoord.xy);
    vec4 value = texelFetch(srcTex, texelCoord, 0);
    outColor = value * 2.0;
}
```

シェーダへのデータの受け渡しと、計算結果の読み込みはJS側で行う。
1) 入力データ`[1, 2, 3, 4, 5, 6]`を 3x2 のTextureとして作成しシェーダへ渡している。
1) `drawArrays`を呼び出すとシェーダを使って描画の計算が実行される。
今回の場合はTextureの各ピクセルのデータを2倍にして`[2, 4, 6, 8, 10, 12]`を出力する。
1) 計算結果は`readPixels`で読み出す。

```js
const srcWidth = 3;
const srcHeight = 2;
const dstWidth = 3;
const dstHeight = 2;

// Texture の作成
const tex = gl.createTexture();
gl.bindTexture(gl.TEXTURE_2D, tex);
gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
gl.texImage2D(
  gl.TEXTURE_2D,
  0,
  gl.R8,
  srcWidth,
  srcHeight,
  0,
  gl.RED,
  gl.UNSIGNED_BYTE,
  new Uint8Array([1, 2, 3, 4, 5, 6]) // 入力データ
);
gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);

gl.uniform1i(gl.getUniformLocation(shaderProgram, "srcTex"), 0);

// 計算の実行
gl.drawArrays(gl.TRIANGLES, 0, plane_pos.length);

// 計算結果の読み出し
const results = new Uint8Array(dstWidth * dstHeight * 4);
gl.readPixels(0, 0, dstWidth, dstHeight, gl.RGBA, gl.UNSIGNED_BYTE, results);

for (let i = 0; i < dstWidth * dstHeight; ++i) {
  console.log(results[i * 4]);
}
```

実行結果 :
```
2
4
6
8
10
12
```

## Transform Feedback を使った方法

```glsl
#version 300 es

in float a;
in float b;

out float sum;
out float diff;
out float prod;

void main(void){
  sum = a + b;
  diff = a - b;
  prod = a * b;
}
```

```glsl
#version 300 es

precision highp float;

void main(void){
}
```

# 参考

- https://webgl2fundamentals.org/webgl/lessons/webgl-gpgpu.html
